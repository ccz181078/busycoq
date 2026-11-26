(* 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- does not halt from the blank tape.

   Main configurations hold two binary counters around the head, low digit next to the head ([tok], [X], [AC]):
     left digits T(d) = 1 digit cell and four 0 cells, right digits (x 1), then one 1 and blanks.
   One tick adds 1 to the left counter and 2 to the right one ([tick]; [mix_tick] across a defect), and [skip_plain], [skip_mix] take any number of ticks that
   overflows neither counter at once. An overflow writes defects into the left digits ([U], [D3]),
   and the machine then rebounds.

   All of this is summarised by F states [F0] and [F1] (with [FC]): the left side blank or one token, the right digits
   0^a 1 H (1 0^(a-1) 1 H with the token), H of width h, G the complement of H in h digits. The lemmas of Map and the wrappers after it give the next
   F state from (e, a, h, G) as an exact formula, with subtractions of y = 2^A(m) (2^(m+2) - 3) and of
   y2 = 2^A'(r) (2 z + 1), z = y + 2^(r+1) - 1, where A(m) = floor((5m+1)/2) and A'(r) = floor((5r+2)/2).

   The steps need that a second subtraction leaves neither 0 nor a power of 2 ([good_tailL] takes this as a hypothesis).
   The invariant [Inv] gives this without knowing G digit by digit: a >= 26, the top bits of G, bounds on the
   trailing zeros r of G, and one condition [DCond]: if the first subtraction D is not negative, then D holds a run of
   ones [p, q) with 5 (q - p) >= 2 p + 25 ([LR]). A negative D carries no condition.

   Why it closes:
   - [close_O], [close_E] (in [close_TS] the new D is always negative): a new D that is not negative forces G to be long, and then ones of the new G
     lie on a zero interval of the number subtracted, so the new D has such a run again.
   - [two_cells], [N2_run]: such a run covers two zero cells of the next number subtracted, so the second subtraction
     leaves neither 0 nor a power of 2 ([two_zero]).
   - [short_B], [short_C]: when D is negative and G is short, the digits at the second level have a known shape
     (a top run, then at least a zeros, then little), and popcount with size arithmetic ([core_even], [core_odd],
     [block], [sizes_even]) excludes the same two results.

   [inv_step] is the closure: every state with [Inv] goes to a later F state with [Inv]. The start: [start0] runs
   2742 plain steps to F0 11 12 458, [s1], [s2], [s3] take one explicit stage to the F state with a = 131, h = 61,
   and [inv0] checks [Inv] there. The file has no skip inside the VM; [vm_compute] is only used on small numbers. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat NArith String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Module TM1.

Local Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition sb (b : bool) : Sym := if b then S1 else S0.

(* Right digits (x 1), low digit next to the head, then one 1 and blanks. *)
Fixpoint X (xs : list bool) : side :=
  match xs with
  | [] => S1 >> const S0
  | b :: r => sb b >> S1 >> X r
  end.

(* Left digits, low digit next to the head: T(1) = 1 0000, T(0) = 0 0000, read away from the head 0000 b. *)
Definition tok (b : bool) (L : side) : side := S0 >> S0 >> S0 >> S0 >> sb b >> L.

Fixpoint TL (ds : list bool) (L : side) : side :=
  match ds with
  | [] => L
  | d :: r => tok d (TL r L)
  end.

Fixpoint inc (xs : list bool) : option (list bool) :=
  match xs with
  | [] => None
  | false :: r => Some (true :: r)
  | true :: r =>
    match inc r with
    | Some r' => Some (false :: r')
    | None => None
    end
  end.

Fixpoint ones (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S n' => S1 >> ones n' r
  end.

Fixpoint zeros (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S n' => S0 >> zeros n' r
  end.

Lemma ones_shift : forall n r, ones n (S1 >> r) = S1 >> ones n r.
Proof. induction n as [|n IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma zeros_shift : forall n r, zeros n (S0 >> r) = S0 >> zeros n r.
Proof. induction n as [|n IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma ones_add : forall a b r, ones a (ones b r) = ones (a + b) r.
Proof. induction a as [|a IH]; intros b r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma zeros_add : forall a b r, zeros a (zeros b r) = zeros (a + b) r.
Proof. induction a as [|a IH]; intros b r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma B_clear : forall n P r, P {{B}}> ones n r -->* zeros n P {{B}}> r.
Proof.
  induction n as [|n IH]; intros P r.
  - finish.
  - simpl. step. follow IH. rewrite <- zeros_shift. simpl. finish.
Qed.

Lemma C_pass : forall n P r, P {{C}}> ones n r -->* ones n P {{C}}> r.
Proof.
  induction n as [|n IH]; intros P r.
  - finish.
  - simpl. step. follow IH. rewrite <- ones_shift. simpl. finish.
Qed.

(* A carry through the right digits: the token left of the digits becomes 0 1. *)
Lemma carry : forall xs ys, inc xs = Some ys ->
  forall P, S1 >> S1 >> P {{C}}> X xs -->+ P <{{A}} S0 >> S1 >> X ys.
Proof.
  induction xs as [|b r IH]; intros ys H P; [discriminate|].
  destruct b; simpl in H.
  - destruct (inc r) as [r'|] eqn:E; [|discriminate].
    injection H as <-. simpl X.
    eapply evstep_progress_trans.
    + do 2 step. finish.
    + eapply progress_trans; [apply (IH r' eq_refl (S1 >> S1 >> P))|].
      eapply progress_intro; [prove_step|].
      do 1 step. finish.
  - injection H as <-. simpl X. cbn [sb].
    eapply progress_intro; [prove_step|].
    do 2 step. finish.
Qed.

(* The E sweep through the left digits, and the clearing to the right. *)
Lemma E_T1 : forall T r, tok true T <{{E}} r -->+ T <{{E}} ones 5 r.
Proof.
  intros T r. unfold tok. cbn [sb].
  eapply progress_intro; [prove_step|].
  do 4 step. finish.
Qed.

Lemma E_T0 : forall T r, tok false T <{{E}} r -->+ (S1 >> T) {{B}}> ones 4 r.
Proof.
  intros T r. unfold tok. cbn [sb].
  eapply progress_intro; [prove_step|].
  do 4 step. finish.
Qed.

Lemma sweepD : forall ds ds', inc ds = Some ds' ->
  forall L k R, TL ds L <{{E}} ones k (S0 >> R) -->+ zeros k (TL ds' L) {{B}}> S0 >> R.
Proof.
  induction ds as [|b r IH]; intros ds' H L k R; [discriminate|].
  destruct b; simpl in H.
  - destruct (inc r) as [r'|] eqn:E; [|discriminate].
    injection H as <-. simpl TL.
    eapply progress_trans; [apply E_T1|].
    rewrite ones_add.
    eapply progress_evstep_trans; [apply IH; reflexivity|].
    replace (5 + k) with (k + 5) by lia. rewrite <- zeros_add. simpl. unfold tok. simpl. finish.
  - injection H as <-. simpl TL.
    eapply progress_evstep_trans; [apply E_T0|].
    rewrite ones_add.
    eapply evstep_trans; [apply B_clear|].
    replace (4 + k) with (k + 4) by lia. rewrite <- zeros_add. simpl. unfold tok. simpl. finish.
Qed.

(* Anchor: head A on the cell left of 0 1 digits. *)
Definition anchor (ds xs : list bool) (L : side) : Q * tape :=
  S0 >> TL ds L <{{A}} S0 >> S1 >> X xs.

Lemma phase1 : forall xs x1, inc xs = Some x1 ->
  forall L, S0 >> L <{{A}} S0 >> S1 >> X xs -->+ L <{{E}} S1 >> S0 >> S1 >> X x1.
Proof.
  intros xs x1 H L.
  eapply evstep_progress_trans.
  - do 3 step. finish.
  - eapply progress_trans; [apply (carry _ _ H (S1 >> L))|].
    eapply progress_intro; [prove_step|]. finish.
Qed.

Lemma phase2 : forall xs x1, inc xs = Some x1 ->
  forall P, P {{B}}> S0 >> S1 >> X xs -->+ P <{{A}} S0 >> S1 >> X x1.
Proof.
  intros xs x1 H P.
  eapply evstep_progress_trans.
  - do 2 step. finish.
  - apply (carry _ _ H P).
Qed.

(* THE TICK LAW: left counter + 1, right counter + 2, for all digits and any tape left of the counter. *)
Theorem tick : forall ds ds' xs x1 x2 L,
  inc ds = Some ds' -> inc xs = Some x1 -> inc x1 = Some x2 ->
  anchor ds xs L -->+ anchor ds' x2 L.
Proof.
  intros ds ds' xs x1 x2 L Hd H1 H2. unfold anchor.
  eapply progress_trans; [apply (phase1 _ _ H1)|].
  eapply progress_trans; [apply (sweepD _ _ Hd L 1 (S1 >> X x1))|].
  simpl zeros. apply phase2. exact H2.
Qed.

Module Part_Tape.

Local Open Scope nat_scope.

Definition oL (n : nat) : list bool := repeat true n.
Definition zL (n : nat) : list bool := repeat false n.
Definition B0 : side := const S0.
Definition U (R : side) : side := S0 >> S0 >> S0 >> S1 >> R.
Definition D3 (R : side) : side := S0 >> S0 >> S1 >> R.
Definition AC (L : side) (xs : list bool) : Q * tape := S0 >> L <{{A}} S0 >> S1 >> X xs.
Definition EC (L : side) (xs : list bool) : Q * tape := L <{{E}} S1 >> S0 >> S1 >> X xs.
Definition BC (P : side) (xs : list bool) : Q * tape := P {{B}}> S0 >> S1 >> X xs.

Fixpoint pr (k : nat) (r : side) : side :=
  match k with O => r | S k' => S0 >> S1 >> pr k' r end.
Fixpoint alt (k : nat) (r : side) : side :=
  match k with O => r | S k' => S1 >> S0 >> alt k' r end.

Lemma X_zL : forall k xs, X (zL k ++ xs) = pr k (X xs).
Proof. induction k as [|k IH]; intros xs; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma alt_shift : forall p a b r, alt p (a >> b >> r) = alt p (a >> b >> r).
Proof. reflexivity. Qed.

Lemma alt_S0 : forall p r, alt p (S1 >> S0 >> r) = S1 >> S0 >> alt p r.
Proof. induction p as [|p IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma alt_S1 : forall p r, alt p (S1 >> r) = S1 >> pr p r.
Proof. induction p as [|p IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma tok_false : forall R, tok false R = zeros 5 R.
Proof. reflexivity. Qed.

Lemma tok_true : forall R, tok true R = zeros 4 (S1 >> R).
Proof. reflexivity. Qed.

Lemma U_zeros : forall R, U R = zeros 3 (S1 >> R).
Proof. reflexivity. Qed.

Lemma D3_zeros : forall R, D3 R = zeros 2 (S1 >> R).
Proof. reflexivity. Qed.

Lemma TL_zL : forall n R, TL (zL n) R = zeros (5 * n) R.
Proof.
  induction n as [|n IH]; intros R; [reflexivity|].
  replace (5 * S n) with (5 + 5 * n) by lia. rewrite <- zeros_add.
  simpl TL. rewrite IH. reflexivity.
Qed.

Lemma zeros_B0 : forall n, zeros n B0 = B0.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite IH. unfold B0. rewrite <- const_unfold. reflexivity.
Qed.

Lemma TL_zL_B0 : forall n, TL (zL n) B0 = B0.
Proof. intros n. rewrite TL_zL. apply zeros_B0. Qed.

Lemma TL_app : forall a b R, TL (a ++ b) R = TL a (TL b R).
Proof. induction a as [|d a IH]; intros b R; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

(* Sweeps to the left *)
Lemma E_T1s : forall m Q r, TL (oL m) Q <{{E}} r -->* Q <{{E}} ones (5 * m) r.
Proof.
  induction m as [|m IH]; intros Q r.
  - finish.
  - simpl TL.
    eapply evstep_trans; [apply progress_evstep; apply E_T1|].
    eapply evstep_trans; [apply IH|].
    rewrite ones_add. replace (5 * m + 5) with (5 * S m) by lia. finish.
Qed.

Lemma U_pass : forall R r, U R <{{E}} r -->+ R <{{E}} ones 4 r.
Proof.
  intros R r. unfold U.
  eapply progress_intro; [prove_step|].
  do 3 step. finish.
Qed.

Lemma E_stop : forall Q k R, zeros 5 Q <{{E}} ones k (S0 >> R) -->+ zeros (4 + k) (S1 >> Q) {{B}}> S0 >> R.
Proof.
  intros Q k R.
  eapply progress_evstep_trans; [apply (E_T0 Q)|].
  rewrite ones_add.
  apply B_clear.
Qed.

(* Right overflows *)
Lemma ovf_C : forall W P, S1 >> S1 >> P {{C}}> X (oL W) -->+ P <{{E}} S1 >> S0 >> S1 >> X (zL W).
Proof.
  induction W as [|W IH]; intros P.
  - simpl.
    eapply progress_intro; [prove_step|].
    do 4 step. finish.
  - simpl.
    eapply evstep_progress_trans.
    + do 2 step. finish.
    + eapply progress_trans; [apply (IH (S1 >> S1 >> P))|].
      eapply progress_intro; [prove_step|].
      do 1 step. finish.
Qed.

Lemma ovf1 : forall W L, AC (S0 >> L) (oL W) -->+ EC L (true :: zL W).
Proof.
  intros W L. unfold AC, EC.
  eapply evstep_progress_trans.
  - do 3 step. finish.
  - eapply progress_trans; [apply (ovf_C W (S1 >> S0 >> L))|].
    eapply progress_intro; [prove_step|].
    do 7 step. finish.
Qed.

Lemma ovf2 : forall W P, BC P (oL W) -->+ EC P (zL W).
Proof.
  intros W P. unfold BC, EC.
  eapply evstep_progress_trans.
  - do 2 step. finish.
  - apply ovf_C.
Qed.

(* One E sweep *)
Lemma E_step : forall ds ds' L x, inc ds = Some ds' -> EC (TL ds L) x -->+ BC (S0 >> TL ds' L) x.
Proof.
  intros ds ds' L x H. unfold EC, BC.
  apply (sweepD _ _ H L 1 (S1 >> X x)).
Qed.

Lemma E5 : forall Q x, EC (zeros 5 Q) x -->+ BC (S0 >> tok true Q) x.
Proof.
  intros Q x. unfold EC, BC.
  apply (E_stop Q 1 (S1 >> X x)).
Qed.

Lemma ones_tail : forall n R, ones n (S1 >> R) = ones (n + 1) R.
Proof. intros n R. rewrite <- ones_add. reflexivity. Qed.

Lemma E_cross : forall m i Q x,
  EC (TL (oL m) (U (TL (oL i) (zeros 5 Q)))) x -->+ BC (S0 >> TL (zL (m + i + 1)) (U Q)) x.
Proof.
  intros m i Q x. unfold EC, BC.
  eapply evstep_progress_trans; [apply E_T1s|].
  eapply progress_trans; [apply U_pass|].
  eapply evstep_progress_trans; [apply E_T1s|].
  rewrite !ones_add, ones_tail.
  eapply progress_evstep_trans; [apply E_stop|].
  rewrite TL_zL, U_zeros, zeros_add.
  match goal with |- zeros ?n _ {{B}}> _ -->* _ => replace n with (S (5 * (m + i + 1) + 3)) by lia end.
  finish.
Qed.

Lemma E_absorb : forall m i x,
  EC (TL (oL m) (U (TL (oL i) (U B0)))) x -->+ BC (S0 >> TL (zL (m + i + 2)) (D3 B0)) x.
Proof.
  intros m i x. unfold EC, BC.
  eapply evstep_progress_trans; [apply E_T1s|].
  eapply progress_trans; [apply U_pass|].
  eapply evstep_progress_trans; [apply E_T1s|].
  eapply progress_trans; [apply U_pass|].
  rewrite !ones_add, ones_tail.
  rewrite <- (zeros_B0 5) at 1.
  eapply progress_evstep_trans; [apply E_stop|].
  rewrite TL_zL, D3_zeros, zeros_add.
  match goal with |- zeros ?n _ {{B}}> _ -->* _ => replace n with (S (5 * (m + i + 2) + 2)) by lia end.
  finish.
Qed.

(* Ticks across a defect *)
Lemma tick_cross : forall m i R xs x1 x2,
  inc xs = Some x1 -> inc x1 = Some x2 ->
  AC (TL (oL m) (U (TL (oL i) (tok false R)))) xs -->+ AC (TL (zL (m + i + 1)) (U R)) x2.
Proof.
  intros m i R xs x1 x2 H1 H2.
  eapply progress_trans; [apply (phase1 _ _ H1)|].
  eapply progress_trans; [apply (E_cross m i R x1)|].
  apply phase2. exact H2.
Qed.

Lemma tick_absorb : forall m i xs x1 x2,
  inc xs = Some x1 -> inc x1 = Some x2 ->
  AC (TL (oL m) (U (TL (oL i) (U B0)))) xs -->+ AC (TL (zL (m + i + 2)) (D3 B0)) x2.
Proof.
  intros m i xs x1 x2 H1 H2.
  eapply progress_trans; [apply (phase1 _ _ H1)|].
  eapply progress_trans; [apply (E_absorb m i x1)|].
  apply phase2. exact H2.
Qed.

Lemma tick_plain : forall ds ds' R xs x1 x2,
  inc ds = Some ds' -> inc xs = Some x1 -> inc x1 = Some x2 ->
  AC (TL ds R) xs -->+ AC (TL ds' R) x2.
Proof.
  intros ds ds' R xs x1 x2 Hd H1 H2.
  apply (tick ds ds' xs x1 x2 R Hd H1 H2).
Qed.

(* Rebounds *)
Lemma turn : forall P x,
  S1 >> S1 >> P {{C}}> S0 >> S1 >> X x -->+ S1 >> P <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros P x.
  eapply progress_intro; [prove_step|].
  do 1 step. finish.
Qed.

Lemma reb0a : forall k N r,
  S1 >> S0 >> N <{{E}} ones k r -->* S1 >> S1 >> N {{C}}> ones k r.
Proof. intros k N r. do 3 step. finish. Qed.

Lemma reb0 : forall k N x,
  S1 >> S0 >> N <{{E}} ones k (S0 >> S1 >> X x) -->+ ones (k + 1) N <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros k N x.
  eapply evstep_progress_trans.
  - eapply evstep_trans; [apply reb0a|]. apply C_pass.
  - rewrite !ones_shift.
    eapply progress_evstep_trans; [apply turn|].
    replace (ones (k + 1) N) with (S1 >> ones k N).
    + finish.
    + rewrite <- ones_add. simpl. rewrite <- ones_shift. reflexivity.
Qed.

Lemma reb2a : forall k Ln r,
  D3 Ln <{{E}} ones k r -->* S1 >> Ln {{C}}> ones (S (S k)) r.
Proof. intros k Ln r. unfold D3. do 3 step. finish. Qed.

Lemma reb2 : forall k Ln x,
  D3 Ln <{{E}} ones k (S0 >> S1 >> X x) -->+ ones (k + 2) Ln <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros k Ln x.
  eapply evstep_progress_trans.
  - eapply evstep_trans; [apply reb2a|]. apply C_pass.
  - rewrite ones_shift. simpl ones.
    eapply progress_evstep_trans; [apply turn|].
    replace (ones (k + 2) Ln) with (S1 >> ones (S k) Ln).
    + finish.
    + replace (k + 2) with (S (S k)) by lia. reflexivity.
Qed.

Lemma E_ones_even : forall p P r, ones (2 * p) P <{{E}} r -->* P <{{E}} alt p r.
Proof.
  induction p as [|p IH]; intros P r.
  - finish.
  - replace (2 * S p) with (S (S (2 * p))) by lia. simpl ones.
    do 2 step.
    eapply evstep_trans; [apply IH|].
    rewrite alt_S0. finish.
Qed.

Lemma E_ones_odd : forall p P r, ones (2 * p + 1) P <{{E}} r -->+ P <{{A}} S0 >> alt p r.
Proof.
  intros p P r.
  rewrite <- ones_add. simpl (ones 1 P).
  eapply evstep_progress_trans; [apply E_ones_even|].
  eapply progress_intro; [prove_step|]. finish.
Qed.

Lemma after_even : forall p P x,
  ones (2 * S p) P <{{E}} S1 >> S1 >> S1 >> X x -->* EC P (zL p ++ true :: x).
Proof.
  intros p P x. unfold EC.
  eapply evstep_trans; [apply E_ones_even|].
  rewrite alt_S1. simpl (pr _ _).
  replace (S1 >> S1 >> X x) with (X (true :: x)) by reflexivity.
  rewrite <- X_zL. finish.
Qed.

Lemma after_odd : forall p L x,
  ones (2 * p + 1) (S0 >> L) <{{E}} S1 >> S1 >> S1 >> X x -->+ AC L (zL p ++ true :: x).
Proof.
  intros p L x. unfold AC.
  eapply progress_evstep_trans; [apply E_ones_odd|].
  rewrite alt_S1.
  replace (S1 >> S1 >> X x) with (X (true :: x)) by reflexivity.
  rewrite <- X_zL. finish.
Qed.

(* R0: rebound at a 1 right after the low digits; R2: at a defect D3 *)
Lemma R0 : forall m N x,
  EC (TL (oL m) (S1 >> S0 >> N)) x -->+ ones (5 * m + 2) N <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros m N x. unfold EC.
  eapply evstep_progress_trans; [apply E_T1s|].
  rewrite ones_tail.
  eapply progress_evstep_trans; [apply reb0|].
  replace (5 * m + 1 + 1) with (5 * m + 2) by lia. finish.
Qed.

Lemma R2 : forall r Ln x,
  EC (TL (oL r) (D3 Ln)) x -->+ ones (5 * r + 3) Ln <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros r Ln x. unfold EC.
  eapply evstep_progress_trans; [apply E_T1s|].
  rewrite ones_tail.
  eapply progress_evstep_trans; [apply reb2|].
  replace (5 * r + 1 + 2) with (5 * r + 3) by lia. finish.
Qed.

Lemma R2U : forall m i Ln x,
  EC (TL (oL m) (U (TL (oL i) (D3 Ln)))) x -->+ ones (5 * (m + i + 1) + 2) Ln <{{E}} S1 >> S1 >> S1 >> X x.
Proof.
  intros m i Ln x. unfold EC.
  eapply evstep_progress_trans; [apply E_T1s|].
  eapply progress_trans; [apply U_pass|].
  eapply evstep_progress_trans; [apply E_T1s|].
  rewrite !ones_add, ones_tail.
  eapply progress_evstep_trans; [apply reb2|].
  match goal with |- ones ?n _ <{{E}} _ -->* _ => replace n with (5 * (m + i + 1) + 2) by lia end.
  finish.
Qed.

End Part_Tape.
Import Part_Tape.

Module Part_Num.

Definition pw (n : nat) : N := (2 ^ N.of_nat n)%N.

Lemma pw_0 : pw 0 = 1%N.
Proof. reflexivity. Qed.

Lemma pw_S : forall n, pw (S n) = (2 * pw n)%N.
Proof.
  intros n. unfold pw. rewrite Nat2N.inj_succ, N.pow_succ_r'. reflexivity.
Qed.

Lemma pw_add : forall a b, pw (a + b) = (pw a * pw b)%N.
Proof.
  intros a b. unfold pw. rewrite Nat2N.inj_add, N.pow_add_r. reflexivity.
Qed.

Lemma pw_pos : forall n, (1 <= pw n)%N.
Proof.
  intros n. unfold pw. apply N.lt_pred_le. simpl.
  apply N.neq_0_lt_0. apply N.pow_nonzero. lia.
Qed.

Lemma pw_le : forall a b, (a <= b)%nat -> (pw a <= pw b)%N.
Proof.
  intros a b H. replace b with (a + (b - a))%nat by lia. rewrite pw_add.
  pose proof (pw_pos (b - a)). pose proof (pw_pos a). nia.
Qed.

Lemma pw_lt : forall a b, (a < b)%nat -> (2 * pw a <= pw b)%N.
Proof.
  intros a b H. rewrite <- pw_S. apply pw_le. lia.
Qed.

Fixpoint bin (n : nat) (v : N) : list bool :=
  match n with
  | O => []
  | S n' => N.odd v :: bin n' (N.div2 v)
  end.

Lemma bin_even : forall n w, bin (S n) (2 * w)%N = false :: bin n w.
Proof. intros n w. destruct w; reflexivity. Qed.

Lemma bin_odd : forall n w, bin (S n) (2 * w + 1)%N = true :: bin n w.
Proof. intros n w. destruct w; reflexivity. Qed.

Lemma N_parity : forall v : N, (exists w, v = 2 * w)%N \/ (exists w, v = 2 * w + 1)%N.
Proof.
  intros v. destruct (N.even v) eqn:E.
  - left. apply N.even_spec in E. destruct E as [w Hw]. exists w. exact Hw.
  - right. assert (N.odd v = true) by (rewrite <- N.negb_even, E; reflexivity).
    apply N.odd_spec in H. destruct H as [w Hw]. exists w. exact Hw.
Qed.

Lemma bin_length : forall n v, length (bin n v) = n.
Proof. induction n as [|n IH]; intros v; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma bin_zero : forall n, bin n 0%N = zL n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma bin_ones : forall n, bin n (pw n - 1)%N = oL n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (pw (S n) - 1)%N with (2 * (pw n - 1) + 1)%N.
  - rewrite bin_odd, IH. reflexivity.
  - rewrite pw_S. pose proof (pw_pos n). lia.
Qed.

Lemma bin_app : forall n t u m, (t < pw n)%N ->
  bin (n + m) (t + pw n * u)%N = bin n t ++ bin m u.
Proof.
  induction n as [|n IH]; intros t u m H.
  - rewrite pw_0 in *. assert (t = 0%N) by lia. subst. replace (0 + 1 * u)%N with u by lia. reflexivity.
  - rewrite pw_S in *. destruct (N_parity t) as [[w Hw]|[w Hw]]; subst t.
    + replace (2 * w + 2 * pw n * u)%N with (2 * (w + pw n * u))%N by lia.
      simpl (S n + m)%nat. rewrite bin_even, bin_even. simpl. rewrite IH by lia. reflexivity.
    + replace (2 * w + 1 + 2 * pw n * u)%N with (2 * (w + pw n * u) + 1)%N by lia.
      simpl (S n + m)%nat. rewrite bin_odd, bin_odd. simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma bin_split : forall t c C, bin (t + S c) (pw t * (2 * C + 1))%N = zL t ++ true :: bin c C.
Proof.
  intros t c C.
  replace (pw t * (2 * C + 1))%N with (0 + pw t * (2 * C + 1))%N by lia.
  rewrite bin_app by (pose proof (pw_pos t); lia).
  rewrite bin_zero, bin_odd. reflexivity.
Qed.

Lemma bin_pow : forall u k, bin (u + S k) (pw u) = zL u ++ true :: zL k.
Proof.
  intros u k.
  replace (pw u) with (pw u * (2 * 0 + 1))%N by lia.
  rewrite bin_split, bin_zero. reflexivity.
Qed.

(* inc on lists *)
Lemma inc_bin : forall n v, (v + 1 < pw n)%N -> inc (bin n v) = Some (bin n (v + 1)).
Proof.
  induction n as [|n IH]; intros v H.
  - rewrite pw_0 in H. lia.
  - rewrite pw_S in H. destruct (N_parity v) as [[w Hw]|[w Hw]]; subst v.
    + rewrite bin_even, bin_odd. reflexivity.
    + rewrite bin_odd. replace (2 * w + 1 + 1)%N with (2 * (w + 1))%N by lia.
      rewrite bin_even. simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma inc_oL : forall n, inc (oL n) = None.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. unfold oL in IH. rewrite IH. reflexivity. Qed.

Lemma inc_none : forall xs, inc xs = None -> xs = oL (length xs).
Proof.
  induction xs as [|b r IH]; intros H; [reflexivity|].
  destruct b; simpl in H; [|discriminate].
  destruct (inc r) as [r'|] eqn:E; [discriminate|].
  specialize (IH eq_refl).
  change (true :: r = true :: oL (length r)). f_equal. exact IH.
Qed.

Lemma inc_form : forall xs ys, inc xs = Some ys ->
  exists i rest, xs = oL i ++ false :: rest /\ ys = zL i ++ true :: rest.
Proof.
  induction xs as [|b r IH]; intros ys H; [discriminate|].
  destruct b; simpl in H.
  - destruct (inc r) as [r'|] eqn:E; [|discriminate].
    injection H as <-. destruct (IH _ eq_refl) as [i [rest [H1 H2]]].
    exists (S i), rest. subst. split; reflexivity.
  - injection H as <-. exists 0%nat, r. split; reflexivity.
Qed.

Lemma inc_app : forall a a' b, inc a = Some a' -> inc (a ++ b) = Some (a' ++ b).
Proof.
  induction a as [|d a IH]; intros a' b H; [discriminate|].
  destruct d; simpl in *.
  - destruct (inc a) as [a2|] eqn:E; [|discriminate].
    injection H as <-. rewrite (IH a2 b eq_refl). reflexivity.
  - injection H as <-. reflexivity.
Qed.

Lemma inc_oL_app : forall m r, inc (oL m ++ r) =
  match inc r with Some r' => Some (zL m ++ r') | None => None end.
Proof.
  induction m as [|m IH]; intros r.
  - change (inc (oL 0 ++ r)) with (inc r). destruct (inc r); reflexivity.
  - change (inc (oL (S m) ++ r)) with
      (match inc (oL m ++ r) with Some r' => Some (false :: r') | None => None end).
    rewrite IH. destruct (inc r); reflexivity.
Qed.

Lemma zL_add : forall a b, zL (a + b) = zL a ++ zL b.
Proof. intros a b. apply repeat_app. Qed.

Lemma oL_true_form : forall a b n, a ++ true :: b = oL n -> a = oL (length a) /\ b = oL (length b).
Proof.
  induction a as [|d a IH]; intros b n H.
  - simpl in H. destruct n; [discriminate|]. injection H as H.
    split; [reflexivity|]. rewrite H. unfold oL. rewrite repeat_length. reflexivity.
  - destruct n; [discriminate|]. injection H as H1 H2. subst d.
    destruct (IH _ _ H2) as [H3 H4]. split; [|exact H4].
    change (true :: a = true :: oL (length a)). f_equal. exact H3.
Qed.

Lemma zL_true_form : forall u a b k, a ++ true :: b = zL u ++ true :: zL k -> a = zL u /\ b = zL k.
Proof.
  induction u as [|u IH]; intros a b k H.
  - destruct a as [|d a]; simpl in H.
    + injection H as H. split; [reflexivity|exact H].
    + injection H as H1 H2. subst d.
      assert (In true (zL k)) as Hin.
      { rewrite <- H2. apply in_or_app. right. left. reflexivity. }
      apply repeat_spec in Hin. discriminate.
  - destruct a as [|d a]; simpl in H.
    + discriminate.
    + injection H as H1 H2. subst d. destruct (IH _ _ _ H2) as [H3 H4]. subst. split; reflexivity.
Qed.

Lemma TL_bin_pad : forall n k v, (v < pw n)%N -> TL (bin (n + k) v) B0 = TL (bin n v) B0.
Proof.
  intros n k v H.
  replace v with (v + pw n * 0)%N at 1 by lia.
  rewrite bin_app by exact H. rewrite TL_app, bin_zero, TL_zL_B0. reflexivity.
Qed.

(* Skips *)
Lemma skip_plain : forall K m W v x R, (v + K < pw m)%N -> (x + 2 * K < pw W)%N ->
  AC (TL (bin m v) R) (bin W x) -->* AC (TL (bin m (v + K)) R) (bin W (x + 2 * K)).
Proof.
  induction K as [|K IH] using N.peano_ind; intros m W v x R H1 H2.
  - rewrite N.add_0_r. replace (x + 2 * 0)%N with x by lia. finish.
  - rewrite N.add_succ_r in *.
    replace (x + 2 * N.succ K)%N with ((x + 2) + 2 * K)%N in * by lia.
    eapply evstep_trans.
    + apply progress_evstep. apply (tick_plain (bin m v) (bin m (v + 1)) R (bin W x) (bin W (x + 1)) (bin W (x + 1 + 1))).
      * apply inc_bin. lia.
      * apply inc_bin. lia.
      * apply inc_bin. lia.
    + replace (x + 1 + 1)%N with (x + 2)%N by lia.
      replace (N.succ (v + K))%N with (v + 1 + K)%N by lia.
      apply IH; lia.
Qed.

(* The mixed counter: a defect U sits on a digit 1 of the value. *)
Definition MXC (T : side) (low hi : list bool) (W : nat) (x : N) : Q * tape :=
  AC (TL low (U (TL hi T))) (bin W x).

Lemma mix_tick : forall L V W x T low hi, low ++ true :: hi = bin L V ->
  (V + 1 < pw L)%N -> (x + 2 < pw W)%N ->
  exists low' hi', low' ++ true :: hi' = bin L (V + 1) /\
    MXC T low hi W x -->+ MXC T low' hi' W (x + 2).
Proof.
  intros L V W x T low hi Hb H1 H2. unfold MXC.
  assert (inc (bin L V) = Some (bin L (V + 1))) as HI by (apply inc_bin; exact H1).
  rewrite <- Hb in HI.
  assert (inc (bin W x) = Some (bin W (x + 1))) as Hx1 by (apply inc_bin; lia).
  assert (inc (bin W (x + 1)) = Some (bin W (x + 2))) as Hx2.
  { replace (x + 2)%N with (x + 1 + 1)%N by lia. apply inc_bin. lia. }
  destruct (inc low) as [low'|] eqn:El.
  - exists low', hi. rewrite (inc_app _ _ _ El) in HI. injection HI as HI.
    split; [exact HI|].
    apply tick_plain with (bin W (x + 1)); assumption.
  - apply inc_none in El. rewrite El in HI.
    rewrite inc_oL_app in HI. simpl in HI.
    destruct (inc hi) as [h'|] eqn:Eh; [|discriminate].
    injection HI as HI.
    destruct (inc_form _ _ Eh) as [i [rest [E1 E2]]]. subst hi h'.
    exists (zL (length low + i + 1)), rest. split.
    + rewrite <- HI. replace (length low + i + 1)%nat with (length low + S i)%nat by lia.
      rewrite zL_add, <- app_assoc. reflexivity.
    + rewrite El at 1. rewrite TL_app. simpl TL.
      apply tick_cross with (bin W (x + 1)); assumption.
Qed.

Lemma skip_mix : forall K L V W x T low hi, low ++ true :: hi = bin L V ->
  (V + K < pw L)%N -> (x + 2 * K < pw W)%N ->
  exists low' hi', low' ++ true :: hi' = bin L (V + K) /\
    MXC T low hi W x -->* MXC T low' hi' W (x + 2 * K).
Proof.
  induction K as [|K IH] using N.peano_ind; intros L V W x T low hi Hb H1 H2.
  - exists low, hi. rewrite N.add_0_r. split; [exact Hb|].
    replace (x + 2 * 0)%N with x by lia. finish.
  - rewrite N.add_succ_r in H1.
    replace (x + 2 * N.succ K)%N with ((x + 2) + 2 * K)%N in * by lia.
    destruct (mix_tick L V W x T low hi Hb) as [l1 [h1 [E1 S1']]]; [lia|lia|].
    destruct (IH L (V + 1)%N W (x + 2)%N T l1 h1 E1) as [l2 [h2 [E2 S2']]]; [lia|lia|].
    exists l2, h2. split.
    + rewrite E2. f_equal. lia.
    + eapply evstep_trans; [apply progress_evstep; exact S1'|exact S2'].
Qed.

(* Reaching an exact power of 2 on a blank tape puts the defect at the top. *)
Lemma mix_to_pow : forall K u k W x low hi, low ++ true :: hi = bin (u + S k) (pw u - K)%N ->
  (K <= pw u - 1)%N -> (x + 2 * K < pw W)%N ->
  MXC B0 low hi W x -->* AC (TL (zL u) (U B0)) (bin W (x + 2 * K)).
Proof.
  intros K u k W x low hi Hb H1 H2.
  destruct (skip_mix K (u + S k)%nat (pw u - K)%N W x B0 low hi Hb) as [l2 [h2 [E2 S2']]].
  - replace (pw u - K + K)%N with (pw u) by lia.
    rewrite pw_add, pw_S. pose proof (pw_pos u). pose proof (pw_pos k). nia.
  - exact H2.
  - replace (pw u - K + K)%N with (pw u) in E2 by lia.
    rewrite bin_pow in E2. destruct (zL_true_form _ _ _ _ E2) as [E3 E4]. subst l2 h2.
    unfold MXC in S2'. rewrite TL_zL_B0 in S2'. exact S2'.
Qed.

(* Reaching all ones under a defect *)
Lemma mix_to_ones : forall K L W x T low hi, low ++ true :: hi = bin L (pw L - 1 - K)%N ->
  (K <= pw L - 1)%N -> (x + 2 * K < pw W)%N ->
  exists m i, (m + S i = L)%nat /\
    MXC T low hi W x -->* AC (TL (oL m) (U (TL (oL i) T))) (bin W (x + 2 * K)).
Proof.
  intros K L W x T low hi Hb H1 H2.
  destruct (skip_mix K L (pw L - 1 - K)%N W x T low hi Hb) as [l2 [h2 [E2 S2']]].
  - pose proof (pw_pos L). lia.
  - exact H2.
  - replace (pw L - 1 - K + K)%N with (pw L - 1)%N in E2 by lia.
    rewrite bin_ones in E2.
    destruct (oL_true_form _ _ _ E2) as [E3 E4].
    exists (length l2), (length h2). split.
    + assert (length (l2 ++ true :: h2) = L).
      { rewrite E2. unfold oL. apply repeat_length. }
      rewrite app_length in H. simpl in H. lia.
    + rewrite <- E3, <- E4. exact S2'.
Qed.

End Part_Num.
Import Part_Num.

Module Part_Stage.

Local Open Scope N_scope.

Definition Afun (m : nat) : nat := ((5 * m + 1) / 2)%nat.
Definition Apr (r : nat) : nat := ((5 * r + 2) / 2)%nat.

Lemma Afun_even : forall k, Afun (2 * k) = (5 * k)%nat.
Proof. intros k. unfold Afun. symmetry; apply Nat.div_unique with 1%nat; lia. Qed.
Lemma Afun_odd : forall k, Afun (2 * k + 1) = (5 * k + 3)%nat.
Proof. intros k. unfold Afun. symmetry; apply Nat.div_unique with 0%nat; lia. Qed.
Lemma Apr_even : forall k, Apr (2 * k) = (5 * k + 1)%nat.
Proof. intros k. unfold Apr. symmetry; apply Nat.div_unique with 0%nat; lia. Qed.
Lemma Apr_odd : forall k, Apr (2 * k + 1) = (5 * k + 3)%nat.
Proof. intros k. unfold Apr. symmetry; apply Nat.div_unique with 1%nat; lia. Qed.

Definition x1v (t : nat) : N := pw (S (S t)) - 2.
Definition yv (t : nat) : N := pw (Afun (S t)) * (2 * x1v t + 1).
Definition zv (t r : nat) : N := yv t + 2 * pw r - 1.
Definition y2v (t r : nat) : N := pw (Apr r) * (2 * zv t r + 1).

Definition D1 (m : nat) (Cs : side) (W : nat) : Q * tape := AC (TL (bin m 1) (S1 >> Cs)) (bin W 1).

Lemma pw_ge2 : forall t, 2 <= pw (S t).
Proof. intros t. rewrite pw_S. pose proof (pw_pos t). lia. Qed.

Lemma d1_skip : forall t Cs W, (S (S t) <= W)%nat ->
  D1 (S t) Cs W -->+ EC (TL (oL (S t)) (S1 >> Cs)) (bin W (x1v t)).
Proof.
  intros t Cs W H. unfold D1, x1v.
  pose proof (pw_ge2 t) as H2.
  pose proof (pw_le _ _ H) as H3. rewrite (pw_S (S t)) in H3.
  rewrite (pw_S (S t)).
  eapply evstep_progress_trans.
  - apply (skip_plain (pw (S t) - 2) (S t) W 1 1 (S1 >> Cs)); lia.
  - replace (1 + (pw (S t) - 2)) with (pw (S t) - 1) by lia.
    rewrite bin_ones.
    apply phase1. replace (2 * pw (S t) - 2) with (1 + 2 * (pw (S t) - 2) + 1) by lia.
    apply inc_bin. lia.
Qed.

Lemma stage_even : forall t k N W, S t = (2 * k)%nat -> (S (S t) <= W)%nat ->
  D1 (S t) (S0 >> N) W -->+ EC N (bin (Afun (S t) + S W) (yv t)).
Proof.
  intros t k N W Hk HW.
  eapply progress_trans; [apply d1_skip; exact HW|].
  eapply progress_evstep_trans; [apply R0|].
  rewrite Hk.
  replace (5 * (2 * k) + 2)%nat with (2 * S (5 * k))%nat by lia.
  eapply evstep_trans; [apply after_even|].
  unfold yv. rewrite Hk, Afun_even. rewrite bin_split. finish.
Qed.

Lemma stage_odd : forall t k L W, S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  D1 (S t) (S0 >> S0 >> L) W -->+ AC L (bin (Afun (S t) + S W) (yv t)).
Proof.
  intros t k L W Hk HW.
  eapply progress_trans; [apply d1_skip; exact HW|].
  eapply progress_trans; [apply R0|].
  rewrite Hk.
  replace (5 * (2 * k + 1) + 2)%nat with (2 * (5 * k + 3) + 1)%nat by lia.
  unfold yv. rewrite Hk, Afun_odd. rewrite bin_split.
  apply after_odd.
Qed.

(* digits with their first set bit *)
Lemma Cs_form : forall r c1 C1 T,
  TL (bin (r + S c1) (pw r * (2 * C1 + 1))) T = zeros (5 * r + 4) (S1 >> TL (bin c1 C1) T).
Proof.
  intros r c1 C1 T. rewrite bin_split, TL_app. simpl TL. rewrite TL_zL, tok_true, zeros_add. reflexivity.
Qed.

Lemma tokS_form : forall r c1 C1 T,
  TL (bin (r + S c1) (pw r * (2 * C1 + 1))) T = S0 >> TL (zL r) (U (TL (bin c1 C1) T)).
Proof.
  intros r c1 C1 T. rewrite Cs_form, TL_zL, U_zeros, zeros_add.
  replace (5 * r + 4)%nat with (S (5 * r + 3)) by lia. reflexivity.
Qed.

Lemma tokD3_form : forall r c1 C1 T,
  TL (bin (r + S c1) (pw r * (2 * C1 + 1))) T = S0 >> S0 >> TL (zL r) (D3 (TL (bin c1 C1) T)).
Proof.
  intros r c1 C1 T. rewrite Cs_form, TL_zL, D3_zeros, zeros_add.
  replace (5 * r + 4)%nat with (S (S (5 * r + 2))) by lia. reflexivity.
Qed.

Lemma N_tz : forall D, D <> 0 -> exists t C, D = pw t * (2 * C + 1).
Proof.
  intros D. induction D as [p IH] using (well_founded_ind N.lt_wf_0).
  intros H. destruct (N_parity p) as [[w Hw]|[w Hw]].
  - subst p. assert (w <> 0) as Hw0 by lia. destruct (IH w) as [t [C HC]]; [lia|exact Hw0|].
    exists (S t), C. rewrite pw_S, HC. lia.
  - exists 0%nat, w. rewrite pw_0. lia.
Qed.

Lemma tz_bound : forall u t C, pw t * (2 * C + 1) < pw u ->
  exists c, u = (t + S c)%nat /\ C < pw c.
Proof.
  intros u t C H.
  assert (t < u)%nat as Ht.
  { destruct (Nat.lt_ge_cases t u) as [H1|H1]; [exact H1|].
    pose proof (pw_le _ _ H1). pose proof (pw_pos t). nia. }
  exists (u - S t)%nat. split; [lia|].
  replace u with (t + S (u - S t))%nat in H by lia.
  rewrite pw_add, pw_S in H. pose proof (pw_pos t) as H1.
  assert (2 * C + 1 < 2 * pw (u - S t)) as H2.
  { apply N.mul_lt_mono_pos_l with (pw t); lia. }
  lia.
Qed.

(* E on the digits cut by one cell: value + 1, with a defect U *)
Lemma cut_sweep : forall r c1 C1 T x x2, inc x = Some x2 ->
  pw r * (2 * C1 + 1) + 1 < pw (r + S c1) ->
  exists low hi, low ++ true :: hi = bin (r + S c1) (pw r * (2 * C1 + 1) + 1) /\
    EC (TL (zL r) (U (TL (bin c1 C1) T))) x -->+ AC (TL low (U (TL hi T))) x2.
Proof.
  intros r c1 C1 T x x2 Hx HC.
  destruct r as [|r'].
  - rewrite pw_0, N.mul_1_l in *. simpl (0 + S c1)%nat in *.
    rewrite pw_S in HC.
    assert (HC1 : C1 + 1 < pw c1) by lia.
    assert (Hi : inc (bin c1 C1) = Some (bin c1 (C1 + 1))) by (apply inc_bin; exact HC1).
    destruct (inc_form _ _ Hi) as [i [rest [E1 E2]]].
    exists (zL (S i)), rest. split.
    + replace (2 * C1 + 1 + 1) with (2 * (C1 + 1)) by lia. rewrite bin_even, E2. reflexivity.
    + rewrite E1, TL_app. simpl TL.
      eapply progress_trans.
      * apply (E_cross 0 i (TL rest T)).
      * replace (0 + i + 1)%nat with (S i) by lia. apply phase2. exact Hx.
  - exists (true :: zL r'), (bin c1 C1). split.
    + replace (pw (S r') * (2 * C1 + 1) + 1) with (2 * (pw r' * (2 * C1 + 1)) + 1)
        by (rewrite pw_S; lia).
      simpl (S r' + S c1)%nat. rewrite bin_odd, bin_split. reflexivity.
    + replace (TL (zL (S r')) (U (TL (bin c1 C1) T))) with (zeros 5 (TL (zL r') (U (TL (bin c1 C1) T))))
        by (simpl TL; reflexivity).
      eapply progress_trans; [apply E5|].
      apply phase2. exact Hx.
Qed.

(* m even: the value + 1 under a defect U *)
Lemma stage_E : forall t k r c1 C1 T W,
  S t = (2 * k)%nat -> (S (S t) <= W)%nat ->
  yv t + 1 < pw (Afun (S t) + S W) -> pw r * (2 * C1 + 1) + 1 < pw (r + S c1) ->
  exists low hi, low ++ true :: hi = bin (r + S c1) (pw r * (2 * C1 + 1) + 1) /\
    D1 (S t) (TL (bin (r + S c1) (pw r * (2 * C1 + 1))) T) W -->+
      MXC T low hi (Afun (S t) + S W) (yv t + 1).
Proof.
  intros t k r c1 C1 T W Hk HW Hy HC.
  assert (HI2 : inc (bin (Afun (S t) + S W) (yv t)) = Some (bin (Afun (S t) + S W) (yv t + 1)))
    by (apply inc_bin; exact Hy).
  destruct (cut_sweep r c1 C1 T _ _ HI2 HC) as [low [hi [E1 E2]]].
  exists low, hi. split; [exact E1|].
  rewrite tokS_form.
  eapply progress_trans; [apply (stage_even t k _ W Hk HW)|].
  exact E2.
Qed.

(* m even, all digits ones, a defect U above: both defects merge *)
Lemma stage_Vover : forall t k c1 W,
  S t = (2 * k)%nat -> (S (S t) <= W)%nat ->
  yv t + 1 < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin (S c1) (pw (S c1) - 1)) (U B0)) W -->+
    AC (TL (zL (c1 + 2)) (D3 B0)) (bin (Afun (S t) + S W) (yv t + 1)).
Proof.
  intros t k c1 W Hk HW Hy.
  assert (HI2 : inc (bin (Afun (S t) + S W) (yv t)) = Some (bin (Afun (S t) + S W) (yv t + 1)))
    by (apply inc_bin; exact Hy).
  rewrite bin_ones.
  replace (TL (oL (S c1)) (U B0)) with (S0 >> U (TL (oL c1) (U B0))) by reflexivity.
  eapply progress_trans; [apply (stage_even t k _ W Hk HW)|].
  eapply progress_trans; [apply (E_absorb 0 c1)|].
  replace (0 + c1 + 2)%nat with (c1 + 2)%nat by lia.
  apply phase2. exact HI2.
Qed.

Lemma stage_Oc : forall t k r c1 C1 T W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t r < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin (r + S c1) (pw r * (2 * C1 + 1))) T) W -->+
    EC (TL (oL r) (D3 (TL (bin c1 C1) T))) (bin (Afun (S t) + S W) (zv t r)).
Proof.
  intros t k r c1 C1 T W Hk HW Hz.
  rewrite tokD3_form.
  eapply progress_trans; [apply (stage_odd t k _ W Hk HW)|].
  rewrite <- (bin_zero r).
  pose proof (pw_pos r) as Hr.
  unfold zv in *.
  eapply evstep_progress_trans.
  - apply (skip_plain (pw r - 1) r (Afun (S t) + S W) 0 (yv t)); lia.
  - replace (0 + (pw r - 1)) with (pw r - 1) by lia. rewrite bin_ones.
    replace (yv t + 2 * pw r - 1) with (yv t + 2 * (pw r - 1) + 1) by lia.
    apply phase1. apply inc_bin. lia.
Qed.

Lemma stage_O0 : forall t k j r2 c2 C2 T W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j) < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) T) W -->+
    MXC T (zL r2) (bin c2 C2) (Apr (2 * j) + S (Afun (S t) + S W)) (y2v t (2 * j)).
Proof.
  intros t k j r2 c2 C2 T W Hk HW Hz.
  eapply progress_trans; [apply (stage_Oc t k); assumption|].
  rewrite tokS_form.
  eapply progress_trans; [apply R2|].
  replace (5 * (2 * j) + 3)%nat with (2 * (5 * j + 1) + 1)%nat by lia.
  unfold MXC, y2v. rewrite Apr_even, bin_split.
  apply after_odd.
Qed.

Lemma stage_O1 : forall t k j c1 C1 T W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j + 1) < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) T) W -->+
    EC (TL (bin c1 C1) T) (bin (Apr (2 * j + 1) + S (Afun (S t) + S W)) (y2v t (2 * j + 1))).
Proof.
  intros t k j c1 C1 T W Hk HW Hz.
  eapply progress_trans; [apply (stage_Oc t k); assumption|].
  eapply progress_evstep_trans; [apply R2|].
  replace (5 * (2 * j + 1) + 3)%nat with (2 * S (5 * j + 3))%nat by lia.
  eapply evstep_trans; [apply after_even|].
  unfold y2v. rewrite Apr_odd, bin_split. finish.
Qed.

(* Overflows of the right counter *)
Lemma ovf1_cut : forall u D T W, D <> 0 -> D + 1 < pw u ->
  exists low hi, low ++ true :: hi = bin u (D + 1) /\
    AC (TL (bin u D) T) (oL (S W)) -->+ MXC T low hi (S (S W)) 2.
Proof.
  intros u D T W H0 H1.
  destruct (N_tz D H0) as [t [C HD]]. subst D.
  destruct (tz_bound u t C) as [c [Hu HC]]; [lia|]. subst u.
  assert (Hx : inc (true :: zL (S W)) = Some (bin (S (S W)) 2)).
  { change (true :: zL (S W)) with (true :: zL (S W)).
    rewrite <- bin_zero.
    change (true :: bin (S W) 0) with (bin (S (S W)) (2 * 0 + 1)).
    apply inc_bin. rewrite !pw_S. pose proof (pw_pos W). lia. }
  destruct (cut_sweep t c C T _ _ Hx H1) as [low [hi [E1 E2]]].
  exists low, hi. split; [exact E1|].
  rewrite tokS_form.
  eapply progress_trans; [apply ovf1|].
  exact E2.
Qed.

Lemma of2 : forall t c C R W',
  pw t * (2 * C + 1) < pw (t + S c) ->
  EC (TL (bin (t + S c) (pw t * (2 * C + 1) - 1)) R) (oL (S W')) -->+
    D1 (S t) (TL (bin c C) R) (S W').
Proof.
  intros t c C R W' H.
  assert (Hp : 1 <= pw t * (2 * C + 1)).
  { pose proof (pw_pos t). nia. }
  eapply progress_trans.
  - apply E_step. apply inc_bin. lia.
  - replace (pw t * (2 * C + 1) - 1 + 1) with (pw t * (2 * C + 1)) by lia.
    eapply progress_trans; [apply ovf2|].
    rewrite Cs_form.
    replace (S0 >> zeros (5 * t + 4) (S1 >> TL (bin c C) R))
      with (zeros 5 (zeros (5 * t) (S1 >> TL (bin c C) R))).
    + eapply progress_trans; [apply E5|].
      unfold D1. change (bin (S t) 1) with (true :: bin t 0). rewrite bin_zero. simpl TL. rewrite TL_zL.
      change (bin (S W') 1) with (true :: bin W' 0). rewrite bin_zero.
      apply phase2. reflexivity.
    + rewrite zeros_add. replace (5 + 5 * t)%nat with (S (5 * t + 4)) by lia. reflexivity.
Qed.

Lemma mx_pad : forall low hi c d V W x, low ++ true :: hi = bin c V -> V < pw c ->
  low ++ true :: (hi ++ zL d) = bin (c + d) V /\ MXC B0 low (hi ++ zL d) W x = MXC B0 low hi W x.
Proof.
  intros low hi c d V W x H1 H2. split.
  - replace (bin (c + d) V) with (bin (c + d) (V + pw c * 0)) by (f_equal; lia).
    rewrite bin_app by exact H2. rewrite <- H1, bin_zero. rewrite <- app_assoc. reflexivity.
  - unfold MXC. rewrite TL_app, TL_zL_B0. reflexivity.
Qed.

Lemma mx_to_tail : forall low hi c u V K Vl W x,
  low ++ true :: hi = bin c V -> V < pw c -> (c <= S u)%nat -> V <= pw u -> 1 <= V ->
  V + K = pw u + Vl -> Vl < pw u -> x + 2 * K < pw W ->
  MXC B0 low hi W x -->* AC (TL (bin u Vl) (U B0)) (bin W (x + 2 * K)).
Proof.
  intros low hi c u V K Vl W x H1 H2 H3 H4 H4b H5 H6 H7.
  destruct (mx_pad low hi c (S u - c) V W x H1 H2) as [E1 E2].
  rewrite <- E2.
  replace (c + (S u - c))%nat with (u + S 0)%nat in E1 by lia.
  pose proof (pw_pos u) as Hu.
  eapply evstep_trans.
  - apply (mix_to_pow (pw u - V) u 0 W x low (hi ++ zL (S u - c))); [|lia|lia].
    replace (pw u - (pw u - V)) with V by lia. exact E1.
  - rewrite <- (bin_zero u).
    replace (x + 2 * K) with (x + 2 * (pw u - V) + 2 * Vl) by lia.
    replace (bin u Vl) with (bin u (0 + Vl)) by (f_equal; lia).
    apply skip_plain; lia.
Qed.

Lemma dbl_blank : forall t c C,
  pw t * (2 * C + 1) + 1 < pw (t + S c) ->
  AC (TL (bin (t + S c) (pw t * (2 * C + 1))) B0) (oL (t + S c)) -->+
    D1 (S t) (TL (bin c C) (U B0)) (S (t + S c)).
Proof.
  intros t c C H1.
  set (c0 := pw t * (2 * C + 1)) in *.
  assert (Hp : 1 <= c0) by (unfold c0; pose proof (pw_pos t); nia).
  assert (c0 <> 0) as H0 by lia.
  set (w := (t + S c)%nat) in *.
  assert (exists W', w = S W') as [W' HW] by (exists (t + c)%nat; unfold w; lia).
  rewrite HW in H1 |- *.
  destruct (ovf1_cut (S W') c0 B0 W' H0 H1) as [low [hi [E1 E2]]].
  eapply progress_trans; [exact E2|].
  pose proof (pw_S (S W')) as Hs.
  apply evstep_progress_trans with
    (c' := AC (TL (bin (S W') (c0 - 1)) (U B0)) (bin (S (S W')) (pw (S (S W')) - 2))).
  - replace (bin (S (S W')) (pw (S (S W')) - 2)) with
      (bin (S (S W')) (2 + 2 * (pw (S W') - (c0 + 1) + (c0 - 1)))).
    + eapply mx_to_tail with (c := S W') (V := c0 + 1) (u := S W').
      * exact E1.
      * exact H1.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
    + f_equal. lia.
  - pose proof (pw_pos (S W')) as Hp2.
    eapply progress_trans.
    + apply phase1. apply inc_bin. lia.
    + replace (pw (S (S W')) - 2 + 1) with (pw (S (S W')) - 1) by lia.
      rewrite bin_ones. rewrite <- HW. unfold w, c0 in *. apply of2.
      rewrite HW in *. lia.
Qed.

Lemma tailL : forall u D t c3 C3,
  D <> 0 -> D + 1 < pw u -> pw u + D = pw t * (2 * C3 + 1) -> (S u = t + S c3)%nat ->
  AC (TL (bin u D) (U B0)) (oL (S u)) -->+ D1 (S t) (TL (bin c3 C3) (D3 B0)) (S (S u)).
Proof.
  intros u D t c3 C3 H0 H1 HZ Hu.
  destruct (ovf1_cut u D (U B0) u H0 H1) as [low [hi [E1 E2]]].
  eapply progress_trans; [exact E2|].
  pose proof (pw_pos u) as Hp.
  pose proof (pw_S u) as Hs. pose proof (pw_S (S u)) as Hs2.
  destruct (mix_to_ones (pw u - 1 - (D + 1)) u (S (S u)) 2 (U B0) low hi) as [m [i [Hm Sm]]].
  - replace (pw u - 1 - (pw u - 1 - (D + 1))) with (D + 1) by lia. exact E1.
  - lia.
  - lia.
  - eapply evstep_progress_trans; [exact Sm|].
    set (x0 := 2 + 2 * (pw u - 1 - (D + 1))) in *.
    eapply progress_trans.
    + apply (tick_absorb m i (bin (S (S u)) x0) (bin (S (S u)) (x0 + 1)) (bin (S (S u)) (x0 + 1 + 1)));
        apply inc_bin; unfold x0; lia.
    + replace (m + i + 2)%nat with (S u) by lia. rewrite <- (bin_zero (S u)).
      eapply evstep_progress_trans.
      * apply (skip_plain (pw u - 1 + D) (S u) (S (S u)) 0 (x0 + 1 + 1) (D3 B0)); unfold x0; lia.
      * eapply progress_trans.
        { apply phase1. apply inc_bin. unfold x0. lia. }
        replace (x0 + 1 + 1 + 2 * (pw u - 1 + D) + 1) with (pw (S (S u)) - 1) by (unfold x0; lia).
        rewrite bin_ones.
        replace (0 + (pw u - 1 + D)) with (pw t * (2 * C3 + 1) - 1) by lia.
        rewrite Hu. apply of2. rewrite <- Hu. lia.
Qed.

Lemma tailS : forall u Vl, Vl <> 0 -> Vl + 1 < pw u ->
  AC (TL (bin u Vl) (U B0)) (oL (S (S u))) -->+
    EC (TL (oL (S u)) (D3 B0)) (bin (S (S (S u))) (2 * pw u - 2 * Vl + 2 * pw (S u) - 1)).
Proof.
  intros u Vl H0 H1.
  destruct (ovf1_cut u Vl (U B0) (S u) H0 H1) as [low [hi [E1 E2]]].
  eapply progress_trans; [exact E2|].
  pose proof (pw_pos u) as Hp.
  pose proof (pw_S u) as Hs. pose proof (pw_S (S u)) as Hs2. pose proof (pw_S (S (S u))) as Hs3.
  destruct (mix_to_ones (pw u - 1 - (Vl + 1)) u (S (S (S u))) 2 (U B0) low hi) as [m [i [Hm Sm]]].
  - replace (pw u - 1 - (pw u - 1 - (Vl + 1))) with (Vl + 1) by lia. exact E1.
  - lia.
  - lia.
  - eapply evstep_progress_trans; [exact Sm|].
    set (x0 := 2 + 2 * (pw u - 1 - (Vl + 1))) in *.
    eapply progress_trans.
    + apply (tick_absorb m i (bin (S (S (S u))) x0) (bin (S (S (S u))) (x0 + 1)) (bin (S (S (S u))) (x0 + 1 + 1)));
        apply inc_bin; unfold x0; lia.
    + replace (m + i + 2)%nat with (S u) by lia. rewrite <- (bin_zero (S u)).
      eapply evstep_progress_trans.
      * apply (skip_plain (pw (S u) - 1) (S u) (S (S (S u))) 0 (x0 + 1 + 1) (D3 B0)); unfold x0; lia.
      * replace (0 + (pw (S u) - 1)) with (pw (S u) - 1) by lia. rewrite bin_ones.
        replace (2 * pw u - 2 * Vl + 2 * pw (S u) - 1) with (x0 + 1 + 1 + 2 * (pw (S u) - 1) + 1) by (unfold x0; lia).
        apply phase1. apply inc_bin. unfold x0. lia.
Qed.

(* The defect levels *)
Lemma b_level : forall low hi L V Wf x,
  low ++ true :: hi = bin L V -> V < pw L -> x + 2 * (pw L - V) < pw Wf ->
  MXC (U B0) low hi Wf x -->+ AC (TL (zL (S L)) (D3 B0)) (bin Wf (x + 2 * (pw L - V))).
Proof.
  intros low hi L V Wf x H1 H2 H3.
  destruct (mix_to_ones (pw L - 1 - V) L Wf x (U B0) low hi) as [m [i [Hm Sm]]].
  - replace (pw L - 1 - (pw L - 1 - V)) with V by lia. exact H1.
  - lia.
  - lia.
  - eapply evstep_progress_trans; [exact Sm|].
    replace (x + 2 * (pw L - V)) with (x + 2 * (pw L - 1 - V) + 1 + 1) by lia.
    replace (S L) with (m + i + 2)%nat by lia.
    apply (tick_absorb m i (bin Wf (x + 2 * (pw L - 1 - V))) (bin Wf (x + 2 * (pw L - 1 - V) + 1)));
      apply inc_bin; lia.
Qed.

Lemma d3_plain : forall N Wf x, x + 2 * pw N - 1 < pw Wf ->
  AC (TL (zL N) (D3 B0)) (bin Wf x) -->+ EC (TL (oL N) (D3 B0)) (bin Wf (x + 2 * pw N - 1)).
Proof.
  intros N Wf x H.
  pose proof (pw_pos N) as Hp.
  rewrite <- (bin_zero N).
  eapply evstep_progress_trans.
  - apply (skip_plain (pw N - 1) N Wf 0 x (D3 B0)); lia.
  - replace (0 + (pw N - 1)) with (pw N - 1) by lia. rewrite bin_ones.
    replace (x + 2 * pw N - 1) with (x + 2 * (pw N - 1) + 1) by lia.
    apply phase1. apply inc_bin. lia.
Qed.

Lemma d3_level : forall low hi L V Wf x,
  low ++ true :: hi = bin L V -> V < pw L -> x + 2 * (pw L - 1 - V) + 1 < pw Wf ->
  exists m i, (m + S i = L)%nat /\
    MXC (D3 B0) low hi Wf x -->+
      EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin Wf (x + 2 * (pw L - 1 - V) + 1)).
Proof.
  intros low hi L V Wf x H1 H2 H3.
  destruct (mix_to_ones (pw L - 1 - V) L Wf x (D3 B0) low hi) as [m [i [Hm Sm]]].
  - replace (pw L - 1 - (pw L - 1 - V)) with V by lia. exact H1.
  - lia.
  - lia.
  - exists m, i. split; [exact Hm|].
    eapply evstep_progress_trans; [exact Sm|].
    apply phase1. apply inc_bin. lia.
Qed.

(* Full wipes *)
Definition F0 (a h : nat) (H : N) : Q * tape := AC B0 (zL a ++ true :: bin h H).
Definition F1 (a h : nat) (H : N) : Q * tape := AC (tok true B0) (true :: zL (a - 1) ++ true :: bin h H).

Lemma B0_S0 : B0 = S0 >> B0.
Proof. unfold B0. apply const_unfold. Qed.

Lemma after_odd_B0 : forall p x,
  ones (2 * p + 1) B0 <{{E}} S1 >> S1 >> S1 >> X x -->+ AC B0 (zL p ++ true :: x).
Proof.
  intros p x. pose proof (after_odd p B0 x) as H. rewrite <- B0_S0 in H. exact H.
Qed.

Lemma after_even_B0 : forall p x,
  ones (2 * S (S p)) B0 <{{E}} S1 >> S1 >> S1 >> X x -->+ AC (tok true B0) (true :: zL p ++ true :: x).
Proof.
  intros p x.
  eapply evstep_progress_trans; [apply after_even|].
  pose proof (E5 B0 (zL (S p) ++ true :: x)) as H. rewrite zeros_B0 in H.
  eapply progress_trans; [exact H|].
  apply phase2. reflexivity.
Qed.

Lemma fin_plain_even : forall j h H,
  EC (TL (oL (2 * j)) (D3 B0)) (bin h H) -->+ F0 (Apr (2 * j)) h H.
Proof.
  intros j h H. unfold F0. rewrite Apr_even.
  eapply progress_trans; [apply R2|].
  replace (5 * (2 * j) + 3)%nat with (2 * (5 * j + 1) + 1)%nat by lia.
  apply after_odd_B0.
Qed.

Lemma fin_plain_odd : forall j h H,
  EC (TL (oL (2 * j + 1)) (D3 B0)) (bin h H) -->+ F1 (Apr (2 * j + 1)) h H.
Proof.
  intros j h H. unfold F1. rewrite Apr_odd.
  eapply progress_trans; [apply R2|].
  replace (5 * (2 * j + 1) + 3)%nat with (2 * S (S (5 * j + 2)))%nat by lia.
  replace (5 * j + 3 - 1)%nat with (5 * j + 2)%nat by lia.
  apply after_even_B0.
Qed.

Lemma fin_U_odd : forall m i j h H, (m + i + 1 = 2 * j + 1)%nat ->
  EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H) -->+ F0 (Afun (2 * j + 1)) h H.
Proof.
  intros m i j h H Hj. unfold F0. rewrite Afun_odd.
  eapply progress_trans; [apply R2U|].
  rewrite Hj.
  replace (5 * (2 * j + 1) + 2)%nat with (2 * (5 * j + 3) + 1)%nat by lia.
  apply after_odd_B0.
Qed.

Lemma fin_U_even : forall m i j h H, (m + i + 1 = 2 * S j)%nat ->
  EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H) -->+ F1 (Afun (2 * S j)) h H.
Proof.
  intros m i j h H Hj. unfold F1. rewrite Afun_even.
  eapply progress_trans; [apply R2U|].
  rewrite Hj.
  replace (5 * (2 * S j) + 2)%nat with (2 * S (S (5 * j + 4)))%nat by lia.
  replace (5 * S j - 1)%nat with (5 * j + 4)%nat by lia.
  apply after_even_B0.
Qed.

End Part_Stage.
Import Part_Stage.

Module Part_Map.

Local Open Scope N_scope.

Definition FC (b : bool) (a h : nat) (H : N) : Q * tape := if b then F1 a h H else F0 a h H.

Lemma odd_2j : forall j, Nat.odd (2 * j) = false.
Proof. intros j. rewrite <- Nat.negb_even, Nat.even_mul. reflexivity. Qed.
Lemma odd_2j1 : forall j, Nat.odd (2 * j + 1) = true.
Proof. intros j. apply Nat.odd_spec. exists j. reflexivity. Qed.
Lemma even_2j : forall j, Nat.even (2 * j) = true.
Proof. intros j. rewrite Nat.even_mul. reflexivity. Qed.
Lemma even_2j1 : forall j, Nat.even (2 * j + 1) = false.
Proof. intros j. rewrite <- Nat.negb_odd, odd_2j1. reflexivity. Qed.

Lemma fin_plain : forall N h H,
  EC (TL (oL N) (D3 B0)) (bin h H) -->+ FC (Nat.odd N) (Apr N) h H.
Proof.
  intros N h H. destruct (Nat.Even_or_Odd N) as [[j Hj]|[j Hj]]; subst N.
  - rewrite odd_2j. apply fin_plain_even.
  - rewrite odd_2j1. apply fin_plain_odd.
Qed.

Lemma fin_U : forall m i L h H, (m + i + 1 = L)%nat ->
  EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H) -->+ FC (Nat.even L) (Afun L) h H.
Proof.
  intros m i L h H HL. destruct (Nat.Even_or_Odd L) as [[j Hj]|[j Hj]]; rewrite Hj in *.
  - rewrite even_2j. destruct j as [|j]; [lia|].
    apply fin_U_even. exact HL.
  - rewrite even_2j1. apply fin_U_odd. exact HL.
Qed.

Lemma d3_fin : forall N Wf x, x + 2 * pw N - 1 < pw Wf ->
  AC (TL (zL N) (D3 B0)) (bin Wf x) -->+ FC (Nat.odd N) (Apr N) Wf (x + 2 * pw N - 1).
Proof.
  intros N Wf x H.
  eapply progress_trans; [apply d3_plain; exact H|].
  apply fin_plain.
Qed.

Lemma phase1_full : forall W x L, x + 2 = pw W ->
  AC L (bin W x) -->+ EC L (oL W).
Proof.
  intros W x L H.
  assert (HI : inc (bin W x) = Some (oL W)).
  { rewrite <- bin_ones. replace (pw W - 1) with (x + 1) by lia. apply inc_bin. lia. }
  apply (phase1 _ _ HI).
Qed.

(* From a full wipe to the first D1 form *)
Lemma F0_D1 : forall a' h G H, G + H + 1 = pw h ->
  F0 (S a') h H -->+ D1 (S a') (TL (bin h G) B0) (S (a' + S h)).
Proof.
  intros a' h G H HG. unfold F0.
  replace (zL (S a') ++ true :: bin h H) with (bin (S (a' + S h)) (pw (S a') * (2 * H + 1)))
    by (change (S (a' + S h)) with (S a' + S h)%nat; apply bin_split).
  assert (pW : pw (S (a' + S h)) = 4 * (pw a' * pw h)).
  { rewrite pw_S, pw_add, pw_S. lia. }
  assert (hz : pw a' * G + pw a' * H + pw a' = pw a' * pw h).
  { rewrite <- HG. lia. }
  pose proof (pw_pos a') as Ha. pose proof (pw_pos h) as Hh.
  assert (Hb : G < pw h) by lia.
  assert (HT : TL (bin (S h) G) B0 = TL (bin h G) B0).
  { rewrite <- Nat.add_1_r. apply TL_bin_pad. exact Hb. }
  pose proof (of2 a' (S h) G B0 (a' + S h)) as Hof.
  replace (a' + S (S h))%nat with (S (a' + S h)) in Hof by lia.
  rewrite HT in Hof.
  rewrite pw_S.
  set (Z := pw a' * (2 * G + 1)) in *.
  assert (hZ : Z = 2 * (pw a' * G) + pw a') by (unfold Z; lia).
  replace B0 with (TL (bin (S (a' + S h)) 0) B0) at 1 by (rewrite bin_zero; apply TL_zL_B0).
  eapply evstep_progress_trans.
  - apply (skip_plain (Z - 1) (S (a' + S h)) (S (a' + S h)) 0 (2 * pw a' * (2 * H + 1)) B0); lia.
  - replace (0 + (Z - 1)) with (Z - 1) by lia.
    eapply progress_trans.
    + apply phase1_full. lia.
    + apply Hof. lia.
Qed.

Lemma F1_D1 : forall a' h G H, G + H + 1 = pw h ->
  F1 (S a') h H -->+ D1 (S a') (TL (bin (S h) G) (U B0)) (S (S (a' + S h))).
Proof.
  intros a' h G H HG. unfold F1.
  replace (S a' - 1)%nat with a' by lia.
  assert (Hdig : true :: zL a' ++ true :: bin h H = bin (S (a' + S h)) (2 * (pw a' * (2 * H + 1)) + 1)).
  { rewrite bin_odd, bin_split. reflexivity. }
  assert (Htok : tok true B0 = TL (bin (S (a' + S h)) 1) B0).
  { change (bin (S (a' + S h)) 1) with (true :: bin (a' + S h) 0).
    rewrite bin_zero. simpl TL. rewrite TL_zL_B0. reflexivity. }
  rewrite Hdig, Htok.
  assert (pW : pw (S (a' + S h)) = 4 * (pw a' * pw h)).
  { rewrite pw_S, pw_add, pw_S. lia. }
  assert (hz : pw a' * G + pw a' * H + pw a' = pw a' * pw h).
  { rewrite <- HG. lia. }
  pose proof (pw_pos a') as Ha. pose proof (pw_pos h) as Hh.
  pose proof (dbl_blank a' (S h) G) as Hd.
  replace (a' + S (S h))%nat with (S (a' + S h)) in Hd by lia.
  set (Z := pw a' * (2 * G + 1)) in *.
  assert (hZ : Z = 2 * (pw a' * G) + pw a') by (unfold Z; lia).
  eapply evstep_progress_trans.
  - apply (skip_plain (Z - 1) (S (a' + S h)) (S (a' + S h)) 1 (2 * (pw a' * (2 * H + 1)) + 1) B0); lia.
  - replace (1 + (Z - 1)) with Z by lia.
    replace (2 * (pw a' * (2 * H + 1)) + 1 + 2 * (Z - 1)) with (pw (S (a' + S h)) - 1) by lia.
    rewrite bin_ones.
    apply Hd. lia.
Qed.

(* Level a: the tape blank above the digits *)
Lemma a_E1_tail : forall t k r c1 C1 W K u Vl,
  S t = (2 * k)%nat -> (S (S t) <= W)%nat ->
  pw r * (2 * C1 + 1) < pw (r + S c1) ->
  yv t + 1 + 2 * K + 1 = pw (Afun (S t) + S W) ->
  (r + S c1 + 1 <= S u)%nat -> pw r * (2 * C1 + 1) + 1 <= pw u ->
  pw r * (2 * C1 + 1) + 1 + K = pw u + Vl -> Vl < pw u ->
  D1 (S t) (TL (bin (r + S c1) (pw r * (2 * C1 + 1))) B0) W -->+
    AC (TL (bin u Vl) (U B0)) (oL (Afun (S t) + S W)).
Proof.
  intros t k r c1 C1 W K u Vl Hk HW HC Hx Hc HV HK HVl.
  rewrite <- (TL_bin_pad (r + S c1) 1 _ HC).
  replace (r + S c1 + 1)%nat with (r + S (c1 + 1))%nat in * by lia.
  assert (HC2 : pw r * (2 * C1 + 1) + 1 < pw (r + S (c1 + 1))).
  { replace (r + S (c1 + 1))%nat with (S (r + S c1)) by lia. rewrite pw_S.
    pose proof (pw_pos (r + S c1)). lia. }
  destruct (stage_E t k r (c1 + 1) C1 B0 W Hk HW) as [low [hi [E1 E2]]]; [lia|exact HC2|].
  eapply progress_evstep_trans; [exact E2|].
  rewrite <- bin_ones.
  replace (pw (Afun (S t) + S W) - 1) with (yv t + 1 + 2 * K) by lia.
  eapply mx_to_tail with (c := (r + S (c1 + 1))%nat) (V := pw r * (2 * C1 + 1) + 1); try exact E1; lia.
Qed.

Lemma a_O0_next : forall t k j r2 c2 C2 W K u t' c' C' W2,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j) < pw (Afun (S t) + S W) ->
  (Apr (2 * j) + S (Afun (S t) + S W) = S W2)%nat ->
  y2v t (2 * j) + 2 * K + 2 = pw (S W2) ->
  pw r2 * (2 * C2 + 1) < pw (r2 + S c2) -> (r2 + S c2 <= S u)%nat ->
  1 <= pw r2 * (2 * C2 + 1) -> pw r2 * (2 * C2 + 1) <= pw u ->
  pw r2 * (2 * C2 + 1) + K + 1 = pw u + pw t' * (2 * C' + 1) -> (u = t' + S c')%nat ->
  pw t' * (2 * C' + 1) < pw u ->
  D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) B0) W -->+
    D1 (S t') (TL (bin c' C') (U B0)) (S W2).
Proof.
  intros t k j r2 c2 C2 W K u t' c' C' W2 Hk HW Hz HW2 Hx HC Hc HV1 HV HK Hu HZ.
  eapply progress_trans; [apply (stage_O0 t k j r2 c2 C2 B0 W); assumption|].
  rewrite HW2.
  assert (Hp : 1 <= pw t' * (2 * C' + 1)) by (pose proof (pw_pos t'); nia).
  assert (Hb : zL r2 ++ true :: bin c2 C2 = bin (r2 + S c2) (pw r2 * (2 * C2 + 1))) by (rewrite bin_split; reflexivity).
  eapply evstep_progress_trans.
  - apply (mx_to_tail (zL r2) (bin c2 C2) (r2 + S c2) u (pw r2 * (2 * C2 + 1)) K (pw t' * (2 * C' + 1) - 1) (S W2) (y2v t (2 * j))); try exact Hb; try lia.
  - eapply progress_trans.
    + apply phase1_full. lia.
    + subst u. apply of2. exact HZ.
Qed.

Lemma a_O1_next : forall t k j c1 C1 W K t' c' C',
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j + 1) < pw (Afun (S t) + S W) ->
  y2v t (2 * j + 1) + 1 + 2 * K + 1 = pw (t' + S c') ->
  (Apr (2 * j + 1) + S (Afun (S t) + S W) = t' + S c')%nat ->
  (c1 <= t' + S c')%nat -> C1 < pw c1 -> C1 + 1 < pw (t' + S c') ->
  C1 + 1 + K = pw t' * (2 * C' + 1) -> pw t' * (2 * C' + 1) + 1 < pw (t' + S c') ->
  D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) B0) W -->+
    D1 (S t') (TL (bin c' C') (U B0)) (S (t' + S c')).
Proof.
  intros t k j c1 C1 W K t' c' C' Hk HW Hz Hx HW2 Hc HC1 HC2 HK HZ.
  eapply progress_trans; [apply (stage_O1 t k j c1 C1 B0 W); assumption|].
  rewrite HW2.
  replace (TL (bin c1 C1) B0) with (TL (bin (t' + S c') C1) B0).
  2:{ replace (t' + S c')%nat with (c1 + (t' + S c' - c1))%nat by lia. apply TL_bin_pad. exact HC1. }
  eapply progress_trans.
  { apply E_step. apply inc_bin. exact HC2. }
  eapply progress_trans.
  { apply phase2. apply inc_bin. lia. }
  eapply evstep_progress_trans.
  { apply (skip_plain K (t' + S c') (t' + S c') (C1 + 1) (y2v t (2 * j + 1) + 1) B0); lia. }
  replace (C1 + 1 + K) with (pw t' * (2 * C' + 1)) by lia.
  replace (y2v t (2 * j + 1) + 1 + 2 * K) with (pw (t' + S c') - 1) by lia.
  rewrite bin_ones.
  apply dbl_blank. exact HZ.
Qed.

(* Level b: a defect U on top of the digits *)
Lemma b_E1 : forall t k c C W,
  S t = (2 * k)%nat -> (S (S t) <= W)%nat -> C <> 0 -> C < pw c ->
  yv t + 1 + 2 * (pw c - (C + 1)) < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin c C) (U B0)) W -->+
    AC (TL (zL (S c)) (D3 B0)) (bin (Afun (S t) + S W) (yv t + 1 + 2 * (pw c - (C + 1)))).
Proof.
  intros t k c C W Hk HW H0 HC Hx.
  destruct (N.eq_dec (C + 1) (pw c)) as [Eq|Ne].
  - destruct c as [|c1]; [rewrite pw_0 in HC; lia|].
    assert (HC' : C = pw (S c1) - 1) by lia. subst C.
    pose proof (pw_pos (S c1)) as Hp.
    replace (yv t + 1 + 2 * (pw (S c1) - (pw (S c1) - 1 + 1))) with (yv t + 1) in * by lia.
    replace (S (S c1)) with (c1 + 2)%nat by lia.
    apply (stage_Vover t k c1 W Hk HW Hx).
  - destruct (N_tz C H0) as [r [C1 HC1]]. subst C.
    destruct (tz_bound c r C1 HC) as [c1 [Hc Hb]]. subst c.
    destruct (stage_E t k r c1 C1 (U B0) W Hk HW) as [low [hi [E1 E2]]]; [lia|lia|].
    eapply progress_trans; [exact E2|].
    apply b_level with (L := (r + S c1)%nat) (V := pw r * (2 * C1 + 1) + 1).
    + exact E1.
    + lia.
    + lia.
Qed.

Lemma b_O0 : forall t k j r2 c2 C2 W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j) < pw (Afun (S t) + S W) ->
  pw r2 * (2 * C2 + 1) < pw (r2 + S c2) ->
  y2v t (2 * j) + 2 * (pw (r2 + S c2) - pw r2 * (2 * C2 + 1)) < pw (Apr (2 * j) + S (Afun (S t) + S W)) ->
  D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (U B0)) W -->+
    AC (TL (zL (S (r2 + S c2))) (D3 B0))
       (bin (Apr (2 * j) + S (Afun (S t) + S W)) (y2v t (2 * j) + 2 * (pw (r2 + S c2) - pw r2 * (2 * C2 + 1)))).
Proof.
  intros t k j r2 c2 C2 W Hk HW Hz HC Hx.
  eapply progress_trans; [apply (stage_O0 t k j r2 c2 C2 (U B0) W); assumption|].
  apply b_level with (L := (r2 + S c2)%nat) (V := pw r2 * (2 * C2 + 1)).
  - rewrite bin_split. reflexivity.
  - exact HC.
  - exact Hx.
Qed.

Lemma b_O1 : forall t k j c1 C1 W K u Vl,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j + 1) < pw (Afun (S t) + S W) -> C1 < pw c1 ->
  y2v t (2 * j + 1) + 1 + 2 * K + 1 = pw (Apr (2 * j + 1) + S (Afun (S t) + S W)) ->
  (c1 + 2 <= S u)%nat -> C1 + 1 + pw c1 <= pw u ->
  C1 + 1 + pw c1 + K = pw u + Vl -> Vl < pw u ->
  D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) (U B0)) W -->+
    AC (TL (bin u Vl) (U B0)) (oL (Apr (2 * j + 1) + S (Afun (S t) + S W))).
Proof.
  intros t k j c1 C1 W K u Vl Hk HW Hz HC Hx Hc HV HK HVl.
  eapply progress_trans; [apply (stage_O1 t k j c1 C1 (U B0) W); assumption|].
  set (W2 := (Apr (2 * j + 1) + S (Afun (S t) + S W))%nat) in *.
  set (y2 := y2v t (2 * j + 1)) in *.
  assert (HI : inc (bin W2 y2) = Some (bin W2 (y2 + 1))) by (apply inc_bin; lia).
  pose proof (pw_pos c1) as Hp1.
  rewrite <- bin_ones.
  replace (pw W2 - 1) with (y2 + 1 + 2 * K) by lia.
  destruct (N.eq_dec (C1 + 1) (pw c1)) as [Eq|Ne].
  - (* all ones: the carry moves the defect up *)
    replace C1 with (pw c1 - 1) by lia. rewrite bin_ones.
    eapply progress_evstep_trans.
    + eapply progress_trans.
      * pose proof (E_cross c1 0 B0 (bin W2 y2)) as H. rewrite zeros_B0 in H. exact H.
      * apply phase2. exact HI.
    + replace (c1 + 0 + 1)%nat with (S c1) by lia.
      apply (mx_to_tail (zL (S c1)) [] (S c1 + S 0) u (pw (S c1)) K Vl W2 (y2 + 1)).
      * rewrite bin_pow. reflexivity.
      * rewrite pw_add, pw_S, pw_S, pw_0. pose proof (pw_pos (S c1)). lia.
      * lia.
      * rewrite pw_S. lia.
      * rewrite pw_S. lia.
      * rewrite pw_S. lia.
      * exact HVl.
      * lia.
  - eapply progress_evstep_trans.
    + eapply progress_trans.
      * apply E_step. apply inc_bin. lia.
      * apply phase2. exact HI.
    + apply (mx_to_tail (bin c1 (C1 + 1)) [] (c1 + 1) u (C1 + 1 + pw c1) K Vl W2 (y2 + 1)).
      * replace (C1 + 1 + pw c1) with (C1 + 1 + pw c1 * 1) by lia.
        rewrite bin_app by lia. reflexivity.
      * rewrite pw_add. change (pw 1) with 2. lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact HVl.
      * lia.
Qed.

(* Level d3: a defect D3 on top of the digits *)
Lemma d3_E1 : forall t k r c1 C1 W,
  S t = (2 * k)%nat -> (S (S t) <= W)%nat ->
  pw r * (2 * C1 + 1) + 1 < pw (r + S c1) ->
  yv t + 1 + 2 * (pw (r + S c1) - 1 - (pw r * (2 * C1 + 1) + 1)) + 1 < pw (Afun (S t) + S W) ->
  D1 (S t) (TL (bin (r + S c1) (pw r * (2 * C1 + 1))) (D3 B0)) W -->+
    FC (Nat.even (r + S c1)) (Afun (r + S c1)) (Afun (S t) + S W)
       (yv t + 1 + 2 * (pw (r + S c1) - 1 - (pw r * (2 * C1 + 1) + 1)) + 1).
Proof.
  intros t k r c1 C1 W Hk HW HC Hx.
  destruct (stage_E t k r c1 C1 (D3 B0) W Hk HW) as [low [hi [E1 E2]]]; [lia|lia|].
  eapply progress_trans; [exact E2|].
  destruct (d3_level low hi (r + S c1) (pw r * (2 * C1 + 1) + 1) (Afun (S t) + S W) (yv t + 1) E1 HC Hx) as [m [i [Hm Sm]]].
  eapply progress_trans; [exact Sm|].
  apply fin_U. lia.
Qed.

Lemma d3_O0 : forall t k j r2 c2 C2 W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j) < pw (Afun (S t) + S W) ->
  pw r2 * (2 * C2 + 1) < pw (r2 + S c2) ->
  y2v t (2 * j) + 2 * (pw (r2 + S c2) - 1 - pw r2 * (2 * C2 + 1)) + 1 < pw (Apr (2 * j) + S (Afun (S t) + S W)) ->
  D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (D3 B0)) W -->+
    FC (Nat.even (r2 + S c2)) (Afun (r2 + S c2)) (Apr (2 * j) + S (Afun (S t) + S W))
       (y2v t (2 * j) + 2 * (pw (r2 + S c2) - 1 - pw r2 * (2 * C2 + 1)) + 1).
Proof.
  intros t k j r2 c2 C2 W Hk HW Hz HC Hx.
  eapply progress_trans; [apply (stage_O0 t k j r2 c2 C2 (D3 B0) W); assumption|].
  assert (Hb : zL r2 ++ true :: bin c2 C2 = bin (r2 + S c2) (pw r2 * (2 * C2 + 1))) by (rewrite bin_split; reflexivity).
  destruct (d3_level _ _ (r2 + S c2) (pw r2 * (2 * C2 + 1)) _ _ Hb HC Hx) as [m [i [Hm Sm]]].
  eapply progress_trans; [exact Sm|].
  apply fin_U. lia.
Qed.

Lemma d3_O1 : forall t k j c1 C1 W,
  S t = (2 * k + 1)%nat -> (S (S t) <= W)%nat ->
  zv t (2 * j + 1) < pw (Afun (S t) + S W) -> C1 + 1 < pw c1 ->
  y2v t (2 * j + 1) + 1 + 2 * (pw c1 - 1 - (C1 + 1)) + 1 < pw (Apr (2 * j + 1) + S (Afun (S t) + S W)) ->
  D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) (D3 B0)) W -->+
    FC (Nat.odd c1) (Apr c1) (Apr (2 * j + 1) + S (Afun (S t) + S W))
       (y2v t (2 * j + 1) + 1 + 2 * (pw c1 - 1 - (C1 + 1)) + 1).
Proof.
  intros t k j c1 C1 W Hk HW Hz HC Hx.
  eapply progress_trans; [apply (stage_O1 t k j c1 C1 (D3 B0) W); assumption|].
  set (W2 := (Apr (2 * j + 1) + S (Afun (S t) + S W))%nat) in *.
  set (y2 := y2v t (2 * j + 1)) in *.
  pose proof (pw_pos c1) as Hp1.
  eapply progress_trans.
  { apply E_step. apply inc_bin. exact HC. }
  eapply progress_trans.
  { apply phase2. apply inc_bin. lia. }
  eapply evstep_progress_trans.
  { apply (skip_plain (pw c1 - 1 - (C1 + 1)) c1 W2 (C1 + 1) (y2 + 1) (D3 B0)); lia. }
  replace (C1 + 1 + (pw c1 - 1 - (C1 + 1))) with (pw c1 - 1) by lia.
  rewrite bin_ones.
  eapply progress_trans.
  { apply phase1. apply inc_bin. lia. }
  apply fin_plain.
Qed.

Lemma tailS_fin : forall u Vl, Vl <> 0 -> Vl + 1 < pw u ->
  AC (TL (bin u Vl) (U B0)) (oL (S (S u))) -->+
    FC (Nat.odd (S u)) (Apr (S u)) (S (S (S u))) (2 * pw u - 2 * Vl + 2 * pw (S u) - 1).
Proof.
  intros u Vl H0 H1.
  eapply progress_trans; [apply tailS; assumption|].
  apply fin_plain.
Qed.

(* The low digits all ones under the defect at the right overflow: both defects merge at once *)
Lemma tailS_top : forall u Vl, Vl + 1 = pw u -> (1 <= u)%nat ->
  AC (TL (bin u Vl) (U B0)) (oL (S (S u))) -->+
    FC (Nat.odd (S u)) (Apr (S u)) (S (S (S u))) (2 * pw u - 2 * Vl + 2 * pw (S u) - 1).
Proof.
  intros u Vl H Hu.
  replace Vl with (pw u - 1) by lia. clear H Vl.
  rewrite bin_ones.
  destruct u as [|u0]; [lia|].
  replace (TL (oL (S u0)) (U B0)) with (S0 >> U (TL (oL u0) (U B0))) by reflexivity.
  eapply progress_trans; [apply ovf1|].
  assert (Hx : inc (true :: zL (S (S (S u0)))) = Some (bin (S (S (S (S u0)))) 2)).
  { rewrite <- bin_zero.
    change (true :: bin (S (S (S u0))) 0) with (bin (S (S (S (S u0)))) (2 * 0 + 1)).
    apply inc_bin. rewrite !pw_S. pose proof (pw_pos u0). lia. }
  eapply progress_trans; [apply (E_absorb 0 u0)|].
  eapply progress_trans; [apply phase2; exact Hx|].
  replace (0 + u0 + 2)%nat with (S (S u0)) by lia.
  pose proof (pw_S (S u0)) as P1. pose proof (pw_S (S (S u0))) as P2. pose proof (pw_S (S (S (S u0)))) as P3.
  pose proof (pw_pos (S u0)) as P4.
  replace (2 * pw (S u0) - 2 * (pw (S u0) - 1) + 2 * pw (S (S u0)) - 1) with (2 + 2 * pw (S (S u0)) - 1) by lia.
  apply d3_fin. lia.
Qed.

End Part_Map.
Import Part_Map.

Module Part_Close1.

Local Open Scope N_scope.

(* Runs of ones as arithmetic *)
Definition ones_on (V : N) (p q : nat) : Prop :=
  (p <= q)%nat /\ exists a b, b < pw p /\ V = a * pw q + (pw q - pw p) + b.

Definition LR (D : N) : Prop :=
  exists p q, ones_on D p q /\ (2 * p + 25 <= 5 * (q - p))%nat.

Lemma mod_uniq : forall M a b r s, r < M -> s < M -> a * M + r = b * M + s -> a = b /\ r = s.
Proof.
  intros M a b r s Hr Hs H.
  destruct (N.lt_trichotomy a b) as [Hl|[He|Hg]].
  - exfalso. assert ((a + 1) * M <= b * M) as H1 by (apply N.mul_le_mono_r; lia). lia.
  - subst. lia.
  - exfalso. assert ((b + 1) * M <= a * M) as H1 by (apply N.mul_le_mono_r; lia). lia.
Qed.

Lemma pw_split : forall a b, (a <= b)%nat -> pw b = pw a * pw (b - a).
Proof. intros a b H. rewrite <- pw_add. f_equal. lia. Qed.

Lemma ones_sub_lo : forall V p p' q, ones_on V p q -> (p <= p' <= q)%nat -> ones_on V p' q.
Proof.
  intros V p p' q [Hpq [a [b [Hb HV]]]] Hp.
  split; [lia|].
  pose proof (pw_le p p' (proj1 Hp)) as H1. pose proof (pw_le p' q (proj2 Hp)) as H2.
  exists a, (pw p' - pw p + b). split; lia.
Qed.

Lemma ones_sub_hi : forall V p q' q, ones_on V p q -> (p <= q' <= q)%nat -> ones_on V p q'.
Proof.
  intros V p q' q [Hpq [a [b [Hb HV]]]] Hp.
  split; [lia|].
  pose proof (pw_le p q' (proj1 Hp)) as H1.
  pose proof (pw_split q' q (proj2 Hp)) as H2.
  pose proof (pw_pos (q - q')) as H3.
  destruct (pw (q - q')) as [|d] eqn:Ed; [lia|].
  set (Pd := N.pos d) in *.
  exists (a * Pd + (Pd - 1)), b. split; [exact Hb|].
  rewrite HV, H2.
  assert (Pd * pw q' <= pw q' * Pd) by lia.
  replace ((a * Pd + (Pd - 1)) * pw q') with (a * (pw q' * Pd) + (pw q' * Pd - pw q')).
  - pose proof (pw_pos q'). nia.
  - assert (Hx : (Pd - 1) * pw q' = pw q' * Pd - pw q').
    { replace Pd with (Pd - 1 + 1) at 2 by lia. nia. }
    nia.
Qed.

Lemma ones_sub : forall V p p' q' q, ones_on V p q -> (p <= p')%nat -> (q' <= q)%nat -> (p' <= q')%nat ->
  ones_on V p' q'.
Proof.
  intros V p p' q' q H H1 H2 H3.
  apply (ones_sub_lo V p p' q'); [|lia].
  apply (ones_sub_hi V p q' q); [exact H|].
  destruct H. lia.
Qed.

Lemma ones_high : forall V p q n, ones_on V p q -> (q <= n)%nat -> ones_on (V + pw n) p q.
Proof.
  intros V p q n [Hpq [a [b [Hb HV]]]] Hn.
  split; [exact Hpq|].
  pose proof (pw_split q n Hn) as H2.
  exists (a + pw (n - q)), b. split; [exact Hb|].
  rewrite HV, H2. nia.
Qed.

(* Dividing out the first set bit *)
Lemma ones_shift : forall V V1 r p q, V = pw r * (2 * V1 + 1) -> ones_on V p q -> (r < p)%nat ->
  ones_on V1 (p - S r) (q - S r).
Proof.
  intros V V1 r p q HV [Hpq [a [b [Hb HE]]]] Hr.
  split; [lia|].
  pose proof (pw_split (S r) p Hr) as Hp.
  pose proof (pw_split (S r) q ltac:(lia)) as Hq.
  rewrite pw_S in Hp, Hq.
  set (P1 := pw (p - S r)) in *. set (Q1 := pw (q - S r)) in *. set (R := pw r) in *.
  pose proof (pw_pos r) as HR. fold R in HR.
  assert (HPQ : P1 <= Q1) by (apply pw_le; lia).
  set (X := a * Q1 + (Q1 - P1)) in *.
  assert (Ha : pw q * a + (pw q - pw p) = 2 * R * X).
  { rewrite Hp, Hq. unfold X.
    replace (Q1 - P1) with (Q1 - P1) by reflexivity.
    assert (Hm : 2 * R * Q1 - 2 * R * P1 = 2 * R * (Q1 - P1)).
    { rewrite N.mul_sub_distr_l. reflexivity. }
    nia. }
  assert (HE2 : R * (2 * V1 + 1) = 2 * R * X + b).
  { rewrite <- HV, HE. lia. }
  assert (V1 >= X) as HV1.
  { destruct (N.lt_ge_cases V1 X) as [Hlt|Hge]; [|lia].
    exfalso. assert (V1 + 1 <= X) as H3 by lia.
    assert (2 * R * (V1 + 1) <= 2 * R * X) as H4 by (apply N.mul_le_mono_l; lia). nia. }
  exists (a), (V1 - X). split.
  - assert (Hbb : b = R + 2 * R * (V1 - X)).
    { assert (2 * R * V1 = 2 * R * X + 2 * R * (V1 - X)) as H5.
      { rewrite <- N.mul_add_distr_l. f_equal. lia. }
      nia. }
    rewrite Hp in Hb.
    assert (2 * R * (V1 - X) < 2 * R * P1) as H6 by lia.
    apply N.mul_lt_mono_pos_l with (2 * R); lia.
  - unfold X. lia.
Qed.

(* Subtracting a number with zeros on the run *)
Lemma int_sub : forall A i j Y Yh Yl, ones_on A i j -> (i < j)%nat -> Y = Yh * pw j + Yl -> Yl < pw i -> Y <= A ->
  ones_on (A - Y) (S i) j.
Proof.
  intros A i j Y Yh Yl [Hij [a [b [Hb HA]]]] Hlt HY HYl HYA.
  split; [lia|].
  pose proof (pw_lt i j Hlt) as H2. pose proof (pw_pos i) as H1.
  assert (a >= Yh) as Hge.
  { destruct (N.lt_ge_cases a Yh) as [Hl|Hg]; [|lia].
    exfalso. assert ((a + 1) * pw j <= Yh * pw j) as H3 by (apply N.mul_le_mono_r; lia). nia. }
  exists (a - Yh), (pw i + b - Yl). split.
  - rewrite pw_S. lia.
  - rewrite pw_S.
    assert (a * pw j = (a - Yh) * pw j + Yh * pw j) as H4.
    { rewrite <- N.mul_add_distr_r. f_equal. lia. }
    lia.
Qed.

(* Ones of a number of the form 2^W - Y - K + Q *)
Lemma fresh : forall G Y K0 Q Wf f g Yh Yl, G + Y + K0 = pw Wf + Q ->
  Y = Yh * pw g + Yl -> Yl < pw f -> K0 <= pw f -> Q < K0 -> (f < g)%nat -> (g <= Wf)%nat ->
  ones_on G (S f) g.
Proof.
  intros G Y K0 Q Wf f g Yh Yl HG HY HYl HK HQ Hfg HgW.
  split; [lia|].
  pose proof (pw_split g Wf HgW) as HW.
  set (M := pw (Wf - g)) in *.
  pose proof (pw_lt f g Hfg) as H2. pose proof (pw_pos f) as H1.
  set (B := Yl + K0 - Q) in *.
  assert (HB : G + Yh * pw g + B = pw g * M) by (unfold B; lia).
  assert (HB0 : 0 < B) by (unfold B; lia).
  assert (HB1 : B < 2 * pw f) by (unfold B; lia).
  assert (M >= Yh + 1) as HM.
  { destruct (N.lt_ge_cases M (Yh + 1)) as [Hl|Hg]; [|lia].
    exfalso. assert (M * pw g <= Yh * pw g) as H3 by (apply N.mul_le_mono_r; lia). nia. }
  exists (M - Yh - 1), (2 * pw f - B). split.
  - rewrite pw_S. lia.
  - rewrite pw_S.
    assert (M * pw g = (M - Yh - 1) * pw g + Yh * pw g + pw g) as H4.
    { replace M with (M - Yh - 1 + Yh + 1) at 1 by lia. nia. }
    nia.
Qed.

(* The first set bit is at or below any cell of a run *)
Lemma ones_tz : forall V V1 r p q, V = pw r * (2 * V1 + 1) -> ones_on V p q -> (p < q)%nat -> (r <= p)%nat.
Proof.
  intros V V1 r p q HV [Hpq [a [b [Hb HE]]]] Hlt.
  destruct (Nat.le_gt_cases r p) as [H|H]; [exact H|exfalso].
  pose proof (pw_split (S p) r H) as Hr. rewrite pw_S in Hr.
  pose proof (pw_split (S p) q Hlt) as Hq. rewrite pw_S in Hq.
  pose proof (pw_pos p) as H1.
  set (P := pw p) in *.
  set (R := pw (r - S p)) in *. set (Q1 := pw (q - S p)) in *.
  assert (HE2 : 2 * P * (R * (2 * V1 + 1)) + P = 2 * P * (a * Q1 + Q1) + b).
  { assert (pw q - P + P = pw q) as H3 by (rewrite Hq; pose proof (pw_pos (q - S p)); nia).
    rewrite Hr in HV. rewrite Hq in *. nia. }
  destruct (N.lt_ge_cases (R * (2 * V1 + 1)) (a * Q1 + Q1)) as [Hl|Hg].
  - assert (2 * P * (R * (2 * V1 + 1) + 1) <= 2 * P * (a * Q1 + Q1)) as H4
      by (apply N.mul_le_mono_l; lia).
    nia.
  - assert (2 * P * (a * Q1 + Q1) <= 2 * P * (R * (2 * V1 + 1))) as H4
      by (apply N.mul_le_mono_l; lia).
    lia.
Qed.

(* Two cells where X has a one and Y a zero exclude X = Y and X = Y + 2^x *)
Definition cell1 (V : N) (c : nat) : Prop := exists a b, b < pw c /\ V = a * pw (S c) + pw c + b.
Definition cell0 (V : N) (c : nat) : Prop := exists a b, b < pw c /\ V = a * pw (S c) + b.

Lemma ones_cell : forall V p q c, ones_on V p q -> (p <= c < q)%nat -> cell1 V c.
Proof.
  intros V p q c H Hc.
  destruct (ones_sub V p c (S c) q H) as [_ [a [b [Hb HV]]]]; [lia|lia|lia|].
  exists a, b. split; [exact Hb|]. rewrite HV. rewrite pw_S. lia.
Qed.

Lemma two_zero : forall X Y c1 c2, (c1 < c2)%nat ->
  cell1 X c1 -> cell1 X c2 -> cell0 Y c1 -> cell0 Y c2 ->
  X <> Y /\ forall x, X <> Y + pw x.
Proof.
  intros X Y c1 c2 Hc [cx [dx [Hdx HX1]]] [ax [bx [Hbx HX2]]] [cy [dy [Hdy HY1]]] [ay [by' [Hby HY2]]].
  pose proof (pw_S c2) as HS2. pose proof (pw_S c1) as HS1.
  pose proof (pw_split (S c1) c2 Hc) as HP. rewrite HS1 in HP.
  set (R := pw (c2 - S c1)) in *.
  pose proof (pw_pos (c2 - S c1)) as HR. fold R in HR.
  pose proof (pw_pos c1) as H1. pose proof (pw_pos c2) as H2.
  assert (HPP : pw c1 <= pw c2) by (apply pw_le; lia).
  set (P1 := pw c1) in *. set (P := pw c2) in *.
  assert (Hne : X <> Y).
  { intros E. rewrite E in HX2. rewrite HY2 in HX2.
    destruct (mod_uniq (pw (S c2)) ay ax by' (P + bx)) as [_ E2]; [lia|lia|lia|].
    lia. }
  split; [exact Hne|].
  intros x E.
  destruct (Nat.le_gt_cases x c1) as [Hx|Hx].
  - (* x <= c1: the carry must reach c2, and X has no cell c1 *)
    pose proof (pw_le x c1 Hx) as Hxp. fold P1 in Hxp.
    assert (HE : ax * pw (S c2) + (P + bx) = ay * pw (S c2) + (by' + pw x)) by lia.
    destruct (mod_uniq (pw (S c2)) ax ay (P + bx) (by' + pw x)) as [_ E2]; [lia|lia|exact HE|].
    assert (bx < P1) as Hb by lia.
    (* X modulo 2 P1 *)
    assert (HMul : pw (S c2) = (2 * R) * pw (S c1)) by (rewrite HS2, HS1, HP; lia).
    assert (HX4 : X = (ax * (2 * R) + R) * pw (S c1) + bx).
    { rewrite HX2, HMul. rewrite HS1, HP. nia. }
    assert (HX5 : X = cx * pw (S c1) + (P1 + dx)) by lia.
    destruct (mod_uniq (pw (S c1)) (ax * (2 * R) + R) cx bx (P1 + dx)) as [_ E3]; [rewrite HS1; lia|rewrite HS1; lia|lia|].
    lia.
  - (* x > c1: cell c1 is not changed *)
    assert (HM : pw x = pw (x - S c1) * pw (S c1)).
    { rewrite N.mul_comm. apply pw_split. lia. }
    assert (HE : cx * pw (S c1) + (P1 + dx) = (cy + pw (x - S c1)) * pw (S c1) + dy).
    { rewrite N.mul_add_distr_r, <- HM. lia. }
    destruct (mod_uniq (pw (S c1)) cx (cy + pw (x - S c1)) (P1 + dx) dy) as [_ E3]; [rewrite HS1; lia|rewrite HS1; lia|exact HE|].
    lia.
Qed.

Lemma ones_not_pow : forall D p q, ones_on D p q -> (p + 2 <= q)%nat ->
  D <> 0 /\ forall x, D <> pw x.
Proof.
  intros D p q H Hq.
  assert (Hz0 : forall c, cell0 0 c).
  { intros c. exists 0, 0. split; [pose proof (pw_pos c); lia|reflexivity]. }
  destruct (two_zero D 0 p (S p)) as [H1 H2].
  - lia.
  - apply (ones_cell D p q); [exact H|lia].
  - apply (ones_cell D p q); [exact H|lia].
  - apply Hz0.
  - apply Hz0.
  - split; [exact H1|].
    intros x. specialize (H2 x). rewrite N.add_0_l in H2. exact H2.
Qed.

(* Second set bit below p if the low part is not a power of 2 *)
Lemma second_bit : forall Zh v p t C r C1, v <> 0 -> v < pw p -> (forall x, v <> pw x) ->
  Zh * pw p + v = pw t * (2 * C + 1) -> C = pw r * (2 * C1 + 1) -> (t + r + 2 <= p)%nat.
Proof.
  intros Zh v p t C r C1 H0 Hv Hx HZ HC.
  pose proof (pw_pos t) as Ht.
  assert (Ht1 : (t < p)%nat).
  { destruct (Nat.lt_ge_cases t p) as [H|H]; [exact H|exfalso].
    pose proof (pw_split p t H) as H2.
    assert (HE : (Zh * pw p + v) = ((pw (t - p) * (2 * C + 1)) * pw p + 0)).
    { rewrite HZ, H2. lia. }
    destruct (mod_uniq (pw p) Zh _ v 0 Hv ltac:(pose proof (pw_pos p); lia) HE) as [_ E]. lia. }
  destruct (Nat.le_gt_cases (t + r + 2) p) as [H|H]; [exact H|exfalso].
  (* then v is pw t *)
  assert (HM : pw t * (2 * C) = (pw (t + S r - p) * (2 * C1 + 1)) * pw p).
  { rewrite HC.
    pose proof (pw_split p (t + S r) ltac:(lia)) as H3.
    assert (pw (t + S r) = pw t * (2 * pw r)) as H4 by (rewrite pw_add, pw_S; reflexivity).
    assert (pw t * (2 * (pw r * (2 * C1 + 1))) = pw (t + S r) * (2 * C1 + 1)) as H5.
    { rewrite H4. lia. }
    rewrite H5, H3. lia. }
  assert (HE : Zh * pw p + v = (pw (t + S r - p) * (2 * C1 + 1)) * pw p + pw t).
  { rewrite HZ, <- HM. lia. }
  pose proof (pw_lt t p Ht1) as H6.
  destruct (mod_uniq (pw p) Zh _ v (pw t) Hv ltac:(lia) HE) as [_ E].
  apply (Hx t). exact E.
Qed.

(* Popcount *)
Fixpoint pcp (p : positive) : nat :=
  match p with
  | xH => 1
  | xO q => pcp q
  | xI q => S (pcp q)
  end.
Definition pc (n : N) : nat := match n with N0 => 0%nat | Npos p => pcp p end.

Lemma pc_double : forall x, pc (2 * x) = pc x.
Proof. intros x. destruct x; reflexivity. Qed.
Lemma pc_double1 : forall x, pc (2 * x + 1) = S (pc x).
Proof. intros x. destruct x; reflexivity. Qed.

Lemma pc_succ : forall x, (pc (x + 1) <= pc x + 1)%nat.
Proof.
  intros x. induction x as [x IH] using (well_founded_ind N.lt_wf_0).
  destruct (N_parity x) as [[w Hw]|[w Hw]]; subst x.
  - rewrite pc_double1, pc_double. lia.
  - replace (2 * w + 1 + 1) with (2 * (w + 1)) by lia.
    rewrite pc_double, pc_double1.
    destruct (N.eq_dec w 0) as [E|E].
    + subst w. simpl. lia.
    + specialize (IH w ltac:(lia)). lia.
Qed.

Lemma pc_add : forall x y, (pc (x + y) <= pc x + pc y)%nat.
Proof.
  intros x. induction x as [x IH] using (well_founded_ind N.lt_wf_0). intros y.
  destruct (N.eq_dec x 0) as [E|E].
  - subst x. simpl. lia.
  - destruct (N_parity x) as [[u Hu]|[u Hu]]; destruct (N_parity y) as [[v Hv]|[v Hv]]; subst x y.
    + replace (2 * u + 2 * v) with (2 * (u + v)) by lia.
      rewrite !pc_double. apply IH. lia.
    + replace (2 * u + (2 * v + 1)) with (2 * (u + v) + 1) by lia.
      rewrite pc_double1, pc_double, pc_double1. pose proof (IH u ltac:(lia) v). lia.
    + replace (2 * u + 1 + 2 * v) with (2 * (u + v) + 1) by lia.
      rewrite !pc_double1, pc_double.
      destruct (N.eq_dec u 0) as [E0|E0].
      * subst u. simpl. lia.
      * pose proof (IH u ltac:(lia) v). lia.
    + replace (2 * u + 1 + (2 * v + 1)) with (2 * (u + (v + 1))) by lia.
      rewrite pc_double, !pc_double1.
      destruct (N.eq_dec u 0) as [E0|E0].
      * subst u. simpl (0 + (v + 1)). pose proof (pc_succ v). simpl (pc 0). lia.
      * pose proof (IH u ltac:(lia) (v + 1)). pose proof (pc_succ v). lia.
Qed.

Lemma pc_pw : forall n, pc (pw n) = 1%nat.
Proof.
  induction n as [|n IH]; [reflexivity|]. rewrite pw_S, pc_double. exact IH.
Qed.

Lemma pc_split : forall n x y, x < pw n -> pc (x + pw n * y) = (pc x + pc y)%nat.
Proof.
  induction n as [|n IH]; intros x y H.
  - rewrite pw_0 in *. assert (x = 0) by lia. subst x. replace (0 + 1 * y) with y by lia. reflexivity.
  - rewrite pw_S in *. destruct (N_parity x) as [[w Hw]|[w Hw]]; subst x.
    + replace (2 * w + 2 * pw n * y) with (2 * (w + pw n * y)) by lia.
      rewrite !pc_double. apply IH. lia.
    + replace (2 * w + 1 + 2 * pw n * y) with (2 * (w + pw n * y) + 1) by lia.
      rewrite !pc_double1. rewrite IH by lia. lia.
Qed.

Lemma pc_ones_n : forall n, pc (pw n - 1) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (pw (S n) - 1) with (2 * (pw n - 1) + 1) by (rewrite pw_S; pose proof (pw_pos n); lia).
  rewrite pc_double1, IH. reflexivity.
Qed.

Lemma pc_on : forall V p q, ones_on V p q -> (q - p <= pc V)%nat.
Proof.
  intros V p q [Hpq [a [b [Hb HV]]]].
  pose proof (pw_split p q Hpq) as Hq.
  set (n := (q - p)%nat) in *.
  pose proof (pw_pos n) as Hn. pose proof (pw_pos p) as Hp.
  assert (HV2 : V = b + pw p * ((pw n - 1) + pw n * a)).
  { rewrite HV, Hq. nia. }
  rewrite HV2, (pc_split p) by exact Hb.
  rewrite (N.add_comm (pw n - 1)).
  replace (pw n * a + (pw n - 1)) with ((pw n - 1) + pw n * a) by lia.
  rewrite (pc_split n) by lia. rewrite pc_ones_n. lia.
Qed.

Lemma pc_three : forall a b c, (pc (pw a + pw b + pw c) <= 3)%nat.
Proof.
  intros a b c.
  pose proof (pc_add (pw a + pw b) (pw c)). pose proof (pc_add (pw a) (pw b)).
  rewrite !pc_pw in *. lia.
Qed.

Lemma pc_two : forall a b, (pc (pw a + pw b) <= 2)%nat.
Proof.
  intros a b. pose proof (pc_add (pw a) (pw b)). rewrite !pc_pw in *. lia.
Qed.

End Part_Close1.
Import Part_Close1.

Module Part_Arith1.

(* A run [x,y) of G', a zero zone [zu,zv) of y1' in the coordinates of G1' = G' >> o.
   The candidate: 7 x + 32 <= 5 y + 2 o and so on for the four corners. *)
Definition cand (x y zu zv o : nat) : Prop :=
  7 * x + 32 <= 5 * y + 2 * o /\ 7 * x + 32 <= 5 * (zv + o) + 2 * o /\
  7 * (zu + o) + 32 <= 5 * y + 2 * o /\ 7 * (zu + o) + 32 <= 5 * (zv + o) + 2 * o.

(* Leaf with Yd = y2 (m, r), next a' odd. Lb = L+3 or L+1. *)
Lemma arith_O_odd : forall m r Lb Wp A Ap rp ap A2 A3 f1,
  (5 * m <= 2 * A <= 5 * m + 1) -> (5 * r + 1 <= 2 * Ap <= 5 * r + 2) ->
  (m + r + Lb <= Wp + 1) -> (Wp <= m + r + Lb + 2) ->
  (5 * Lb <= 2 * ap + 9) -> (2 * ap + 3 <= 5 * Lb) -> (12 <= Lb) ->
  (5 * rp + 1 <= 2 * A2 <= 5 * rp + 2) -> (5 * ap <= 2 * A3 <= 5 * ap + 1) ->
  (Wp + A + Ap + 2 + 1 >= rp + A2 + A3 + ap + 2) ->
  (26 <= m \/ 90 <= Wp) ->
  (Lb <= f1) -> (Ap + r + 2 <= f1) -> (f1 <= Lb \/ f1 <= Ap + r + 2) ->
  (Lb < Ap -> rp <= Lb) -> (Ap <= Lb -> r + 1 <= A -> rp <= f1 + 1) ->
  (Lb < Ap /\ cand Lb Ap (A2 + rp + 1) (A2 + A3) (rp + 1)) \/
  (Lb < Ap /\ cand Lb Ap 0 (A2 - 1) (rp + 1)) \/
  (r + 1 <= A /\ cand (f1 + 1) (Ap + A + 1) (A2 + rp + 1) (A2 + A3) (rp + 1)) \/
  (r + 1 <= A /\ cand (f1 + 1) (Ap + A + 1) 0 (A2 - 1) (rp + 1)).
Proof.
  intros. unfold cand.
  assert (A2 >= 1) by lia.
  destruct (Nat.le_gt_cases (7 * (f1 + 1) + 32) (5 * (A2 + rp) + 2 * (rp + 1))) as [Hd|Hd];
  (destruct (Nat.lt_ge_cases Lb Ap) as [Hz0|Hz0];
   [destruct (Nat.le_gt_cases (7 * Lb + 32) (5 * Ap + 2 * (rp + 1))) as [Ha|Ha];
    [destruct (Nat.le_gt_cases (7 * (rp + 1) + 32) (5 * Ap + 2 * (rp + 1))) as [Ha2|Ha2];
     [destruct (Nat.le_gt_cases (7 * (A2 + 2 * rp + 2) + 32) (5 * Ap + 2 * (rp + 1))) as [Hb|Hb];
      [left; repeat split; lia
      |destruct (Nat.le_gt_cases (7 * Lb + 32) (5 * (A2 + rp) + 2 * (rp + 1))) as [Hc|Hc];
       [right; left; repeat split; lia|right; right]]
     |right; right]
    |right; right]
   |right; right]).
  all: first [right; repeat split; lia | left; repeat split; lia].
Qed.

(* Leaf with Yd = y2 (m, r), next a' even, offset 0. *)
Lemma arith_O_even : forall m r Lb Wp A Ap ap A3 f1,
  (5 * m <= 2 * A <= 5 * m + 1) -> (5 * r + 1 <= 2 * Ap <= 5 * r + 2) ->
  (m + r + Lb <= Wp + 1) -> (Wp <= m + r + Lb + 2) ->
  (5 * Lb <= 2 * ap + 9) -> (2 * ap + 3 <= 5 * Lb) -> (12 <= Lb) ->
  (5 * ap <= 2 * A3 <= 5 * ap + 1) ->
  (Wp + A + Ap + 2 >= A3 + ap + 1) ->
  (26 <= m \/ 90 <= Wp) ->
  (Lb <= f1) -> (Ap + r + 2 <= f1) -> (f1 <= Lb \/ f1 <= Ap + r + 2) ->
  cand Lb Ap 0 (A3 - 1) 0 \/
  (r + 1 <= A /\ cand (f1 + 1) (Ap + A + 1) 0 (A3 - 1) 0).
Proof.
  intros. unfold cand.
  destruct (Nat.le_gt_cases (7 * Lb + 32) (5 * Ap)) as [Ha|Ha].
  - left. repeat split; lia.
  - right. repeat split; lia.
Qed.

(* Leaf with Yd = y (m), r' = 0 when a' is odd *)
Lemma arith_E_odd : forall m Lb Wp A ap A3,
  (5 * m <= 2 * A <= 5 * m + 1) ->
  (m + Lb <= Wp + 2) -> (Wp <= m + Lb + 1) ->
  (5 * Lb <= 2 * ap + 9) -> (2 * ap + 3 <= 5 * Lb) -> (12 <= Lb) ->
  (5 * ap <= 2 * A3 <= 5 * ap + 1) ->
  (Wp + A + 1 >= A3 + ap + 2) ->
  cand Lb A 2 (1 + A3) 1.
Proof.
  intros. unfold cand. repeat split; lia.
Qed.

Lemma arith_E_even : forall m Lb Wp A ap A3,
  (5 * m <= 2 * A <= 5 * m + 1) ->
  (m + Lb <= Wp + 2) -> (Wp <= m + Lb + 1) ->
  (5 * Lb <= 2 * ap + 9) -> (2 * ap + 3 <= 5 * Lb) -> (12 <= Lb) ->
  (5 * ap <= 2 * A3 <= 5 * ap + 1) ->
  (Wp + A + 1 >= A3 + ap + 1) ->
  cand Lb A 0 (A3 - 1) 0.
Proof.
  intros. unfold cand. repeat split; lia.
Qed.

End Part_Arith1.
Import Part_Arith1.

Module Part_Close2.

Local Open Scope N_scope.

Lemma Afun_bd : forall m, (5 * m <= 2 * Afun m <= 5 * m + 1)%nat.
Proof.
  intros m. destruct (Nat.Even_or_Odd m) as [[j Hj]|[j Hj]]; subst m.
  - rewrite Afun_even. lia.
  - rewrite Afun_odd. lia.
Qed.

Lemma Apr_bd : forall r, (5 * r + 1 <= 2 * Apr r <= 5 * r + 2)%nat.
Proof.
  intros r. destruct (Nat.Even_or_Odd r) as [[j Hj]|[j Hj]]; subst r.
  - rewrite Apr_even. lia.
  - rewrite Apr_odd. lia.
Qed.

Definition Ya (m : nat) : N := pw (m + 2) - 3.
Definition y1e (t : nat) : N := pw (Afun (S t) - 1) * Ya (S t).
Definition y1o (t r : nat) : N := pw (Apr r - 1) * (2 * zv t r + 1).

Lemma pw_add_r2 : forall m, pw (m + 2) = 4 * pw m.
Proof. intros m. rewrite pw_add. change (pw 2) with 4. lia. Qed.

Lemma Ya_lo : forall t, pw (S t + 1) <= Ya (S t).
Proof.
  intros t. unfold Ya. replace (S t + 2)%nat with (S (S t + 1)) by lia. rewrite pw_S.
  replace (S t + 1)%nat with (S (S t)) by lia. rewrite !pw_S. pose proof (pw_pos t). lia.
Qed.

Lemma Ya_hi : forall m, Ya m < pw (m + 2).
Proof.
  intros m. unfold Ya. rewrite pw_add_r2. pose proof (pw_pos m). lia.
Qed.

Lemma yv_Ya : forall t, yv t = pw (Afun (S t)) * Ya (S t).
Proof.
  intros t. unfold yv, x1v, Ya. f_equal.
  replace (S t + 2)%nat with (S (S (S t))) by lia. rewrite (pw_S (S (S t))).
  pose proof (pw_ge2 (S t)). lia.
Qed.

Lemma Afun_pos : forall t, (1 <= Afun (S t))%nat.
Proof. intros t. pose proof (Afun_bd (S t)). lia. Qed.
Lemma Apr_pos : forall r, (1 <= Apr r)%nat.
Proof. intros r. pose proof (Apr_bd r). lia. Qed.

Lemma pw_pred2 : forall n, (1 <= n)%nat -> pw n = 2 * pw (n - 1).
Proof. intros n H. rewrite <- pw_S. f_equal. lia. Qed.

Lemma yv_y1e : forall t, yv t = 2 * y1e t.
Proof.
  intros t. rewrite yv_Ya. unfold y1e. rewrite (pw_pred2 (Afun (S t))) by apply Afun_pos. lia.
Qed.

Lemma y2v_y1o : forall t r, y2v t r = 2 * y1o t r.
Proof.
  intros t r. unfold y2v, y1o. rewrite (pw_pred2 (Apr r)) by apply Apr_pos. lia.
Qed.

Lemma zv_form : forall t r, 2 * zv t r + 1 = 2 * yv t + (pw (r + 2) - 1).
Proof.
  intros t r. unfold zv. rewrite pw_add_r2. pose proof (pw_pos r). lia.
Qed.

Lemma y1o_split : forall t r,
  y1o t r = pw (Apr r + Afun (S t)) * Ya (S t) + pw (Apr r - 1) * (pw (r + 2) - 1).
Proof.
  intros t r. unfold y1o. rewrite zv_form, yv_Ya, (pw_add (Apr r)).
  rewrite (pw_pred2 (Apr r)) by apply Apr_pos.
  set (a1 := pw (Apr r - 1)). lia.
Qed.

Lemma y2v_split : forall t r,
  y2v t r = pw (Apr r + (Afun (S t) + 1)) * Ya (S t) + pw (Apr r) * (pw (r + 2) - 1).
Proof.
  intros t r. unfold y2v. rewrite zv_form, yv_Ya.
  rewrite (pw_add (Apr r)), (pw_add (Afun (S t))). change (pw 1) with 2. lia.
Qed.

Lemma Yc_lt : forall a r, pw a * (pw (r + 2) - 1) < pw (a + (r + 2)).
Proof.
  intros a r. rewrite (pw_add a). pose proof (pw_pos a). pose proof (pw_pos (r + 2)). nia.
Qed.

Lemma y2v_lt : forall t r T, (Afun (S t) + (S t + 3) <= T)%nat -> (r + 3 <= T)%nat ->
  y2v t r < pw (Apr r + (T + 1)).
Proof.
  intros t r T H1 H2.
  unfold y2v. rewrite zv_form, yv_Ya.
  rewrite (pw_add (Apr r)).
  pose proof (Ya_hi (S t)) as H3.
  assert (Hy : 2 * (pw (Afun (S t)) * Ya (S t)) + 1 <= pw T).
  { pose proof (pw_le _ _ H1) as H4. rewrite (pw_add (Afun (S t))) in H4.
    replace (S t + 3)%nat with (S (S t + 2)) in H4 by lia. rewrite pw_S in H4.
    pose proof (pw_pos (Afun (S t))).
    assert (pw (Afun (S t)) * (Ya (S t) + 1) <= pw (Afun (S t)) * pw (S t + 2)) as H5
      by (apply N.mul_le_mono_l; lia).
    nia. }
  pose proof (pw_le (r + 2) T ltac:(lia)) as Hr.
  assert (HT : pw (T + 1) = 2 * pw T) by (rewrite pw_add; change (pw 1) with 2; lia).
  pose proof (pw_pos (Apr r)) as Hp. pose proof (pw_pos (r + 2)) as Hp2.
  apply N.mul_lt_mono_pos_l; lia.
Qed.

Lemma yv_lt : forall t T, (Afun (S t) + (S t + 2) <= T)%nat -> yv t < pw T.
Proof.
  intros t T H. rewrite yv_Ya.
  pose proof (pw_le _ _ H) as H4. rewrite pw_add in H4.
  pose proof (Ya_hi (S t)) as H3.
  pose proof (pw_pos (Afun (S t))) as H5.
  assert (pw (Afun (S t)) * Ya (S t) < pw (Afun (S t)) * pw (S t + 2)) as H6
    by (apply N.mul_lt_mono_pos_l; lia).
  lia.
Qed.

(* Zones of y1' *)
Definition Zone (Y : N) (zu zv : nat) : Prop :=
  forall i j, (zu <= i)%nat -> (j <= zv)%nat -> exists Yh Yl, Y = Yh * pw j + Yl /\ Yl < pw i.

Lemma zone_y1o_G : forall t r, Zone (y1o t r) (Apr r + r + 1) (Apr r + Afun (S t)).
Proof.
  intros t r i j Hi Hj.
  exists (pw (Apr r + Afun (S t) - j) * Ya (S t)), (pw (Apr r - 1) * (pw (r + 2) - 1)). split.
  - rewrite y1o_split. rewrite (pw_split j (Apr r + Afun (S t))) by lia. lia.
  - pose proof (Yc_lt (Apr r - 1) r) as H.
    pose proof (Apr_pos r).
    pose proof (pw_le (Apr r - 1 + (r + 2)) i ltac:(lia)). lia.
Qed.

Lemma zone_y1o_Z : forall t r, Zone (y1o t r) 0 (Apr r - 1).
Proof.
  intros t r i j Hi Hj.
  exists (pw (Apr r - 1 - j) * (2 * zv t r + 1)), 0. split.
  - unfold y1o. rewrite (pw_split j (Apr r - 1)) by lia. lia.
  - pose proof (pw_pos i). lia.
Qed.

Lemma zone_y1e_Z : forall t, Zone (y1e t) 0 (Afun (S t) - 1).
Proof.
  intros t i j Hi Hj.
  exists (pw (Afun (S t) - 1 - j) * Ya (S t)), 0. split.
  - unfold y1e. rewrite (pw_split j (Afun (S t) - 1)) by lia. lia.
  - pose proof (pw_pos i). lia.
Qed.

(* From a candidate to the long run *)
Lemma LR_even : forall A x y zu zv Y, ones_on A x y -> cand x y zu zv 0 -> Zone Y zu zv -> Y <= A -> LR (A - Y).
Proof.
  intros A x y zu zv Y H1 [C1 [C2 [C3 C4]]] HZ HY.
  set (i := Nat.max x (zu + 0)). set (j := Nat.min y (zv + 0)).
  assert (Hi : (7 * i + 32 <= 5 * j)%nat).
  { unfold i, j. destruct (Nat.max_spec x (zu + 0)) as [[_ E1]|[_ E1]]; destruct (Nat.min_spec y (zv + 0)) as [[_ E2]|[_ E2]];
    rewrite E1, E2; lia. }
  assert (Hxi : (x <= i)%nat) by (unfold i; lia).
  assert (Hzi : (zu <= i)%nat) by (unfold i; lia).
  assert (Hjy : (j <= y)%nat) by (unfold j; lia).
  assert (Hjz : (j <= zv)%nat) by (unfold j; lia).
  destruct (HZ i j Hzi Hjz) as [Yh [Yl [E Hl]]].
  assert (Hij : (i < j)%nat) by lia.
  pose proof (ones_sub A x i j y H1 Hxi Hjy ltac:(lia)) as H2.
  pose proof (int_sub A i j Y Yh Yl H2 Hij E Hl HY) as H3.
  exists (S i), j. split; [exact H3|lia].
Qed.

Lemma LR_odd : forall G G1 r A x y zu zv Y,
  G = pw r * (2 * G1 + 1) -> ones_on G x y ->
  cand x y zu zv (S r) -> Zone Y zu zv -> Y <= A ->
  (forall p q, ones_on G1 p q -> (q + S r <= y)%nat -> ones_on A p q) -> LR (A - Y).
Proof.
  intros G G1 r A x y zu zv Y HG H1 [C1 [C2 [C3 C4]]] HZ HY HA.
  set (o := S r) in *.
  set (i := Nat.max x (zu + o)). set (j := Nat.min y (zv + o)).
  assert (Hi : (7 * i + 32 <= 5 * j + 2 * o)%nat).
  { unfold i, j. destruct (Nat.max_spec x (zu + o)) as [[_ E1]|[_ E1]]; destruct (Nat.min_spec y (zv + o)) as [[_ E2]|[_ E2]];
    rewrite E1, E2; lia. }
  assert (Hxi : (x <= i)%nat) by (unfold i; lia).
  assert (Hzi : (zu + o <= i)%nat) by (unfold i; lia).
  assert (Hjy : (j <= y)%nat) by (unfold j; lia).
  assert (Hjz : (j <= zv + o)%nat) by (unfold j; lia).
  assert (Hij : (i < j)%nat) by lia.
  pose proof (ones_sub G x i j y H1 Hxi Hjy ltac:(lia)) as H2.
  pose proof (ones_shift G G1 r i j HG H2 ltac:(unfold o in *; lia)) as H3.
  replace (S r) with o in H3 by reflexivity.
  destruct (HZ (i - o)%nat (j - o)%nat ltac:(lia) ltac:(lia)) as [Yh [Yl [E Hl]]].
  pose proof (HA _ _ H3 ltac:(lia)) as H4.
  pose proof (int_sub A (i - o) (j - o) Y Yh Yl H4 ltac:(lia) E Hl HY) as H5.
  exists (S (i - o)), (j - o)%nat. split; [exact H5|lia].
Qed.

(* Ones of G' with no low part of Y *)
Lemma fresh0 : forall G Yh K0 Q Wf f g, G + Yh * pw g + K0 = pw Wf + Q ->
  K0 <= pw f + Q -> Q < K0 -> (f <= g)%nat -> (g <= Wf)%nat ->
  ones_on G f g.
Proof.
  intros G Yh K0 Q Wf f g HG HK HQ Hfg HgW.
  split; [exact Hfg|].
  pose proof (pw_split g Wf HgW) as HW.
  set (M := pw (Wf - g)) in *.
  pose proof (pw_le f g Hfg) as H2. pose proof (pw_pos f) as H1.
  set (B := K0 - Q) in *.
  assert (HB : G + Yh * pw g + B = pw g * M) by (unfold B; lia).
  assert (HB0 : 0 < B) by (unfold B; lia).
  assert (HB1 : B <= pw f) by (unfold B; lia).
  assert (M >= Yh + 1) as HM.
  { destruct (N.lt_ge_cases M (Yh + 1)) as [Hl|Hg]; [|lia].
    exfalso. assert (M * pw g <= Yh * pw g) as H3 by (apply N.mul_le_mono_r; lia). nia. }
  exists (M - Yh - 1), (pw f - B). split; [lia|].
  assert (M * pw g = (M - Yh - 1) * pw g + Yh * pw g + pw g) as H4.
  { replace M with (M - Yh - 1 + Yh + 1) at 1 by lia. nia. }
  nia.
Qed.

End Part_Close2.
Import Part_Close2.

Module Part_Close3.

Local Open Scope N_scope.

Definition DCond (e : bool) (a h r : nat) (G1 G : N) : Prop :=
  forall t, a = S t ->
    (Nat.even a = true -> e = false -> y1e t <= G -> LR (G - y1e t)) /\
    (Nat.even a = false -> e = false -> y1o t r <= G1 -> LR (G1 - y1o t r)) /\
    (Nat.even a = false -> e = true -> Nat.odd r = true ->
       y1o t r <= G1 + pw (h - r) -> LR (G1 + pw (h - r) - y1o t r)).

Definition Inv (e : bool) (a h : nat) (G : N) : Prop :=
  (26 <= a)%nat /\ (2 <= h)%nat /\ pw (h - 2) <= G /\ G < pw h /\
  exists r G1, G = pw r * (2 * G1 + 1) /\ (r + 3 <= h)%nat /\ (e = true -> (r + 9 <= h)%nat) /\
    (r <= a)%nat /\ DCond e a h r G1 G.

Lemma pw_lt_inv : forall x y, pw x < pw y -> (x < y)%nat.
Proof.
  intros x y H. destruct (Nat.lt_ge_cases x y) as [H1|H1]; [exact H1|].
  pose proof (pw_le y x H1). lia.
Qed.

Lemma y1o_lo : forall t r, pw (Apr r + Afun (S t) + (S t + 1)) <= y1o t r.
Proof.
  intros t r. rewrite y1o_split, (pw_add (Apr r + Afun (S t))).
  pose proof (Ya_lo t) as H.
  pose proof (pw_pos (Apr r + Afun (S t))) as H1.
  assert (pw (Apr r + Afun (S t)) * pw (S t + 1) <= pw (Apr r + Afun (S t)) * Ya (S t)) as H2
    by (apply N.mul_le_mono_l; exact H).
  eapply N.le_trans; [exact H2|apply N.le_add_r].
Qed.

Lemma y1e_lo : forall t, pw (Afun (S t) - 1 + (S t + 1)) <= y1e t.
Proof.
  intros t. unfold y1e. rewrite pw_add.
  apply N.mul_le_mono_l. apply Ya_lo.
Qed.

Lemma G1_bound : forall G G1 r Wf x, G = pw r * (2 * G1 + 1) -> G < pw Wf -> pw x <= G1 -> (r + S x < Wf)%nat.
Proof.
  intros G G1 r Wf x H1 H2 H3.
  apply pw_lt_inv. rewrite pw_add, pw_S.
  pose proof (pw_pos r) as H4.
  assert (pw r * (2 * pw x) <= pw r * (2 * G1 + 1)) as H5 by (apply N.mul_le_mono_l; lia).
  lia.
Qed.

Lemma r_lt : forall G G1 r Wf, G = pw r * (2 * G1 + 1) -> G < pw Wf -> (r < Wf)%nat.
Proof.
  intros G G1 r Wf H1 H2. apply pw_lt_inv.
  pose proof (pw_pos r) as H4.
  assert (pw r * 1 <= pw r * (2 * G1 + 1)) as H5 by (apply N.mul_le_mono_l; lia).
  lia.
Qed.

Lemma G1_bound2 : forall G G1 r Wf x, G = pw r * (2 * G1 + 1) -> G < pw Wf ->
  pw x <= G1 + pw (Wf - r) -> (x + r <= Wf)%nat.
Proof.
  intros G G1 r Wf x H1 H2 H3.
  pose proof (r_lt G G1 r Wf H1 H2) as Hr.
  pose proof (pw_split r Wf ltac:(lia)) as H4.
  pose proof (pw_pos r) as H5.
  assert (2 * G1 + 1 < pw (Wf - r)) as H6.
  { apply N.mul_lt_mono_pos_l with (pw r); lia. }
  assert (pw x < pw (S (Wf - r))) as H7 by (rewrite pw_S; lia).
  pose proof (pw_lt_inv _ _ H7). lia.
Qed.

Lemma ones_G1_high : forall G1 n y o p q, (y <= n + o)%nat -> ones_on G1 p q -> (q + o <= y)%nat ->
  ones_on (G1 + pw n) p q.
Proof.
  intros G1 n y o p q H1 H2 H3. apply ones_high; [exact H2|lia].
Qed.

(* Nat facts of the leaf, kept apart from the numbers so that lia stays small *)
Lemma O_nat1 : forall m q Lb Wp A Ap ta,
  (5 * m <= 2 * A <= 5 * m + 1)%nat -> (5 * q + 1 <= 2 * Ap <= 5 * q + 2)%nat ->
  (m + q + Lb <= Wp + 1)%nat -> (Wp <= m + q + Lb + 2)%nat ->
  (5 * Lb <= 2 * ta + 9)%nat -> (2 * ta + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat -> (1 <= m)%nat ->
  (26 <= ta)%nat /\ (Lb <= Ap + A + Wp + 2 - 2)%nat /\ (9 <= Ap + A + Wp + 2)%nat.
Proof. intros. lia. Qed.

Lemma O_r_bound : forall m q Lb Wp A Ap ta r T f1 f2,
  (5 * m <= 2 * A <= 5 * m + 1)%nat -> (5 * q + 1 <= 2 * Ap <= 5 * q + 2)%nat ->
  (m + q + Lb <= Wp + 1)%nat -> (Wp <= m + q + Lb + 2)%nat ->
  (5 * Lb <= 2 * ta + 9)%nat -> (2 * ta + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat -> (1 <= m)%nat ->
  (A + (m + 3) <= T)%nat -> (q + 3 <= T)%nat -> (T <= A + (m + 3) \/ T <= q + 3)%nat ->
  (Lb <= f1)%nat -> (Ap + q + 2 <= f1)%nat -> (f1 <= Lb \/ f1 <= Ap + q + 2)%nat ->
  (Ap + (T + 1) <= f2)%nat -> (Lb <= f2)%nat -> (f2 <= Ap + (T + 1) \/ f2 <= Lb)%nat ->
  (Lb < Ap -> r <= Lb)%nat ->
  (Ap <= Lb -> (S f1 < Ap + (A + 1) /\ r <= S f1) \/ (Ap + (A + 1) <= S f1 /\ r <= S f2))%nat ->
  (r <= ta /\ r + 3 <= Ap + A + Wp + 2)%nat.
Proof.
  intros m q Lb Wp A Ap ta r T f1 f2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
  destruct (Nat.lt_ge_cases Lb Ap) as [H|H].
  - specialize (H18 H). lia.
  - destruct (H19 H) as [[H20 H21]|[H20 H21]]; lia.
Qed.

Lemma O_even_part : forall (G : N) m q Lb Wp A Ap t' f1,
  (5 * m <= 2 * A <= 5 * m + 1)%nat -> (5 * q + 1 <= 2 * Ap <= 5 * q + 2)%nat ->
  (m + q + Lb <= Wp + 1)%nat -> (Wp <= m + q + Lb + 2)%nat ->
  (5 * Lb <= 2 * S t' + 9)%nat -> (2 * S t' + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat ->
  (26 <= m \/ 90 <= Wp)%nat ->
  (Lb <= f1)%nat -> (Ap + q + 2 <= f1)%nat -> (f1 <= Lb \/ f1 <= Ap + q + 2)%nat ->
  (Lb <= Ap -> ones_on G Lb Ap)%nat ->
  (f1 < Ap + (A + 1) -> ones_on G (S f1) (Ap + (A + 1)))%nat ->
  G < pw (Ap + A + Wp + 2) -> y1e t' <= G -> LR (G - y1e t').
Proof.
  intros G m q Lb Wp A Ap t' f1 BA BAp H1 H2 H3 H4 H5 H6 H7 H8 H9 run0 run1 Hhigh Hle.
  pose proof (Afun_bd (S t')) as BA3.
  pose proof (y1e_lo t') as Hl.
  assert (HR : pw (Afun (S t') - 1 + (S t' + 1)) < pw (Ap + A + Wp + 2)) by lia.
  pose proof (pw_lt_inv _ _ HR) as HR2.
  clear HR Hl Hhigh.
  destruct (arith_O_even m q Lb Wp A Ap (S t') (Afun (S t')) f1) as [C|[C1 C]]; try assumption; try lia.
  - apply (LR_even G Lb Ap 0 (Afun (S t') - 1) (y1e t')).
    + apply run0. unfold cand in C. lia.
    + exact C.
    + apply zone_y1e_Z.
    + exact Hle.
  - apply (LR_even G (f1 + 1) (Ap + A + 1) 0 (Afun (S t') - 1) (y1e t')).
    + replace (f1 + 1)%nat with (S f1) by lia. replace (Ap + A + 1)%nat with (Ap + (A + 1))%nat by lia.
      apply run1. unfold cand in C. lia.
    + exact C.
    + apply zone_y1e_Z.
    + exact Hle.
Qed.

Lemma O_odd_part : forall (G G1 At : N) r m q Lb Wp A Ap t' f1,
  (5 * m <= 2 * A <= 5 * m + 1)%nat -> (5 * q + 1 <= 2 * Ap <= 5 * q + 2)%nat ->
  (m + q + Lb <= Wp + 1)%nat -> (Wp <= m + q + Lb + 2)%nat ->
  (5 * Lb <= 2 * S t' + 9)%nat -> (2 * S t' + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat ->
  (26 <= m \/ 90 <= Wp)%nat ->
  (Lb <= f1)%nat -> (Ap + q + 2 <= f1)%nat -> (f1 <= Lb \/ f1 <= Ap + q + 2)%nat ->
  (Lb <= Ap -> ones_on G Lb Ap)%nat ->
  (f1 < Ap + (A + 1) -> ones_on G (S f1) (Ap + (A + 1)))%nat ->
  (Lb < Ap -> r <= Lb)%nat -> (Ap <= Lb -> q + 1 <= A -> r <= f1 + 1)%nat ->
  G = pw r * (2 * G1 + 1) ->
  (r + Apr r + Afun (S t') + S t' + 1 <= Ap + A + Wp + 2)%nat ->
  (forall p q0, ones_on G1 p q0 -> (q0 + S r <= Ap + A + Wp + 2)%nat -> ones_on At p q0) ->
  y1o t' r <= At -> LR (At - y1o t' r).
Proof.
  intros G G1 At r m q Lb Wp A Ap t' f1 BA BAp H1 H2 H3 H4 H5 H6 H7 H8 H9 run0 run1 R1 R2 HGr HR HA Hle.
  pose proof (Afun_bd (S t')) as BA3. pose proof (Apr_bd r) as BA2.
  destruct (arith_O_odd m q Lb Wp A Ap r (S t') (Apr r) (Afun (S t')) f1) as [[C0 C]|[[C0 C]|[[C0 C]|[C0 C]]]]; try assumption; try lia.
  - apply (LR_odd G G1 r At Lb Ap (Apr r + r + 1) (Apr r + Afun (S t')) (y1o t' r)).
    + exact HGr.
    + apply run0. lia.
    + replace (S r) with (r + 1)%nat by lia. exact C.
    + apply zone_y1o_G.
    + exact Hle.
    + intros p q0 H10 H11. apply HA; [exact H10|lia].
  - apply (LR_odd G G1 r At Lb Ap 0 (Apr r - 1) (y1o t' r)).
    + exact HGr.
    + apply run0. lia.
    + replace (S r) with (r + 1)%nat by lia. exact C.
    + apply zone_y1o_Z.
    + exact Hle.
    + intros p q0 H10 H11. apply HA; [exact H10|lia].
  - apply (LR_odd G G1 r At (f1 + 1) (Ap + A + 1) (Apr r + r + 1) (Apr r + Afun (S t')) (y1o t' r)).
    + exact HGr.
    + replace (f1 + 1)%nat with (S f1) by lia. replace (Ap + A + 1)%nat with (Ap + (A + 1))%nat by lia.
      apply run1. unfold cand in C. lia.
    + replace (S r) with (r + 1)%nat by lia. exact C.
    + apply zone_y1o_G.
    + exact Hle.
    + intros p q0 H10 H11. apply HA; [exact H10|lia].
  - apply (LR_odd G G1 r At (f1 + 1) (Ap + A + 1) 0 (Apr r - 1) (y1o t' r)).
    + exact HGr.
    + replace (f1 + 1)%nat with (S f1) by lia. replace (Ap + A + 1)%nat with (Ap + (A + 1))%nat by lia.
      apply run1. unfold cand in C. lia.
    + replace (S r) with (r + 1)%nat by lia. exact C.
    + apply zone_y1o_Z.
    + exact Hle.
    + intros p q0 H10 H11. apply HA; [exact H10|lia].
Qed.

(* The leaf with Yd = y2 *)
Lemma close_O : forall t k q K0 Q Lb Wp G t' e,
  S t = (2 * k + 1)%nat ->
  G + y2v t q + K0 = pw (Apr q + S (Afun (S t) + S Wp)) + Q -> Q < K0 -> K0 <= pw Lb ->
  (S t + q + Lb <= Wp + 1)%nat -> (Wp <= S t + q + Lb + 2)%nat ->
  (5 * Lb <= 2 * S t' + 9)%nat -> (2 * S t' + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat ->
  (26 <= S t \/ 90 <= Wp)%nat ->
  (e = true -> forall r G1, G = pw r * (2 * G1 + 1) -> (r + 9 <= Apr q + S (Afun (S t) + S Wp))%nat) ->
  Inv e (S t') (Apr q + S (Afun (S t) + S Wp)) G.
Proof.
  intros t k q K0 Q Lb Wp G t' e Hk HG HQ HK HW1 HW2 Ha1 Ha2 HLb Hm H9.
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd q) as BAp.
  replace (Apr q + S (Afun (S t) + S Wp))%nat with (Apr q + Afun (S t) + Wp + 2)%nat in * by lia.
  set (A := Afun (S t)) in *. set (Ap := Apr q) in *.
  set (Wf := (Ap + A + Wp + 2)%nat) in *.
  destruct (O_nat1 (S t) q Lb Wp A Ap (S t')) as [H26 [HLW0 H9W]]; try assumption; try lia.
  set (T := Nat.max (A + (S t + 3)) (q + 3)).
  assert (HT1 : (A + (S t + 3) <= T)%nat) by (unfold T; lia).
  assert (HT2 : (q + 3 <= T)%nat) by (unfold T; lia).
  assert (HT3 : (T <= A + (S t + 3) \/ T <= q + 3)%nat) by (unfold T; lia).
  pose proof (y2v_lt t q T HT1 HT2) as HY.
  fold Ap in HY.
  assert (HTW : (Ap + (T + 1) <= Wf - 1)%nat) by (unfold Wf; lia).
  assert (HLW : (Lb <= Wf - 2)%nat) by (unfold Wf in *; lia).
  pose proof (pw_le _ _ HTW) as HP1. pose proof (pw_le _ _ HLW) as HP2.
  assert (HW0 : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  assert (HW1' : pw (Wf - 1) = 2 * pw (Wf - 2)).
  { replace (Wf - 2)%nat with (Wf - 1 - 1)%nat by lia. apply pw_pred2. unfold Wf; lia. }
  assert (Hlow : pw (Wf - 2) <= G) by lia.
  assert (Hhigh : G < pw Wf) by lia.
  assert (HG0 : G <> 0) by (pose proof (pw_pos (Wf - 2)); lia).
  clear HW0 HW1' HP1 HP2.
  destruct (N_tz G HG0) as [r [G1 HGr]].
  (* the runs of ones *)
  assert (runI0 : (Lb <= Ap)%nat -> ones_on G Lb Ap).
  { intros Hl. apply (fresh0 G (2 * zv t q + 1) K0 Q Wf Lb Ap).
    - assert (y2v t q = (2 * zv t q + 1) * pw Ap) as Hy2 by (unfold y2v; fold Ap; lia).
      rewrite <- Hy2. exact HG.
    - lia.
    - exact HQ.
    - exact Hl.
    - unfold Wf; lia. }
  set (f1 := Nat.max Lb (Ap + q + 2)).
  assert (Hf1 : (Lb <= f1)%nat) by (unfold f1; lia).
  assert (Hf2 : (Ap + q + 2 <= f1)%nat) by (unfold f1; lia).
  assert (Hf3 : (f1 <= Lb \/ f1 <= Ap + q + 2)%nat) by (unfold f1; lia).
  assert (runI1 : (f1 < Ap + (A + 1))%nat -> ones_on G (S f1) (Ap + (A + 1))).
  { intros Hl. apply (fresh G (y2v t q) K0 Q Wf f1 (Ap + (A + 1)) (Ya (S t)) (pw Ap * (pw (q + 2) - 1))).
    - exact HG.
    - rewrite y2v_split. change (Apr q) with Ap. change (Afun (S t)) with A. lia.
    - pose proof (Yc_lt Ap q) as H1. pose proof (pw_le (Ap + (q + 2)) f1 ltac:(lia)) as H2. lia.
    - pose proof (pw_le Lb f1 Hf1). lia.
    - exact HQ.
    - exact Hl.
    - unfold Wf; lia. }
  set (f2 := Nat.max (Ap + (T + 1)) Lb).
  assert (Hg1 : (Ap + (T + 1) <= f2)%nat) by (unfold f2; lia).
  assert (Hg2 : (Lb <= f2)%nat) by (unfold f2; lia).
  assert (Hg3 : (f2 <= Ap + (T + 1) \/ f2 <= Lb)%nat) by (unfold f2; lia).
  assert (runI2 : (f2 < Wf)%nat -> ones_on G (S f2) Wf).
  { intros Hl. apply (fresh G (y2v t q) K0 Q Wf f2 Wf 0 (y2v t q)).
    - exact HG.
    - lia.
    - pose proof (pw_le _ _ Hg1). lia.
    - pose proof (pw_le _ _ Hg2). lia.
    - exact HQ.
    - exact Hl.
    - lia. }
  (* the bound on the first set bit *)
  assert (Hr1 : (Lb < Ap -> r <= Lb)%nat).
  { intros Hl. apply (ones_tz G G1 r Lb Ap HGr (runI0 ltac:(lia)) Hl). }
  assert (Hr2 : (Ap <= Lb -> (S f1 < Ap + (A + 1) /\ r <= S f1) \/ (Ap + (A + 1) <= S f1 /\ r <= S f2))%nat).
  { intros Hl. destruct (Nat.lt_ge_cases (S f1) (Ap + (A + 1))) as [H1|H1].
    - left. split; [exact H1|]. apply (ones_tz G G1 r (S f1) (Ap + (A + 1)) HGr (runI1 ltac:(lia)) H1).
    - right. split; [lia|].
      assert (S (S f2) <= Wf)%nat as H2.
      { clear -BA BAp HW1 HW2 HLb Hg3 HT3 HLW. unfold Wf in *. lia. }
      apply (ones_tz G G1 r (S f2) Wf HGr (runI2 ltac:(lia)) ltac:(lia)). }
  destruct (O_r_bound (S t) q Lb Wp A Ap (S t') r T f1 f2) as [Hb1 Hb2]; try assumption; try lia.
  split; [exact H26|]. split; [unfold Wf; lia|]. split; [exact Hlow|]. split; [exact Hhigh|].
  exists r, G1. split; [exact HGr|]. split; [exact Hb2|]. split.
  { intros He. apply (H9 He r G1 HGr). }
  split; [exact Hb1|].
  intros t2 Ht2. assert (t2 = t') by lia. subst t2. clear Ht2.
  assert (Hr3 : (Ap <= Lb -> q + 1 <= A -> r <= f1 + 1 \/ Ap + (A + 1) <= S f1)%nat).
  { intros H1 H2. destruct (Hr2 H1) as [[H3 H4]|[H3 H4]]; lia. }
  split; [|split].
  - (* a' even *)
    intros _ He Hle.
    apply (O_even_part G (S t) q Lb Wp A Ap t' f1); assumption.
  - (* a' odd, e = false *)
    intros _ He Hle.
    pose proof (y1o_lo t' r) as Hl.
    assert (Hx : pw (Apr r + Afun (S t') + (S t' + 1)) <= G1) by lia.
    pose proof (G1_bound G G1 r Wf _ HGr Hhigh Hx) as HR.
    clear Hl Hx.
    apply (O_odd_part G G1 G1 r (S t) q Lb Wp A Ap t' f1); try assumption.
    + intros H1 H2. destruct (Hr3 H1 H2) as [H3|H3]; [exact H3|].
      exfalso. pose proof (Afun_bd (S t')). pose proof (Apr_bd r). clear -H1 H2 H3 HR BA BAp HW1 HW2 Ha1 Ha2 HLb Hf3 Hf2 Hf1 H H0. unfold Wf in *. lia.
    + unfold Wf in *. lia.
    + intros p q0 H1 _. exact H1.
  - (* a' odd, e = true *)
    intros _ He Hodd Hle.
    pose proof (y1o_lo t' r) as Hl.
    assert (Hx : pw (Apr r + Afun (S t') + (S t' + 1)) <= G1 + pw (Wf - r)) by lia.
    pose proof (G1_bound2 G G1 r Wf _ HGr Hhigh Hx) as HR.
    clear Hl Hx.
    apply (O_odd_part G G1 (G1 + pw (Wf - r)) r (S t) q Lb Wp A Ap t' f1); try assumption.
    + intros H1 H2. destruct (Hr3 H1 H2) as [H3|H3]; [exact H3|].
      exfalso. pose proof (Afun_bd (S t')). pose proof (Apr_bd r). clear -H1 H2 H3 HR BA BAp HW1 HW2 Ha1 Ha2 HLb Hf3 Hf2 Hf1 H H0. unfold Wf in *. lia.
    + unfold Wf in *. lia.
    + intros p q0 H1 H2. apply ones_high; [exact H1|]. fold Wf in H2. lia.
Qed.

End Part_Close3.
Import Part_Close3.

Module Part_Close4.

Local Open Scope N_scope.

(* The leaf with Yd = y: G' is odd *)
Lemma close_E : forall t k K0 Q Lb Wp G G1 t' e,
  S t = (2 * k)%nat ->
  G + yv t + K0 = pw (Afun (S t) + S Wp) + Q -> Q < K0 -> K0 <= pw Lb -> G = 2 * G1 + 1 ->
  (S t + Lb <= Wp + 2)%nat -> (Wp <= S t + Lb + 1)%nat ->
  (5 * Lb <= 2 * S t' + 9)%nat -> (2 * S t' + 3 <= 5 * Lb)%nat -> (12 <= Lb)%nat ->
  Inv e (S t') (Afun (S t) + S Wp) G.
Proof.
  intros t k K0 Q Lb Wp G G1 t' e Hk HG HQ HK HG1 HW1 HW2 Ha1 Ha2 HLb.
  pose proof (Afun_bd (S t)) as BA.
  replace (Afun (S t) + S Wp)%nat with (Afun (S t) + Wp + 1)%nat in * by lia.
  set (A := Afun (S t)) in *.
  set (Wf := (A + Wp + 1)%nat) in *.
  pose proof (yv_lt t (A + (S t + 2))%nat ltac:(unfold A; lia)) as HY.
  assert (HTW : (A + (S t + 2) <= Wf - 1)%nat) by (unfold Wf; lia).
  assert (HLW : (Lb <= Wf - 2)%nat) by (unfold Wf; lia).
  pose proof (pw_le _ _ HTW) as HP1. pose proof (pw_le _ _ HLW) as HP2.
  assert (HW0 : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  assert (HW1' : pw (Wf - 1) = 2 * pw (Wf - 2)).
  { replace (Wf - 2)%nat with (Wf - 1 - 1)%nat by lia. apply pw_pred2. unfold Wf; lia. }
  assert (Hlow : pw (Wf - 2) <= G) by lia.
  assert (Hhigh : G < pw Wf) by lia.
  clear HW0 HW1' HP1 HP2 HY.
  assert (run0 : (Lb <= A)%nat -> ones_on G Lb A).
  { intros Hl. apply (fresh0 G (Ya (S t)) K0 Q Wf Lb A).
    - assert (yv t = Ya (S t) * pw A) as Hy2 by (rewrite yv_Ya; fold A; lia).
      rewrite <- Hy2. exact HG.
    - lia.
    - exact HQ.
    - exact Hl.
    - unfold Wf; lia. }
  assert (HGr : G = pw 0 * (2 * G1 + 1)) by (rewrite pw_0; lia).
  split; [lia|]. split; [unfold Wf; lia|]. split; [exact Hlow|]. split; [exact Hhigh|].
  exists 0%nat, G1. split; [exact HGr|]. split; [unfold Wf; lia|]. split.
  { intros _. unfold Wf; lia. }
  split; [lia|].
  intros t2 Ht2. assert (t2 = t') by lia. subst t2. clear Ht2.
  pose proof (Afun_bd (S t')) as BA3.
  split; [|split].
  - intros _ He Hle.
    pose proof (y1e_lo t') as Hl.
    assert (HR : pw (Afun (S t') - 1 + (S t' + 1)) < pw Wf) by lia.
    pose proof (pw_lt_inv _ _ HR) as HR2.
    clear HR Hl.
    assert (C : cand Lb A 0 (Afun (S t') - 1) 0).
    { apply (arith_E_even (S t) Lb Wp A (S t') (Afun (S t'))); try assumption. unfold Wf in HR2. lia. }
    apply (LR_even G Lb A 0 (Afun (S t') - 1) (y1e t')).
    + apply run0. unfold cand in C. lia.
    + exact C.
    + apply zone_y1e_Z.
    + exact Hle.
  - intros _ He Hle.
    pose proof (y1o_lo t' 0) as Hl.
    assert (Hx : pw (Apr 0 + Afun (S t') + (S t' + 1)) <= G1) by lia.
    pose proof (G1_bound G G1 0 Wf _ HGr Hhigh Hx) as HR.
    clear Hl Hx.
    change (Apr 0) with 1%nat in HR.
    assert (C : cand Lb A 2 (1 + Afun (S t')) 1).
    { apply (arith_E_odd (S t) Lb Wp A (S t') (Afun (S t'))); try assumption. unfold Wf in HR. lia. }
    apply (LR_odd G G1 0 G1 Lb A 2 (1 + Afun (S t')) (y1o t' 0)).
    + exact HGr.
    + apply run0. unfold cand in C. lia.
    + exact C.
    + exact (zone_y1o_G t' 0).
    + exact Hle.
    + intros p q0 H1 _. exact H1.
  - intros _ _ Hodd. discriminate.
Qed.

(* After a tail with the right counter wide: G' = 2 VR *)
Lemma close_TS : forall u Vl t' e, Vl <> 0 -> Vl < pw u -> S t' = Apr (S u) -> (10 <= u)%nat ->
  (e = true -> forall r G1, pw u + Vl = pw r * (2 * G1 + 1) -> (r + 7 <= u)%nat) ->
  Inv e (S t') (S (S (S u))) (2 * (pw u + Vl)).
Proof.
  intros u Vl t' e H0 H1 Ht HU H7.
  pose proof (Apr_bd (S u)) as BA. rewrite <- Ht in BA.
  pose proof (pw_S u) as P1. pose proof (pw_S (S u)) as P2. pose proof (pw_S (S (S u))) as P3.
  assert (HV0 : pw u + Vl <> 0) by (pose proof (pw_pos u); lia).
  destruct (N_tz _ HV0) as [r [G1 HV]].
  assert (Hru : (r < u)%nat).
  { destruct (Nat.lt_ge_cases r u) as [H|H]; [exact H|exfalso].
    pose proof (pw_split u r H) as H2.
    assert (HE : 1 * pw u + Vl = (pw (r - u) * (2 * G1 + 1)) * pw u + 0).
    { replace (1 * pw u) with (pw u) by lia. rewrite HV, H2. lia. }
    destruct (mod_uniq (pw u) 1 _ Vl 0 H1 ltac:(pose proof (pw_pos u); lia) HE) as [_ E]. lia. }
  assert (HGr : 2 * (pw u + Vl) = pw (S r) * (2 * G1 + 1)) by (rewrite HV, pw_S; lia).
  split; [lia|]. split; [lia|]. split.
  { replace (S (S (S u)) - 2)%nat with (S u) by lia. lia. }
  split; [lia|].
  exists (S r), G1. split; [exact HGr|]. split; [lia|]. split.
  { intros He. pose proof (H7 He r G1 HV). lia. }
  split; [lia|].
  intros t2 Ht2. assert (t2 = t') by lia. subst t2. clear Ht2.
  pose proof (Afun_bd (S t')) as BA3.
  assert (Hhigh : 2 * (pw u + Vl) < pw (S (S (S u)))) by lia.
  split; [|split].
  - intros _ He Hle. exfalso.
    pose proof (y1e_lo t') as Hl.
    assert (HR : pw (Afun (S t') - 1 + (S t' + 1)) < pw (S (S (S u)))) by lia.
    pose proof (pw_lt_inv _ _ HR). lia.
  - intros _ He Hle. exfalso.
    pose proof (y1o_lo t' (S r)) as Hl.
    assert (Hx : pw (Apr (S r) + Afun (S t') + (S t' + 1)) <= G1) by lia.
    pose proof (G1_bound _ G1 (S r) _ _ HGr Hhigh Hx). lia.
  - intros _ He Hodd Hle. exfalso.
    pose proof (y1o_lo t' (S r)) as Hl.
    assert (Hx : pw (Apr (S r) + Afun (S t') + (S t' + 1)) <= G1 + pw (S (S (S u)) - S r)) by lia.
    pose proof (G1_bound2 _ G1 (S r) _ _ HGr Hhigh Hx). lia.
Qed.

(* The top run of G', for the first set bit *)
Lemma run_top : forall t q K0 Q Lb Wf G f,
  G + y2v t q + K0 = pw Wf + Q -> Q < K0 -> K0 <= pw Lb ->
  (Apr q + (Afun (S t) + (S t + 3) + 1) <= f)%nat -> (Apr q + (q + 3 + 1) <= f)%nat -> (Lb <= f)%nat -> (f < Wf)%nat ->
  ones_on G (S f) Wf.
Proof.
  intros t q K0 Q Lb Wf G f HG HQ HK H1 H2 H3 H4.
  set (T := Nat.max (Afun (S t) + (S t + 3)) (q + 3)).
  assert (HT1 : (Afun (S t) + (S t + 3) <= T)%nat) by (unfold T; lia).
  assert (HT2 : (q + 3 <= T)%nat) by (unfold T; lia).
  assert (HT3 : (Apr q + (T + 1) <= f)%nat) by (unfold T; lia).
  pose proof (y2v_lt t q T HT1 HT2) as HY.
  apply (fresh G (y2v t q) K0 Q Wf f Wf 0 (y2v t q)).
  - exact HG.
  - lia.
  - pose proof (pw_le _ _ HT3). lia.
  - pose proof (pw_le _ _ H3). lia.
  - exact HQ.
  - exact H4.
  - lia.
Qed.

End Part_Close4.
Import Part_Close4.

Module Part_Close5.

Local Open Scope N_scope.

Definition Good (c : Q * tape) : Prop :=
  exists e a h G, c -->+ FC e a h (pw h - 1 - G) /\ Inv e a h G.

Lemma Apr_S : forall n, (n <> 0)%nat \/ True -> S (Apr n - 1) = Apr n.
Proof. intros n _. pose proof (Apr_pos n). lia. Qed.

Lemma Afun_S : forall n, (1 <= n)%nat -> S (Afun n - 1) = Afun n.
Proof. intros n H. pose proof (Afun_bd n). lia. Qed.

(* Leaf B.E1 *)
Lemma good_BE1 : forall t k c C W,
  S t = (2 * k)%nat -> C <> 0 -> C < pw c -> (9 <= c)%nat ->
  (S t + c + 1 <= W)%nat -> (W <= S t + c + 2)%nat ->
  Good (D1 (S t) (TL (bin c C) (U B0)) W).
Proof.
  intros t k c C W Hk H0 HC Hc HW1 HW2.
  set (Wf := (Afun (S t) + S W)%nat).
  pose proof (Afun_bd (S t)) as BA.
  pose proof (yv_lt t (Afun (S t) + (S t + 2))%nat ltac:(lia)) as HY.
  pose proof (pw_le (Afun (S t) + (S t + 2)) (Wf - 1) ltac:(unfold Wf; lia)) as H1.
  pose proof (pw_le (c + 3) (Wf - 1) ltac:(unfold Wf; lia)) as H2.
  assert (HW : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  assert (Hc3 : pw (c + 3) = 8 * pw c) by (rewrite pw_add; change (pw 3) with 8; lia).
  pose proof (pw_S c) as HS.
  pose proof (pw_pos c) as Hp.
  set (x' := yv t + 1 + 2 * (pw c - (C + 1))) in *.
  set (xf := x' + 2 * pw (S c) - 1) in *.
  assert (Hx1 : x' < pw Wf) by (unfold x'; lia).
  assert (Hx2 : xf < pw Wf) by (unfold xf, x'; lia).
  set (G := pw Wf - 1 - xf).
  assert (HGe : G + yv t + 6 * pw c = pw Wf + (2 * C + 1)) by (unfold G, xf, x'; lia).
  pose proof (yv_y1e t) as Hye.
  destruct (N_parity G) as [[w Hw]|[w Hw]].
  { exfalso. lia. }
  exists (Nat.odd (S c)), (Apr (S c)), Wf, G. split.
  - replace (pw Wf - 1 - G) with xf by (unfold G; lia).
    eapply progress_trans.
    + apply (b_E1 t k c C W Hk ltac:(lia) H0 HC Hx1).
    + apply d3_fin. exact Hx2.
  - pose proof (Apr_bd (S c)) as BA2.
    rewrite <- (Apr_S (S c) (or_intror I)).
    unfold Wf. apply (close_E t k (6 * pw c) (2 * C + 1) (c + 3) W G w).
    + exact Hk.
    + exact HGe.
    + lia.
    + lia.
    + exact Hw.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

(* Leaf D.E1 *)
Lemma good_DE1 : forall t k r c1 C1 W,
  S t = (2 * k)%nat -> pw r * (2 * C1 + 1) + 1 < pw (r + S c1) -> (11 <= r + S c1)%nat ->
  (W = S t + (r + S c1) + 1)%nat ->
  Good (D1 (S t) (TL (bin (r + S c1) (pw r * (2 * C1 + 1))) (D3 B0)) W).
Proof.
  intros t k r c1 C1 W Hk HC Hc HW.
  set (c := (r + S c1)%nat) in *.
  set (C := pw r * (2 * C1 + 1)) in *.
  set (Wf := (Afun (S t) + S W)%nat).
  pose proof (Afun_bd (S t)) as BA.
  pose proof (yv_lt t (Afun (S t) + (S t + 2))%nat ltac:(lia)) as HY.
  pose proof (pw_le (Afun (S t) + (S t + 2)) (Wf - 1) ltac:(unfold Wf; lia)) as H1.
  pose proof (pw_le (c + 1) (Wf - 1) ltac:(unfold Wf; lia)) as H2.
  assert (HW2 : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  assert (Hc1 : pw (c + 1) = 2 * pw c) by (rewrite pw_add; change (pw 1) with 2; lia).
  set (xf := yv t + 1 + 2 * (pw c - 1 - (C + 1)) + 1) in *.
  assert (Hx : xf < pw Wf) by (unfold xf; lia).
  set (G := pw Wf - 1 - xf).
  assert (HGe : G + yv t + 2 * pw c = pw Wf + (2 * C + 1)) by (unfold G, xf; lia).
  pose proof (yv_y1e t) as Hye.
  destruct (N_parity G) as [[w Hw]|[w Hw]].
  { exfalso. lia. }
  exists (Nat.even c), (Afun c), Wf, G. split.
  - replace (pw Wf - 1 - G) with xf by (unfold G; lia).
    apply (d3_E1 t k r c1 C1 W Hk ltac:(lia) HC Hx).
  - pose proof (Afun_bd c) as BA2.
    rewrite <- (Afun_S c ltac:(lia)).
    unfold Wf. apply (close_E t k (2 * pw c) (2 * C + 1) (c + 1) W G w).
    + exact Hk.
    + exact HGe.
    + lia.
    + lia.
    + exact Hw.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

(* Leaf T.S *)
Lemma good_TS : forall u Vl, Vl <> 0 -> Vl + 1 <= pw u -> (10 <= u)%nat ->
  (Nat.odd (S u) = true -> forall r G1, pw u + Vl = pw r * (2 * G1 + 1) -> (r + 7 <= u)%nat) ->
  Good (AC (TL (bin u Vl) (U B0)) (oL (S (S u)))).
Proof.
  intros u Vl H0 H1 Hu H7.
  pose proof (pw_S u) as P1. pose proof (pw_S (S u)) as P2. pose proof (pw_S (S (S u))) as P3.
  exists (Nat.odd (S u)), (Apr (S u)), (S (S (S u))), (2 * (pw u + Vl)). split.
  - replace (pw (S (S (S u))) - 1 - 2 * (pw u + Vl)) with (2 * pw u - 2 * Vl + 2 * pw (S u) - 1) by lia.
    destruct (N.lt_ge_cases (Vl + 1) (pw u)) as [Hl|Hl].
    + apply tailS_fin; assumption.
    + apply tailS_top; lia.
  - rewrite <- (Apr_S (S u) (or_intror I)).
    apply close_TS.
    + exact H0.
    + lia.
    + apply Apr_S. right. exact I.
    + exact Hu.
    + exact H7.
Qed.

End Part_Close5.
Import Part_Close5.

Module Part_Close6.

Local Open Scope N_scope.

(* The condition e=1 => r+9<=h after a leaf with odd m *)
Lemma h9_run : forall t q K0 Q Lb Wf G r G1,
  G + y2v t q + K0 = pw Wf + Q -> Q < K0 -> K0 <= pw Lb ->
  (Apr q + (Afun (S t) + (S t + 3) + 1) + 10 <= Wf)%nat -> (Apr q + (q + 3 + 1) + 10 <= Wf)%nat -> (Lb + 10 <= Wf)%nat ->
  G = pw r * (2 * G1 + 1) -> (r + 9 <= Wf)%nat.
Proof.
  intros t q K0 Q Lb Wf G r G1 HG HQ HK H1 H2 H3 Hr.
  pose proof (run_top t q K0 Q Lb Wf G (Wf - 10) HG HQ HK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
  pose proof (ones_tz G G1 r _ _ Hr R ltac:(lia)) as E. lia.
Qed.

Lemma h9_gen : forall t k q K0 Q Lb L W G r G1, S t = (2 * k + 1)%nat ->
  G + y2v t q + K0 = pw (Apr q + S (Afun (S t) + S W)) + Q -> Q < K0 -> K0 <= pw Lb ->
  (S t + q + L + 2 <= W)%nat -> (10 <= L)%nat -> (Lb <= L + 3)%nat -> (t <> 0%nat \/ 2 <= q)%nat ->
  G = pw r * (2 * G1 + 1) -> (r + 9 <= Apr q + S (Afun (S t) + S W))%nat.
Proof.
  intros t k q K0 Q Lb L W G r G1 Hk HG HQ HK H1 H2 H3 H4 Hr.
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd q) as BP.
  apply (h9_run t q K0 Q Lb _ G r G1 HG HQ HK); try lia.
Qed.

Lemma y2v00 : y2v 0 0 = 166.
Proof. vm_compute. reflexivity. Qed.

Lemma h9_zero : forall K0 Q W G, G + y2v 0 0 + K0 = pw (Apr 0 + S (Afun 1 + S W)) + Q ->
  G + 166 + K0 = pw (W + 6) + Q.
Proof.
  intros K0 Q W G H. rewrite y2v00 in H. change (Apr 0) with 1%nat in H. change (Afun 1) with 3%nat in H.
  replace (1 + S (3 + S W))%nat with (W + 6)%nat in H by lia. exact H.
Qed.

Lemma mult_split : forall r L G1, (L <= r)%nat -> exists Z, pw r * (2 * G1 + 1) = Z * pw L.
Proof.
  intros r L G1 H. exists (pw (r - L) * (2 * G1 + 1)). rewrite (pw_split L r H). lia.
Qed.

Lemma h9_core : forall P Z C1 B, 512 <= P -> C1 < P -> C1 <> 83 ->
  Z * (2 * P) + 166 = B * (2 * P) + 2 * C1 -> False.
Proof.
  intros P Z C1 B HP H1 H2 E.
  destruct (N.lt_ge_cases C1 83) as [H|H].
  - assert (E2 : Z * (2 * P) + (166 - 2 * C1) = B * (2 * P) + 0) by lia.
    destruct (mod_uniq (2 * P) Z B (166 - 2 * C1) 0 ltac:(lia) ltac:(lia) E2) as [_ E3]. lia.
  - assert (E2 : Z * (2 * P) + 0 = B * (2 * P) + (2 * C1 - 166)) by lia.
    destruct (mod_uniq (2 * P) Z B 0 (2 * C1 - 166) ltac:(lia) ltac:(lia) E2) as [_ E3]. lia.
Qed.

Lemma pw_9 : forall L, pw (L + 9) = 512 * pw L.
Proof. intros L. rewrite pw_add. change (pw 9) with 512. lia. Qed.

Lemma pw_10 : forall L, pw (L + 10) = 1024 * pw L.
Proof. intros L. rewrite pw_add. change (pw 10) with 1024. lia. Qed.

Lemma h9_s1 : forall L C1 G r G1, (9 <= L)%nat -> C1 < pw L -> C1 <> 83 ->
  (G + 166 + 6 * pw L = pw (L + 9) + 2 * C1 \/ G + 166 + 2 * pw L = pw (L + 9) + 2 * C1) ->
  G = pw r * (2 * G1 + 1) -> (r + 9 <= L + 9)%nat.
Proof.
  intros L C1 G r G1 HL H1 H2 HE Hr.
  destruct (Nat.le_gt_cases r L) as [H|H]; [lia|exfalso].
  destruct (mult_split r (S L) G1 ltac:(lia)) as [Z HZ].
  rewrite pw_S in HZ. rewrite pw_9 in HE. rewrite HZ in Hr. subst G.
  pose proof (pw_le 9 L HL) as P. change (pw 9) with 512 in P.
  destruct HE as [HE|HE].
  - apply (h9_core (pw L) Z C1 253); lia.
  - apply (h9_core (pw L) Z C1 255); lia.
Qed.

Lemma h9_s2 : forall L C1 G r G1, (9 <= L)%nat -> C1 < pw L ->
  G + 166 + 6 * pw L = pw (L + 10) + 2 * C1 ->
  G = pw r * (2 * G1 + 1) -> (r + 9 <= L + 10)%nat.
Proof.
  intros L C1 G r G1 HL H1 HE Hr.
  destruct (Nat.le_gt_cases r (S L)) as [H|H]; [lia|exfalso].
  destruct (mult_split r (S (S L)) G1 ltac:(lia)) as [Z HZ].
  rewrite !pw_S in HZ. rewrite pw_10 in HE. rewrite HZ in Hr. subst G.
  pose proof (pw_le 9 L HL) as P. change (pw 9) with 512 in P.
  assert (E2 : Z * (2 * (2 * pw L)) + 0 = 254 * (2 * (2 * pw L)) + (2 * pw L + 2 * C1 - 166)) by lia.
  destruct (mod_uniq (2 * (2 * pw L)) Z 254 0 (2 * pw L + 2 * C1 - 166) ltac:(lia) ltac:(lia) E2) as [_ E3]. lia.
Qed.

Lemma odd_ge10 : forall L, (9 <= L)%nat -> Nat.odd (S L) = true -> (10 <= L)%nat.
Proof.
  intros L H1 H2. destruct (Nat.eq_dec L 9) as [E|E]; [|lia].
  subst L. vm_compute in H2. discriminate.
Qed.

Lemma h9_BO0 : forall t k j L C1 W G, S t = (2 * k + 1)%nat -> (9 <= L)%nat -> C1 < pw L ->
  (S t + (2 * j + S L) + 1 <= W)%nat -> (W <= S t + (2 * j + S L) + 2)%nat ->
  (t = 0%nat -> j = 0%nat -> W = (S t + (2 * j + S L) + 1)%nat -> C1 <> 83) ->
  G + y2v t (2 * j) + 6 * pw L = pw (Apr (2 * j) + S (Afun (S t) + S W)) + 2 * C1 ->
  Nat.odd (S L) = true -> forall r G1, G = pw r * (2 * G1 + 1) ->
  (r + 9 <= Apr (2 * j) + S (Afun (S t) + S W))%nat.
Proof.
  intros t k j L C1 W G Hk HL HC HW1 HW2 H83 HG Ho r G1 Hr.
  pose proof (odd_ge10 L HL Ho) as H10.
  destruct (Nat.eq_dec t 0) as [Et|Et]; [destruct (Nat.eq_dec j 0) as [Ej|Ej]|].
  - subst t j. change (2 * 0)%nat with 0%nat in *.
    apply h9_zero in HG. change (Apr 0) with 1%nat. change (Afun 1) with 3%nat.
    assert (W = (L + 3)%nat \/ W = (L + 4)%nat) as [E|E] by lia.
    + subst W. replace (L + 3 + 6)%nat with (L + 9)%nat in HG by lia.
      pose proof (h9_s1 L C1 G r G1 HL HC (H83 eq_refl eq_refl ltac:(lia)) (or_introl HG) Hr). lia.
    + subst W. replace (L + 4 + 6)%nat with (L + 10)%nat in HG by lia.
      pose proof (h9_s2 L C1 G r G1 HL HC HG Hr). lia.
  - apply (h9_gen t k (2 * j) (6 * pw L) (2 * C1) (L + 3) L W G r G1 Hk HG); try lia.
    + rewrite pw_add. change (pw 3) with 8. lia.
  - apply (h9_gen t k (2 * j) (6 * pw L) (2 * C1) (L + 3) L W G r G1 Hk HG); try lia.
    + rewrite pw_add. change (pw 3) with 8. lia.
Qed.

Lemma h9_DO0 : forall t k j L C1 W G, S t = (2 * k + 1)%nat -> (11 <= L)%nat -> pw (L - 1) <= C1 -> C1 < pw L ->
  W = (S t + (2 * j + S L) + 1)%nat ->
  G + y2v t (2 * j) + 2 * pw L = pw (Apr (2 * j) + S (Afun (S t) + S W)) + 2 * C1 ->
  forall r G1, G = pw r * (2 * G1 + 1) ->
  (r + 9 <= Apr (2 * j) + S (Afun (S t) + S W))%nat.
Proof.
  intros t k j L C1 W G Hk HL HC1 HC HW HG r G1 Hr.
  destruct (Nat.eq_dec t 0) as [Et|Et]; [destruct (Nat.eq_dec j 0) as [Ej|Ej]|].
  - subst t j. change (2 * 0)%nat with 0%nat in *.
    apply h9_zero in HG. change (Apr 0) with 1%nat. change (Afun 1) with 3%nat.
    assert (E : W = (L + 3)%nat) by lia. clear HW. subst W.
    replace (L + 3 + 6)%nat with (L + 9)%nat in HG by lia.
    pose proof (pw_le 10 (L - 1) ltac:(lia)) as P. change (pw 10) with 1024 in P.
    pose proof (h9_s1 L C1 G r G1 ltac:(lia) HC ltac:(lia) (or_intror HG) Hr). lia.
  - pose proof (pw_S (L)) as PS.
    pose proof (pw_le (S L) (L + 3) ltac:(lia)).
    apply (h9_gen t k (2 * j) (2 * pw L) (2 * C1) (L + 3) L W G r G1 Hk HG); try lia.
  - pose proof (pw_S (L)) as PS.
    pose proof (pw_le (S L) (L + 3) ltac:(lia)).
    apply (h9_gen t k (2 * j) (2 * pw L) (2 * C1) (L + 3) L W G r G1 Hk HG); try lia.
Qed.

Lemma zv_lt2 : forall t q W, (S t + 2 <= W)%nat -> (q + 1 <= W)%nat -> zv t q < pw (Afun (S t) + S W).
Proof.
  intros t q W H1 H2. unfold zv.
  pose proof (yv_lt t (Afun (S t) + (S t + 2))%nat ltac:(lia)) as HY.
  pose proof (pw_le (Afun (S t) + (S t + 2)) (Afun (S t) + W) ltac:(lia)) as P1.
  pose proof (pw_le (S q) (Afun (S t) + W) ltac:(lia)) as P2.
  pose proof (pw_S q) as P3. pose proof (pw_pos q) as P4.
  replace (Afun (S t) + S W)%nat with (S (Afun (S t) + W)) by lia.
  rewrite pw_S. lia.
Qed.

Lemma y2v_lt2 : forall t q W, (S t + 3 <= W)%nat -> (q + 3 <= Afun (S t) + W)%nat ->
  y2v t q < pw (Apr q + S (Afun (S t) + S W) - 1).
Proof.
  intros t q W H1 H2.
  replace (Apr q + S (Afun (S t) + S W) - 1)%nat with (Apr q + (Afun (S t) + W + 1))%nat by lia.
  apply y2v_lt; lia.
Qed.

End Part_Close6.
Import Part_Close6.

Module Part_Close7.

Local Open Scope N_scope.

(* Leaf B.O0 *)
Lemma good_BO0 : forall t k j r2 c2 C2 W,
  S t = (2 * k + 1)%nat -> pw r2 * (2 * C2 + 1) < pw (r2 + S c2) -> (9 <= r2 + S c2)%nat ->
  (S t + (2 * j + S (r2 + S c2)) + 1 <= W)%nat -> (W <= S t + (2 * j + S (r2 + S c2)) + 2)%nat ->
  (26 <= S t \/ 90 <= W)%nat ->
  (t = 0%nat -> j = 0%nat -> W = (S t + (2 * j + S (r2 + S c2)) + 1)%nat -> pw r2 * (2 * C2 + 1) <> 83) ->
  Good (D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (U B0)) W).
Proof.
  intros t k j r2 c2 C2 W Hk HC HL HW1 HW2 Hbig H83.
  set (L := (r2 + S c2)%nat) in *.
  set (C1 := pw r2 * (2 * C2 + 1)) in *.
  set (Wf := (Apr (2 * j) + S (Afun (S t) + S W))%nat).
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd (2 * j)) as BP.
  pose proof (y2v_lt2 t (2 * j) W ltac:(lia) ltac:(lia)) as HY. fold Wf in HY.
  pose proof (zv_lt2 t (2 * j) W ltac:(lia) ltac:(lia)) as HZ.
  assert (HW : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  pose proof (pw_le (L + 3) (Wf - 1) ltac:(unfold Wf; lia)) as H2.
  assert (Hc3 : pw (L + 3) = 8 * pw L) by (rewrite pw_add; change (pw 3) with 8; lia).
  pose proof (pw_S L) as HS.
  pose proof (pw_pos L) as Hp.
  set (x' := y2v t (2 * j) + 2 * (pw L - C1)) in *.
  set (xf := x' + 2 * pw (S L) - 1) in *.
  assert (Hx1 : x' < pw Wf) by (unfold x'; lia).
  assert (Hx2 : xf < pw Wf) by (unfold xf, x'; lia).
  set (G := pw Wf - 1 - xf).
  assert (HGe : G + y2v t (2 * j) + 6 * pw L = pw Wf + 2 * C1) by (unfold G, xf, x'; lia).
  exists (Nat.odd (S L)), (Apr (S L)), Wf, G. split.
  - replace (pw Wf - 1 - G) with xf by (unfold G; lia).
    eapply progress_trans.
    + apply (b_O0 t k j r2 c2 C2 W Hk ltac:(lia) HZ HC Hx1).
    + apply d3_fin. exact Hx2.
  - pose proof (Apr_bd (S L)) as BA2.
    rewrite <- (Apr_S (S L) (or_intror I)).
    unfold Wf. apply (close_O t k (2 * j) (6 * pw L) (2 * C1) (L + 3) W G).
    + exact Hk.
    + exact HGe.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Hbig.
    + intros He r G1 Hr. exact (h9_BO0 t k j L C1 W G Hk HL HC HW1 HW2 H83 HGe He r G1 Hr).
Qed.

(* Leaf D.O0 *)
Lemma good_DO0 : forall t k j r2 c2 C2 W,
  S t = (2 * k + 1)%nat -> pw (r2 + S c2 - 1) <= pw r2 * (2 * C2 + 1) -> pw r2 * (2 * C2 + 1) < pw (r2 + S c2) ->
  (11 <= r2 + S c2)%nat ->
  W = (S t + (2 * j + S (r2 + S c2)) + 1)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  Good (D1 (S t) (TL (bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (D3 B0)) W).
Proof.
  intros t k j r2 c2 C2 W Hk HC1 HC HL HW1 Hbig.
  set (L := (r2 + S c2)%nat) in *.
  set (C1 := pw r2 * (2 * C2 + 1)) in *.
  set (Wf := (Apr (2 * j) + S (Afun (S t) + S W))%nat).
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd (2 * j)) as BP.
  pose proof (y2v_lt2 t (2 * j) W ltac:(lia) ltac:(lia)) as HY. fold Wf in HY.
  pose proof (zv_lt2 t (2 * j) W ltac:(lia) ltac:(lia)) as HZ.
  assert (HW : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  pose proof (pw_le (S L) (Wf - 1) ltac:(unfold Wf; lia)) as H2.
  pose proof (pw_S L) as HS.
  set (xf := y2v t (2 * j) + 2 * (pw L - 1 - C1) + 1) in *.
  assert (Hx : xf < pw Wf) by (unfold xf; lia).
  set (G := pw Wf - 1 - xf).
  assert (HGe : G + y2v t (2 * j) + 2 * pw L = pw Wf + 2 * C1) by (unfold G, xf; lia).
  exists (Nat.even L), (Afun L), Wf, G. split.
  - replace (pw Wf - 1 - G) with xf by (unfold G; lia).
    apply (d3_O0 t k j r2 c2 C2 W Hk ltac:(lia) HZ HC Hx).
  - pose proof (Afun_bd L) as BA2.
    rewrite <- (Afun_S L ltac:(lia)).
    unfold Wf. apply (close_O t k (2 * j) (2 * pw L) (2 * C1) (S L) W G).
    + exact Hk.
    + exact HGe.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Hbig.
    + intros _ r G1 Hr. exact (h9_DO0 t k j L C1 W G Hk HL HC1 HC HW1 HGe r G1 Hr).
Qed.

Lemma odd_r0 : forall G r G1 a b, G + 2 * a = 2 * b + 1 -> G = pw r * (2 * G1 + 1) -> r = 0%nat.
Proof.
  intros G r G1 a b H1 H2. destruct r as [|r]; [reflexivity|exfalso].
  rewrite pw_S in H2. lia.
Qed.

(* Leaf D.O1 *)
Lemma good_DO1 : forall t k j c1 C1 W,
  S t = (2 * k + 1)%nat -> pw (c1 - 1) <= C1 -> C1 + 1 < pw c1 -> (11 <= c1)%nat ->
  W = (S t + (2 * j + 1 + S c1) + 1)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  Good (D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) (D3 B0)) W).
Proof.
  intros t k j L C1 W Hk HC1 HC HL HW1 Hbig.
  set (Wf := (Apr (2 * j + 1) + S (Afun (S t) + S W))%nat).
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd (2 * j + 1)) as BP.
  pose proof (y2v_lt2 t (2 * j + 1) W ltac:(lia) ltac:(lia)) as HY. fold Wf in HY.
  pose proof (zv_lt2 t (2 * j + 1) W ltac:(lia) ltac:(lia)) as HZ.
  assert (HW : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; unfold Wf; lia).
  pose proof (pw_le (S L) (Wf - 1) ltac:(unfold Wf; lia)) as H2.
  pose proof (pw_S L) as HS.
  set (xf := y2v t (2 * j + 1) + 1 + 2 * (pw L - 1 - (C1 + 1)) + 1) in *.
  assert (Hx : xf < pw Wf) by (unfold xf; lia).
  set (G := pw Wf - 1 - xf).
  assert (HGe : G + y2v t (2 * j + 1) + 2 * pw L = pw Wf + (2 * C1 + 1)) by (unfold G, xf; lia).
  exists (Nat.odd L), (Apr L), Wf, G. split.
  - replace (pw Wf - 1 - G) with xf by (unfold G; lia).
    apply (d3_O1 t k j L C1 W Hk ltac:(lia) HZ HC Hx).
  - pose proof (Apr_bd L) as BA2.
    rewrite <- (Apr_S L (or_intror I)).
    unfold Wf. apply (close_O t k (2 * j + 1) (2 * pw L) (2 * C1 + 1) (S L) W G).
    + exact Hk.
    + exact HGe.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Hbig.
    + intros _ r G1 Hr.
      pose proof (y2v_y1o t (2 * j + 1)) as Hy.
      assert (r = 0%nat) as E.
      { apply (odd_r0 G r G1 (y1o t (2 * j + 1) + pw L) (pw (Wf - 1) + C1)); lia. }
      lia.
Qed.

End Part_Close7.
Import Part_Close7.

Module Part_Close8.

Local Open Scope N_scope.

Lemma good_back : forall c c', c -->+ c' -> Good c' -> Good c.
Proof.
  intros c c' H [e [a [h [G [HS HI]]]]].
  exists e, a, h, G. split; [|exact HI].
  eapply progress_trans; [exact H|exact HS].
Qed.

Lemma good_DE1' : forall t k c C W, S t = (2 * k)%nat -> C <> 0 -> C + 1 < pw c -> (11 <= c)%nat ->
  W = (S t + c + 1)%nat -> Good (D1 (S t) (TL (bin c C) (D3 B0)) W).
Proof.
  intros t k c C W Hk H0 H1 H2 H3.
  destruct (N_tz C H0) as [r [C1 HC]].
  destruct (tz_bound c r C1 ltac:(lia)) as [c1 [Ec Hc1]].
  subst c C. apply (good_DE1 t k r c1 C1 W); assumption.
Qed.

Lemma good_DO0' : forall t k j L C W, S t = (2 * k + 1)%nat -> pw (L - 1) <= C -> C < pw L -> (11 <= L)%nat ->
  W = (S t + (2 * j + S L) + 1)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  Good (D1 (S t) (TL (bin (2 * j + S L) (pw (2 * j) * (2 * C + 1))) (D3 B0)) W).
Proof.
  intros t k j L C W Hk H1 H2 H3 H4 H5.
  pose proof (pw_pos (L - 1)) as P.
  destruct (N_tz C ltac:(lia)) as [r [C2 HC]].
  rewrite HC in H1, H2.
  destruct (tz_bound L r C2 H2) as [c2 [EL Hc2]].
  subst L C. apply (good_DO0 t k j r c2 C2 W); assumption.
Qed.

Lemma good_BO0' : forall t k j L C W, S t = (2 * k + 1)%nat -> C <> 0 -> C < pw L -> (9 <= L)%nat ->
  (S t + (2 * j + S L) + 1 <= W)%nat -> (W <= S t + (2 * j + S L) + 2)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  (t = 0%nat -> j = 0%nat -> W = (S t + (2 * j + S L) + 1)%nat -> C <> 83) ->
  Good (D1 (S t) (TL (bin (2 * j + S L) (pw (2 * j) * (2 * C + 1))) (U B0)) W).
Proof.
  intros t k j L C W Hk H0 H1 H2 H3 H4 H5 H6.
  destruct (N_tz C H0) as [r [C2 HC]].
  rewrite HC in H1.
  destruct (tz_bound L r C2 H1) as [c2 [EL Hc2]].
  subst L C. apply (good_BO0 t k j r c2 C2 W); assumption.
Qed.

(* The second level below a long tail *)
Lemma good_D3 : forall t c E u, E <> 0 -> E < pw c -> u = (t + c + 11)%nat -> (88 <= u)%nat ->
  Good (D1 (S t) (TL (bin (c + 11) (E + pw (c + 10))) (D3 B0)) (S (S u))).
Proof.
  intros t c E u H0 H1 Hu Hb.
  assert (P2 : pw (c + 10) = 1024 * pw c) by (rewrite pw_add; change (pw 10) with 1024; lia).
  assert (P3 : pw (c + 11) = 2048 * pw c) by (rewrite pw_add; change (pw 11) with 2048; lia).
  destruct (Nat.Even_or_Odd (S t)) as [[k Hk]|[k Hk]].
  - apply (good_DE1' t k (c + 11) (E + pw (c + 10)) (S (S u)) Hk); lia.
  - destruct (N_tz E H0) as [q [E2 HE]].
    rewrite HE in H1.
    destruct (tz_bound c q E2 H1) as [c2 [Ec Hc2]].
    assert (Q2 : pw (c2 + 10) = 1024 * pw c2) by (rewrite pw_add; change (pw 10) with 1024; lia).
    assert (Q3 : pw (c2 + 11) = 2048 * pw c2) by (rewrite pw_add; change (pw 11) with 2048; lia).
    assert (HC : E + pw (c + 10) = pw q * (2 * (E2 + pw (c2 + 10)) + 1)).
    { rewrite HE, Ec. replace (q + S c2 + 10)%nat with (q + S (c2 + 10))%nat by lia. rewrite pw_add, pw_S. lia. }
    rewrite HC.
    replace (c + 11)%nat with (q + S (c2 + 11))%nat by lia.
    replace (c2 + 11 - 1)%nat with (c2 + 10)%nat in * by lia.
    pose proof (pw_pos c2) as Pc.
    destruct (Nat.Even_or_Odd q) as [[j Hj]|[j Hj]].
    + rewrite Hj.
      assert (Hl : pw (c2 + 11 - 1) <= E2 + pw (c2 + 10)).
      { replace (c2 + 11 - 1)%nat with (c2 + 10)%nat by lia. lia. }
      apply (good_DO0' t k j (c2 + 11) (E2 + pw (c2 + 10)) (S (S u)) Hk Hl); lia.
    + rewrite Hj.
      assert (Hl : pw (c2 + 11 - 1) <= E2 + pw (c2 + 10)).
      { replace (c2 + 11 - 1)%nat with (c2 + 10)%nat by lia. lia. }
      apply (good_DO1 t k j (c2 + 11) (E2 + pw (c2 + 10)) (S (S u)) Hk Hl); lia.
Qed.

Lemma good_tailL : forall u D n, n = S u -> D <> 0 -> (forall x, D <> pw x) -> D < pw (u - 10) -> (88 <= u)%nat ->
  Good (AC (TL (bin u D) (U B0)) (oL n)).
Proof.
  intros u D n Hn H0 Hp H1 Hb. subst n.
  destruct (N_tz D H0) as [t [E HD]].
  assert (HE : E <> 0).
  { intros E0. apply (Hp t). rewrite HD, E0. lia. }
  assert (H1' : pw t * (2 * E + 1) < pw (u - 10)) by lia.
  destruct (tz_bound (u - 10) t E H1') as [c [Ec HEc]].
  assert (Hu : u = (t + c + 11)%nat) by lia.
  assert (H2 : pw u + D = pw t * (2 * (E + pw (c + 10)) + 1)).
  { rewrite HD. replace u with (t + S (c + 10))%nat by lia. rewrite pw_add, pw_S. lia. }
  assert (H3 : D + 1 < pw u).
  { pose proof (pw_lt (u - 10) u ltac:(lia)) as P. pose proof (pw_pos (u - 10)). lia. }
  apply (good_back _ _ (tailL u D t (c + 11) (E + pw (c + 10)) H0 H3 H2 ltac:(lia))).
  apply (good_D3 t c E u HE HEc Hu Hb).
Qed.

Lemma tz_sub : forall n E B r G1, E <> 0 -> E < pw B -> (B <= n)%nat ->
  pw n = pw r * (2 * G1 + 1) + E -> (r < B)%nat.
Proof.
  intros n E B r G1 H0 H1 H2 H3.
  destruct (Nat.lt_ge_cases r B) as [H|H]; [exact H|exfalso].
  destruct (mult_split r B G1 H) as [Z HZ].
  rewrite HZ in H3.
  rewrite (pw_split B n H2) in H3.
  assert (E2 : pw (n - B) * pw B + 0 = Z * pw B + E) by lia.
  destruct (mod_uniq (pw B) (pw (n - B)) Z 0 E ltac:(pose proof (pw_pos B); lia) H1 E2) as [_ E3]. lia.
Qed.

Lemma good_TS2 : forall u Vl E B n, n = S (S u) -> Vl <> 0 -> Vl + E = pw u -> E <> 0 -> E < pw B ->
  (B + 6 <= u)%nat -> (10 <= u)%nat -> Good (AC (TL (bin u Vl) (U B0)) (oL n)).
Proof.
  intros u Vl E B n Hn H0 H1 H2 H3 H4 H5. subst n.
  apply good_TS; [exact H0|lia|exact H5|].
  intros _ r G1 Hr.
  assert (HE : pw (S u) = pw r * (2 * G1 + 1) + E) by (rewrite pw_S; lia).
  pose proof (tz_sub (S u) E B r G1 H2 H3 ltac:(lia) HE). lia.
Qed.

End Part_Close8.
Import Part_Close8.

Module Part_Close9.

Local Open Scope N_scope.

Lemma y1o_bound : forall t q, y1o t q < pw (Apr q + (Afun (S t) + (S t + 3) + q)).
Proof.
  intros t q.
  pose proof (y2v_lt t q (Afun (S t) + (S t + 3) + q) ltac:(lia) ltac:(lia)) as H.
  pose proof (y2v_y1o t q) as E.
  replace (Apr q + (Afun (S t) + (S t + 3) + q + 1))%nat with (S (Apr q + (Afun (S t) + (S t + 3) + q)))%nat in H by lia.
  rewrite pw_S in H. lia.
Qed.

(* The b level with an odd q, into a tail *)
Lemma good_BO1 : forall t k j c1 C1 W, S t = (2 * k + 1)%nat -> C1 < pw c1 -> (9 <= c1)%nat ->
  (S t + (2 * j + 1 + S c1) + 1 <= W)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  (y1o t (2 * j + 1) <= C1 + pw c1 -> C1 + pw c1 - y1o t (2 * j + 1) <> 0 /\ forall x, C1 + pw c1 - y1o t (2 * j + 1) <> pw x) ->
  Good (D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) (U B0)) W).
Proof.
  intros t k j c1 C1 W Hk H1 H2 H3 Hbig HD.
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd (2 * j + 1)) as BP.
  pose proof (zv_lt2 t (2 * j + 1) W ltac:(lia) ltac:(lia)) as HZ.
  pose proof (y2v_y1o t (2 * j + 1)) as Hy.
  pose proof (y1o_bound t (2 * j + 1)) as HB.
  set (W2 := (Apr (2 * j + 1) + S (Afun (S t) + S W))%nat).
  set (B := (Apr (2 * j + 1) + (Afun (S t) + (S t + 3) + (2 * j + 1)))%nat) in *.
  assert (HW : pw W2 = 2 * pw (W2 - 1)) by (apply pw_pred2; unfold W2; lia).
  assert (HW' : pw (W2 - 1) = 2 * pw (W2 - 2)).
  { replace (W2 - 2)%nat with (W2 - 1 - 1)%nat by lia. apply pw_pred2. unfold W2; lia. }
  assert (HBu : (B + 6 <= W2 - 2)%nat) by (unfold B, W2; lia).
  pose proof (pw_le B (W2 - 2) ltac:(lia)) as P1.
  pose proof (pw_le (S c1) (W2 - 2) ltac:(unfold W2; lia)) as P2.
  pose proof (pw_le (S c1) (W2 - 1 - 10) ltac:(unfold W2; lia)) as P3.
  pose proof (pw_S c1) as P4.
  assert (HK : y2v t (2 * j + 1) + 1 + 2 * (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) + 1 = pw W2) by lia.
  destruct (N.le_gt_cases (y1o t (2 * j + 1)) (C1 + pw c1)) as [Hle|Hlt].
  - destruct (HD Hle) as [HD0 HDp].
    assert (A1 : C1 + 1 + pw c1 <= pw (W2 - 1)) by lia.
    assert (A2 : C1 + 1 + pw c1 + (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) = pw (W2 - 1) + (C1 + pw c1 - y1o t (2 * j + 1))) by lia.
    assert (A3 : C1 + pw c1 - y1o t (2 * j + 1) < pw (W2 - 1)) by lia.
    apply (good_back _ _ (b_O1 t k j c1 C1 W _ (W2 - 1) _ Hk ltac:(lia) HZ H1 HK ltac:(unfold W2; lia) A1 A2 A3)).
    apply (good_tailL (W2 - 1) _ W2 ltac:(unfold W2; lia) HD0 HDp ltac:(lia) ltac:(unfold W2; lia)).
  - assert (A1 : C1 + 1 + pw c1 <= pw (W2 - 2)) by lia.
    assert (A2 : C1 + 1 + pw c1 + (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) = pw (W2 - 2) + (pw (W2 - 2) + (C1 + pw c1) - y1o t (2 * j + 1))) by lia.
    assert (A3 : pw (W2 - 2) + (C1 + pw c1) - y1o t (2 * j + 1) < pw (W2 - 2)) by lia.
    apply (good_back _ _ (b_O1 t k j c1 C1 W _ (W2 - 2) _ Hk ltac:(lia) HZ H1 HK ltac:(unfold W2; lia) A1 A2 A3)).
    apply (good_TS2 (W2 - 2) _ (y1o t (2 * j + 1) - (C1 + pw c1)) B W2 ltac:(unfold W2; lia)); try lia.
Qed.

Lemma good_B : forall t c C W, C <> 0 -> C < pw c -> (S t + c + 1 <= W)%nat -> (W <= S t + c + 2)%nat ->
  (26 <= S t \/ 90 <= W)%nat ->
  (forall k, S t = (2 * k)%nat -> (9 <= c)%nat) ->
  (forall k, S t = (2 * k + 1)%nat -> forall q c1 C1, C = pw q * (2 * C1 + 1) -> c = (q + S c1)%nat ->
     (9 <= c1)%nat /\ C1 <> 0 /\ (forall j, q = (2 * j + 1)%nat -> y1o t q <= C1 + pw c1 ->
        C1 + pw c1 - y1o t q <> 0 /\ forall x, C1 + pw c1 - y1o t q <> pw x)) ->
  (t = 0%nat -> W = (S t + c + 1)%nat -> C <> 167) ->
  Good (D1 (S t) (TL (bin c C) (U B0)) W).
Proof.
  intros t c C W H0 H1 H2 H3 Hbig HE HO H83.
  destruct (Nat.Even_or_Odd (S t)) as [[k Hk]|[k Hk]].
  - apply (good_BE1 t k c C W Hk H0 H1 (HE k Hk) H2 H3).
  - destruct (N_tz C H0) as [q [C1 HC]].
    assert (H1' : pw q * (2 * C1 + 1) < pw c) by lia.
    destruct (tz_bound c q C1 H1') as [c1 [Ec Hc1]].
    destruct (HO k Hk q c1 C1 HC Ec) as [H9 [Hn HD]].
    destruct (Nat.Even_or_Odd q) as [[j Hj]|[j Hj]].
    + subst q.
      assert (Hg : Good (D1 (S t) (TL (bin (2 * j + S c1) (pw (2 * j) * (2 * C1 + 1))) (U B0)) W)).
      { apply (good_BO0' t k j c1 C1 W Hk Hn Hc1 H9); try lia.
        intros Et Ej HW E83. apply (H83 Et); [lia|]. rewrite HC, Ej, E83. reflexivity. }
      rewrite HC, Ec. exact Hg.
    + subst q.
      assert (Hg : Good (D1 (S t) (TL (bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * C1 + 1))) (U B0)) W)).
      { apply (good_BO1 t k j c1 C1 W Hk Hc1 H9 ltac:(lia) Hbig (HD j eq_refl)). }
      rewrite HC, Ec. exact Hg.
Qed.

End Part_Close9.
Import Part_Close9.

Module Part_Close10.

Local Open Scope N_scope.

(* Zero cells of y1' *)
Lemma cell0_of : forall Y c Q b, Y = Q * pw (S c) + b -> b < pw c -> cell0 Y c.
Proof. intros Y c Q b H1 H2. exists Q, b. split; [exact H2|exact H1]. Qed.

Lemma pw_factor : forall x y, (x <= y)%nat -> exists z, pw y = z * pw x /\ z = pw (y - x).
Proof. intros x y H. exists (pw (y - x)). split; [|reflexivity]. rewrite (pw_split x y H). lia. Qed.

Lemma Ya_form : forall m, (1 <= m)%nat -> Ya m = 4 * (pw m - 1) + 1.
Proof.
  intros m H. unfold Ya. rewrite pw_add_r2. pose proof (pw_pos m) as P.
  destruct m as [|m]; [lia|]. rewrite pw_S in *. pose proof (pw_pos m). lia.
Qed.

Lemma Yc_form : forall a r, pw a * (pw (r + 2) - 1) = pw (a + (r + 2)) - pw a.
Proof.
  intros a r. rewrite (pw_add a (r + 2)). pose proof (pw_pos (r + 2)) as P.
  generalize dependent (pw (r + 2)). intros w P.
  assert (E : exists w', w = w' + 1) by (exists (w - 1); lia).
  destruct E as [w' E]. subst w. replace (w' + 1 - 1) with w' by lia. rewrite N.mul_add_distr_l, N.mul_1_r, N.add_sub. reflexivity.
Qed.

Lemma cz_low : forall t r c, (c + 2 <= Apr r)%nat -> cell0 (y1o t r) c.
Proof.
  intros t r c H. rewrite y1o_split.
  destruct (pw_factor (S c) (Apr r + Afun (S t)) ltac:(lia)) as [z1 [E1 _]].
  destruct (pw_factor (S c) (Apr r - 1) ltac:(lia)) as [z2 [E2 _]].
  apply (cell0_of _ c (z1 * Ya (S t) + z2 * (pw (r + 2) - 1)) 0).
  - rewrite E1, E2. lia.
  - pose proof (pw_pos c). lia.
Qed.

Lemma Yc_bound : forall r, pw (Apr r - 1) * (pw (r + 2) - 1) < pw (Apr r + r + 1).
Proof.
  intros r. pose proof (Yc_lt (Apr r - 1) r) as H. pose proof (Apr_pos r).
  replace (Apr r - 1 + (r + 2))%nat with (Apr r + r + 1)%nat in H by lia. exact H.
Qed.

Lemma cz_gap : forall t r c, (Apr r + r + 1 <= c)%nat -> (c < Apr r + Afun (S t))%nat -> cell0 (y1o t r) c.
Proof.
  intros t r c H1 H2. rewrite y1o_split.
  destruct (pw_factor (S c) (Apr r + Afun (S t)) ltac:(lia)) as [z1 [E1 _]].
  apply (cell0_of _ c (z1 * Ya (S t)) (pw (Apr r - 1) * (pw (r + 2) - 1))).
  - rewrite E1. lia.
  - pose proof (Yc_bound r). pose proof (pw_le _ _ H1). lia.
Qed.

Lemma y1o_form : forall t r, y1o t r = pw (Apr r + Afun (S t) + 2) * (pw (S t) - 1) + pw (Apr r + Afun (S t)) + pw (Apr r - 1) * (pw (r + 2) - 1).
Proof.
  intros t r. rewrite y1o_split. rewrite (Ya_form (S t)) by lia.
  rewrite (pw_add_r2 (Apr r + Afun (S t))).
  generalize (pw (S t) - 1). generalize (pw (Apr r - 1) * (pw (r + 2) - 1)). intros Y x. lia.
Qed.

Lemma cz_a31 : forall t r, (r + 1 <= Afun (S t))%nat -> cell0 (y1o t r) (Apr r + Afun (S t) + 1).
Proof.
  intros t r H. rewrite y1o_form.
  set (a3 := (Apr r + Afun (S t))%nat).
  apply (cell0_of _ (a3 + 1) (pw (S t) - 1) (pw a3 + pw (Apr r - 1) * (pw (r + 2) - 1))).
  - replace (S (a3 + 1)) with (a3 + 2)%nat by lia. lia.
  - pose proof (Yc_bound r) as B. pose proof (pw_le (Apr r + r + 1) a3 ltac:(unfold a3; lia)) as P.
    replace (a3 + 1)%nat with (S a3) by lia. rewrite pw_S. lia.
Qed.

Lemma Yc_exact : forall r, pw (Apr r - 1) * (pw (r + 2) - 1) = pw (Apr r + r + 1) - pw (Apr r - 1).
Proof.
  intros r. rewrite Yc_form. pose proof (Apr_pos r).
  replace (Apr r - 1 + (r + 2))%nat with (Apr r + r + 1)%nat by lia. reflexivity.
Qed.

Lemma cz_Q2 : forall t r, r = Afun (S t) -> cell0 (y1o t r) (Apr r + Afun (S t)).
Proof.
  intros t r H. rewrite y1o_form. rewrite Yc_exact.
  rewrite <- H.
  set (a3 := (Apr r + r)%nat).
  assert (P0 : pw (Apr r - 1) < pw a3) by (pose proof (pw_lt (Apr r - 1) a3 ltac:(pose proof (Apr_pos r); unfold a3; lia)) as P; pose proof (pw_pos (Apr r - 1)); lia).
  pose proof (pw_pos (Apr r - 1)) as P00.
  assert (P1 : pw (a3 + 1) = 2 * pw a3) by (replace (a3 + 1)%nat with (S a3) by lia; apply pw_S).
  assert (P2 : pw (a3 + 2) = 4 * pw a3) by (apply pw_add_r2).
  apply (cell0_of _ a3 (2 * (pw (S t) - 1) + 1) (pw a3 - pw (Apr r - 1))).
  - rewrite (pw_S a3), P1, P2. generalize (pw (S t) - 1). intros x. lia.
  - lia.
Qed.

Lemma cz_M : forall t r c, (Afun (S t) + 1 <= r)%nat -> (c = Apr r + Afun (S t) \/ c = Apr r + Afun (S t) + 1)%nat ->
  cell0 (y1o t r) c.
Proof.
  intros t r c H Hc. rewrite y1o_form. rewrite Yc_exact.
  set (a3 := (Apr r + Afun (S t))%nat) in *.
  destruct (pw_factor (a3 + 2) (Apr r + r + 1) ltac:(unfold a3; lia)) as [z [E _]].
  assert (P0 : pw (Apr r - 1) < pw a3) by (pose proof (pw_lt (Apr r - 1) a3 ltac:(pose proof (Apr_pos r); pose proof (Afun_pos t); unfold a3; lia)) as P; pose proof (pw_pos (Apr r - 1)); lia).
  pose proof (pw_pos (Apr r - 1)) as P00.
  assert (P1 : pw (a3 + 1) = 2 * pw a3) by (replace (a3 + 1)%nat with (S a3) by lia; apply pw_S).
  assert (P2 : pw (a3 + 2) = 4 * pw a3) by (apply pw_add_r2).
  assert (Hz : pw (a3 + 2) <= pw (Apr r + r + 1)) by (apply pw_le; unfold a3; lia).
  rewrite P2 in E, Hz.
  destruct Hc as [Hc|Hc]; subst c.
  - apply (cell0_of _ a3 (2 * (pw (S t) - 1 + z)) (pw a3 - pw (Apr r - 1))).
    + rewrite (pw_S a3), P2. generalize (pw (S t) - 1). intros x. lia.
    + lia.
  - apply (cell0_of _ (a3 + 1) (pw (S t) - 1 + z) (pw a3 - pw (Apr r - 1))).
    + replace (S (a3 + 1)) with (a3 + 2)%nat by lia. rewrite P2. generalize (pw (S t) - 1). intros x. lia.
    + lia.
Qed.

Lemma y1o_ltT : forall t r T, (Afun (S t) + (S t + 3) <= T)%nat -> (r + 3 <= T)%nat -> y1o t r < pw (Apr r + T).
Proof.
  intros t r T H1 H2. pose proof (y2v_lt t r T H1 H2) as H. pose proof (y2v_y1o t r) as E.
  replace (Apr r + (T + 1))%nat with (S (Apr r + T)) in H by lia. rewrite pw_S in H. lia.
Qed.

Lemma cz_top : forall t r T c, (Afun (S t) + (S t + 3) <= T)%nat -> (r + 3 <= T)%nat -> (Apr r + T <= c)%nat ->
  cell0 (y1o t r) c.
Proof.
  intros t r T c H1 H2 H3.
  pose proof (y1o_ltT t r T H1 H2) as Y. pose proof (pw_le _ _ H3) as P.
  apply (cell0_of _ c 0 (y1o t r)); lia.
Qed.

Lemma y1o_lt4 : forall t r, (r <= Afun (S t))%nat -> y1o t r < pw (Apr r + Afun (S t) + (S t + 2)).
Proof.
  intros t r H. rewrite y1o_form.
  set (a3 := (Apr r + Afun (S t))%nat) in *.
  pose proof (Yc_bound r) as B.
  pose proof (pw_le (Apr r + r + 1) (S a3) ltac:(unfold a3; lia)) as P.
  rewrite pw_S in P.
  replace (a3 + (S t + 2))%nat with (a3 + 2 + S t)%nat by lia.
  rewrite (pw_add (a3 + 2) (S t)).
  rewrite pw_add_r2.
  pose proof (pw_pos (S t)) as Q. generalize dependent (pw (S t)). intros w Q.
  assert (E : exists w', w = w' + 1) by (exists (w - 1); lia).
  destruct E as [w' E]. subst w. replace (w' + 1 - 1) with w' by lia.
  rewrite N.mul_add_distr_l, N.mul_1_r. pose proof (pw_pos a3). lia.
Qed.

Lemma cz_top2 : forall t r c, (r <= Afun (S t))%nat -> (Apr r + Afun (S t) + (S t + 2) <= c)%nat ->
  cell0 (y1o t r) c.
Proof.
  intros t r c H1 H2.
  pose proof (y1o_lt4 t r H1) as Y. pose proof (pw_le _ _ H2) as P.
  apply (cell0_of _ c 0 (y1o t r)); lia.
Qed.

End Part_Close10.
Import Part_Close10.

Module Part_Close11.

Local Open Scope N_scope.

Ltac wit c1 c2 Z1 Z2 :=
  exists c1, c2; split; [lia|split; [lia|split; [lia|split; [apply Z1; lia|apply Z2; lia]]]].

(* A long interval holds two zero cells of y1' *)
Lemma two_cells : forall t j u0 v0, (2 * (u0 + S t + (2 * j + 1) + 1) + 18 <= 5 * (v0 - u0))%nat ->
  exists c1 c2, (u0 <= c1)%nat /\ (c1 < c2)%nat /\ (c2 < v0)%nat /\
    cell0 (y1o t (2 * j + 1)) c1 /\ cell0 (y1o t (2 * j + 1)) c2.
Proof.
  intros t j u0 v0 H.
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_bd (2 * j + 1)) as BP.
  pose proof (cz_low t (2 * j + 1)) as Zlow.
  pose proof (cz_gap t (2 * j + 1)) as Zgap.
  pose proof (cz_a31 t (2 * j + 1)) as Z31.
  pose proof (cz_Q2 t (2 * j + 1)) as ZQ.
  pose proof (cz_M t (2 * j + 1)) as ZM.
  pose proof (cz_top t (2 * j + 1)) as Ztop.
  pose proof (cz_top2 t (2 * j + 1)) as Z42.
  generalize dependent (y1o t (2 * j + 1)). intros Y Zlow Zgap Z31 ZQ ZM Ztop Z42.
  generalize dependent (Apr (2 * j + 1)). intros Ap BP Zlow Zgap Z31 ZQ ZM Ztop Z42.
  generalize dependent (Afun (S t)). intros A BA Zgap Z31 ZQ ZM Ztop Z42.
  set (m := S t) in *.
  assert (Hm : (1 <= m)%nat) by (unfold m; lia).
  clearbody m.
  set (R := (2 * j + 1)%nat) in *.
  assert (HR : R = (2 * j + 1)%nat) by reflexivity.
  clearbody R.
  assert (Z31' : (R + 1 <= A)%nat -> forall c, c = (Ap + A + 1)%nat -> cell0 Y c).
  { intros H1 c Hc. subst c. apply Z31. exact H1. }
  assert (ZQ' : R = A -> forall c, c = (Ap + A)%nat -> cell0 Y c).
  { intros H1 c Hc. subst c. apply ZQ. exact H1. }
  clear Z31 ZQ.
  set (T0 := (A + (m + 2))%nat).
  assert (ZT0 : forall c, (R <= A)%nat -> (Ap + T0 <= c)%nat -> cell0 Y c).
  { intros c H1 H2. apply (Z42 c H1). unfold T0 in H2. lia. }
  destruct (Nat.le_gt_cases (u0 + 3) Ap) as [L0|L0].
  { wit u0 (u0 + 1)%nat Zlow Zlow. }
  destruct (Nat.le_gt_cases (R + 1) A) as [S1|S1].
  - (* a2 <= a3 *)
    destruct (Nat.eq_dec (u0 + 2) Ap) as [U|U].
    + destruct (Nat.eq_dec (R + 1) A) as [E|E].
      * wit u0 (Ap + A + 1)%nat Zlow Z31'.
      * wit u0 (Ap + R + 1)%nat Zlow Zgap.
    + destruct (Nat.lt_ge_cases u0 (Ap + R + 1)) as [U2|U2].
      * destruct (Nat.lt_trichotomy (R + 2) A) as [E|[E|E]].
        -- wit (Ap + R + 1)%nat (Ap + R + 2)%nat Zgap Zgap.
        -- wit (Ap + R + 1)%nat (Ap + A + 1)%nat Zgap Z31'.
        -- exists (Ap + A + 1)%nat, (Ap + T0)%nat. unfold T0 in *.
           split; [lia|split; [lia|split; [lia|split; [apply Z31'; lia|apply ZT0; unfold T0; lia]]]].
      * destruct (Nat.lt_ge_cases (u0 + 1) (Ap + A)) as [U3|U3].
        -- wit u0 (u0 + 1)%nat Zgap Zgap.
        -- destruct (Nat.eq_dec (u0 + 1) (Ap + A)) as [U4|U4].
           ++ wit u0 (Ap + A + 1)%nat Zgap Z31'.
           ++ unfold T0 in *. destruct (Nat.le_gt_cases u0 (Ap + A + 1)) as [U5|U5].
              ** exists (Ap + A + 1)%nat, (Ap + (A + (m + 2)))%nat.
                 split; [lia|split; [lia|split; [lia|split; [apply Z31'; lia|apply ZT0; lia]]]].
              ** destruct (Nat.lt_ge_cases u0 (Ap + (A + (m + 2)))) as [U6|U6].
                 --- exists (Ap + (A + (m + 2)))%nat, (Ap + (A + (m + 2)) + 1)%nat.
                     split; [lia|split; [lia|split; [lia|split; apply ZT0; lia]]].
                 --- exists u0, (u0 + 1)%nat.
                     split; [lia|split; [lia|split; [lia|split; apply ZT0; lia]]].
  - destruct (Nat.eq_dec R A) as [E|E].
    + (* a2 = a3 + 1 *)
      unfold T0 in *.
      destruct (Nat.eq_dec (u0 + 2) Ap) as [U|U].
      * wit u0 (Ap + A)%nat Zlow ZQ'.
      * destruct (Nat.le_gt_cases u0 (Ap + A)) as [U2|U2].
        -- exists (Ap + A)%nat, (Ap + (A + (m + 2)))%nat.
           split; [lia|split; [lia|split; [lia|split; [apply ZQ'; lia|apply ZT0; lia]]]].
        -- destruct (Nat.lt_ge_cases u0 (Ap + (A + (m + 2)))) as [U6|U6].
           ++ exists (Ap + (A + (m + 2)))%nat, (Ap + (A + (m + 2)) + 1)%nat.
              split; [lia|split; [lia|split; [lia|split; apply ZT0; lia]]].
           ++ exists u0, (u0 + 1)%nat.
              split; [lia|split; [lia|split; [lia|split; apply ZT0; lia]]].
    + (* a2 >= a3 + 2 *)
      assert (ET : exists T, (A + (m + 3) <= T)%nat /\ (R + 3 <= T)%nat /\ (T <= A + (m + 3) \/ T <= R + 3)%nat).
      { destruct (Nat.le_gt_cases R (A + m)) as [X|X].
        - exists (A + (m + 3))%nat. lia.
        - exists (R + 3)%nat. lia. }
      destruct ET as [T [T1 [T2 T3]]].
      assert (ZT : forall c, (Ap + T <= c)%nat -> cell0 Y c).
      { intros c Hc. apply (Ztop T); [exact T1|exact T2|exact Hc]. }
      clear Ztop ZT0 ZQ' Z42.
      assert (ZM1 : forall c, (c = Ap + A \/ c = Ap + A + 1)%nat -> cell0 Y c).
      { intros c Hc. apply ZM; [lia|exact Hc]. }
      destruct (Nat.eq_dec (u0 + 2) Ap) as [U|U].
      * wit u0 (Ap + A)%nat Zlow ZM1.
      * destruct (Nat.le_gt_cases u0 (Ap + A)) as [U2|U2].
        -- wit (Ap + A)%nat (Ap + A + 1)%nat ZM1 ZM1.
        -- destruct (Nat.eq_dec u0 (Ap + A + 1)) as [U3|U3].
           ++ wit (Ap + A + 1)%nat (Ap + T)%nat ZM1 ZT.
           ++ destruct (Nat.lt_ge_cases u0 (Ap + T)) as [U4|U4].
              ** wit (Ap + T)%nat (Ap + T + 1)%nat ZT ZT.
              ** wit u0 (u0 + 1)%nat ZT ZT.
Qed.

(* Two zero cells of y1' under a run of Z with the ratio of LR *)
Lemma N2_run : forall Z u t C q C1 c1 j p0 q0, Z = pw t * (2 * C + 1) -> C = pw q * (2 * C1 + 1) ->
  q = (2 * j + 1)%nat -> u = (t + S (q + S c1))%nat -> ones_on Z p0 q0 -> (q0 <= u)%nat ->
  (2 * p0 + 25 <= 5 * (q0 - p0))%nat ->
  C1 + pw c1 <> y1o t q /\ forall x, C1 + pw c1 <> y1o t q + pw x.
Proof.
  intros Z u t C q C1 c1 j p0 q0 HZ HC Hq Hu Hrun Hq0 Hratio.
  pose proof (ones_tz Z C t p0 q0 HZ Hrun ltac:(lia)) as Ht.
  assert (Ht2 : (t < p0)%nat).
  { destruct (Nat.eq_dec t p0) as [E|E]; [exfalso|lia].
    pose proof (ones_sub_lo Z p0 (S p0) q0 Hrun ltac:(lia)) as R1.
    pose proof (ones_shift Z C t _ _ HZ R1 ltac:(lia)) as R2.
    pose proof (ones_tz C C1 q _ _ HC R2 ltac:(lia)) as R3. lia. }
  pose proof (ones_shift Z C t _ _ HZ Hrun Ht2) as R2.
  pose proof (ones_tz C C1 q _ _ HC R2 ltac:(lia)) as R3.
  pose proof (ones_sub_lo C _ (S p0 - S t) _ R2 ltac:(lia)) as R4.
  pose proof (ones_shift C C1 q _ _ HC R4 ltac:(lia)) as R5.
  set (u0 := (S p0 - S t - S q)%nat) in *.
  set (v0 := (q0 - S t - S q)%nat) in *.
  pose proof (ones_high C1 u0 v0 c1 R5 ltac:(unfold v0; lia)) as R6.
  subst q.
  destruct (two_cells t j u0 v0 ltac:(unfold u0, v0; lia)) as [c2 [c3 [H1 [H2 [H3 [H4 H5]]]]]].
  apply (two_zero _ _ c2 c3 H2).
  - apply (ones_cell _ u0 v0); [exact R6|lia].
  - apply (ones_cell _ u0 v0); [exact R6|lia].
  - exact H4.
  - exact H5.
Qed.

End Part_Close11.
Import Part_Close11.

Module Part_Close12.

Local Open Scope N_scope.

Lemma tz_uniq : forall a x b y, pw a * (2 * x + 1) = pw b * (2 * y + 1) -> a = b /\ x = y.
Proof.
  induction a as [|a IH]; intros x b y H; destruct b as [|b].
  - rewrite pw_0 in H. split; [reflexivity|lia].
  - exfalso. rewrite pw_0, pw_S in H. lia.
  - exfalso. rewrite pw_0, pw_S in H. lia.
  - rewrite !pw_S in H.
    assert (H2 : pw a * (2 * x + 1) = pw b * (2 * y + 1)) by lia.
    destruct (IH x b y H2) as [E1 E2]. split; [lia|exact E2].
Qed.

(* The b level from a number with at least three ones *)
Lemma good_Z : forall Z t c C W Zh v p, Z = pw t * (2 * C + 1) -> C < pw c ->
  Z = Zh * pw p + v -> v <> 0 -> v < pw p -> (forall x, v <> pw x) -> (p + 9 <= t + S c)%nat ->
  (3 <= pc Z)%nat -> (S t + c + 1 <= W)%nat -> (W <= S t + c + 2)%nat -> (26 <= S t \/ 90 <= W)%nat ->
  (t = 0%nat -> W = (S t + c + 1)%nat -> C <> 167) ->
  (forall k q c1 C1 j, S t = (2 * k + 1)%nat -> C = pw q * (2 * C1 + 1) -> c = (q + S c1)%nat -> q = (2 * j + 1)%nat ->
     C1 + pw c1 <> y1o t q /\ forall x, C1 + pw c1 <> y1o t q + pw x) ->
  Good (D1 (S t) (TL (bin c C) (U B0)) W).
Proof.
  intros Z t c C W Zh v p HZ HC HZv H0 H1 Hnp Hp Hpc HW1 HW2 Hbig H83 HD.
  assert (HC0 : C <> 0).
  { intros E. rewrite E in HZ. replace (pw t * (2 * 0 + 1)) with (pw t) in HZ by lia.
    rewrite HZ, pc_pw in Hpc. lia. }
  assert (Hsb : forall q C1, C = pw q * (2 * C1 + 1) -> (t + q + 2 <= p)%nat).
  { intros q C1 Hq. apply (second_bit Zh v p t C q C1 H0 H1 Hnp); [lia|exact Hq]. }
  apply good_B; try assumption.
  - intros k Hk.
    destruct (N_tz C HC0) as [q [C1 Hq]]. pose proof (Hsb q C1 Hq). lia.
  - intros k Hk q c1 C1 Hq Hc. pose proof (Hsb q C1 Hq) as Hs.
    split; [lia|]. split.
    + intros E. subst C1.
      assert (E2 : Z = pw t + pw (t + S q)).
      { rewrite HZ, Hq, (pw_add t (S q)), pw_S. lia. }
      rewrite E2 in Hpc. pose proof (pc_two t (t + S q)). lia.
    + intros j Hj Hle.
      destruct (HD k q c1 C1 j Hk Hq Hc Hj) as [D1' D2].
      split; [lia|]. intros x E. apply (D2 x). lia.
Qed.

Lemma G1_ne : forall r G1 h, pw (h - 2) <= pw r * (2 * G1 + 1) -> (r + 3 <= h)%nat -> G1 <> 0.
Proof.
  intros r G1 h H1 H2 E. subst G1.
  pose proof (pw_lt r (h - 2) ltac:(lia)) as P. pose proof (pw_pos r). lia.
Qed.

(* A step from a state with e = 1 *)
Lemma step_e1 : forall a h G, Inv true a h G -> Good (FC true a h (pw h - 1 - G)).
Proof.
  intros a h G [Ha [Hh [Hlo [Hhi [r [G1 [HG [Hr [He [Hra HD]]]]]]]]]].
  change (Good (F1 a h (pw h - 1 - G))).
  destruct a as [|t]; [lia|].
  pose proof (pw_pos (h - 2)) as P0. pose proof (pw_S h) as P1.
  apply (good_back _ _ (F1_D1 t h G (pw h - 1 - G) ltac:(lia))).
  pose proof (He eq_refl) as He9.
  apply good_B.
  - lia.
  - lia.
  - lia.
  - lia.
  - left; lia.
  - intros k Hk. lia.
  - intros k Hk q c1 C1 Hq Hc.
    assert (Eq : pw q * (2 * C1 + 1) = pw r * (2 * G1 + 1)) by lia.
    destruct (tz_uniq q C1 r G1 Eq) as [E1 E2]. subst q C1.
    assert (Ec1 : c1 = (h - r)%nat) by lia.
    split; [lia|]. split.
    + apply (G1_ne r G1 h); [lia|exact Hr].
    + intros j Hj Hle.
      destruct (HD t eq_refl) as [_ [_ H3]].
      assert (Hev : Nat.even (S t) = false).
      { rewrite Hk. apply even_2j1. }
      assert (Hod : Nat.odd r = true) by (rewrite Hj; apply odd_2j1).
      rewrite Ec1 in Hle.
      destruct (H3 Hev eq_refl Hod Hle) as [p [q0 [Hrun Hrat]]].
      rewrite Ec1. apply (ones_not_pow _ p q0 Hrun). lia.
  - intros Et. lia.
Qed.

Lemma good_TS3 : forall u Vl n, n = S (S u) -> Vl <> 0 -> Vl + 1 <= pw u -> (10 <= u)%nat ->
  (forall r G1, Nat.odd (S u) = true -> pw u + Vl = pw r * (2 * G1 + 1) -> (r + 7 <= u)%nat) ->
  Good (AC (TL (bin u Vl) (U B0)) (oL n)).
Proof.
  intros u Vl n Hn H0 H1 H2 H3. subst n. apply good_TS; [exact H0|exact H1|exact H2|].
  intros Ho r G1 Hr. apply (H3 r G1 Ho Hr).
Qed.

Lemma TS_small : forall u r2 G2 y1 Yq f G, y1 = pw f * Yq -> G <> 0 -> G < pw f -> (f <= S u)%nat ->
  pw (S u) + G = pw r2 * (2 * G2 + 1) + y1 -> (r2 < f)%nat.
Proof.
  intros u r2 G2 y1 Yq f G Hy H0 H1 H2 H3.
  destruct (Nat.lt_ge_cases r2 f) as [H|H]; [exact H|exfalso].
  destruct (mult_split r2 f G2 H) as [Z HZ].
  rewrite HZ, Hy in H3. rewrite (pw_split f (S u) H2) in H3.
  assert (E : pw (S u - f) * pw f + G = (Z + Yq) * pw f + 0) by lia.
  destruct (mod_uniq (pw f) (pw (S u - f)) (Z + Yq) G 0 H1 ltac:(pose proof (pw_pos f); lia) E) as [_ E3]. lia.
Qed.

(* A step from a state with e = 0 and a even *)
Lemma step_e0_even : forall t k h G, S t = (2 * k)%nat -> Inv false (S t) h G ->
  Good (FC false (S t) h (pw h - 1 - G)).
Proof.
  intros t k h G Hk [Ha [Hh [Hlo [Hhi [r [G1 [HG [Hr [_ [Hra HD]]]]]]]]]].
  change (Good (F0 (S t) h (pw h - 1 - G))).
  apply (good_back _ _ (F0_D1 t h G (pw h - 1 - G) ltac:(lia))).
  destruct (HD t eq_refl) as [Hd1 _].
  assert (Hev : Nat.even (S t) = true) by (rewrite Hk; apply even_2j).
  pose proof (Hd1 Hev eq_refl) as Hd. clear Hd1 HD.
  destruct (tz_bound h r G1 ltac:(lia)) as [c1 [Ec Hc1]].
  pose proof (Afun_bd (S t)) as BA.
  set (W0 := S (t + S h)) in *.
  set (W2 := (Afun (S t) + S W0)%nat).
  pose proof (yv_lt t (Afun (S t) + (S t + 2))%nat ltac:(lia)) as HY.
  pose proof (yv_y1e t) as Hye.
  assert (HW : pw W2 = 2 * pw (W2 - 1)) by (apply pw_pred2; unfold W2; lia).
  assert (HW' : pw (W2 - 1) = 2 * pw (W2 - 2)).
  { replace (W2 - 2)%nat with (W2 - 1 - 1)%nat by lia. apply pw_pred2. unfold W2; lia. }
  assert (HB : pw (Afun (S t) + (S t + 2)) = 2 * pw (Afun (S t) + (S t + 1))).
  { replace (Afun (S t) + (S t + 2))%nat with (S (Afun (S t) + (S t + 1))) by lia. apply pw_S. }
  pose proof (pw_le (Afun (S t) + (S t + 1)) (W2 - 2) ltac:(unfold W2, W0; lia)) as P1.
  pose proof (pw_le h (W2 - 2) ltac:(unfold W2, W0; lia)) as P2.
  assert (HK : yv t + 1 + 2 * (pw (W2 - 1) - 1 - y1e t) + 1 = pw W2) by lia.
  assert (HGr : pw r * (2 * G1 + 1) < pw (r + S c1)) by (rewrite <- Ec; lia).
  assert (E1 : bin h G = bin (r + S c1) (pw r * (2 * G1 + 1))) by (rewrite <- HG, <- Ec; reflexivity).
  assert (Step : forall u Vl, (r + S c1 + 1 <= S u)%nat -> G + 1 <= pw u ->
    G + 1 + (pw (W2 - 1) - 1 - y1e t) = pw u + Vl -> Vl < pw u ->
    D1 (S t) (TL (bin h G) B0) W0 -->+ AC (TL (bin u Vl) (U B0)) (oL W2)).
  { intros u Vl H1 H2 H3 H4. rewrite E1.
    apply (a_E1_tail t k r c1 G1 W0 _ u Vl Hk ltac:(unfold W0; lia) HGr HK H1); try rewrite <- HG; assumption. }
  destruct (N.le_gt_cases (y1e t) G) as [Hle|Hlt].
  - destruct (Hd Hle) as [p [q0 [Hrun Hrat]]].
    destruct (ones_not_pow _ p q0 Hrun ltac:(lia)) as [D0 Dp].
    pose proof (pw_le h (W2 - 1 - 10) ltac:(unfold W2, W0; lia)) as P3.
    apply (good_back _ _ (Step (W2 - 1)%nat (G - y1e t) ltac:(unfold W2, W0; lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    apply (good_tailL (W2 - 1) _ W2 ltac:(unfold W2; lia) D0 Dp ltac:(lia) ltac:(unfold W2, W0; lia)).
  - apply (good_back _ _ (Step (W2 - 2)%nat (pw (W2 - 2) + G - y1e t) ltac:(unfold W2, W0; lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    destruct (Nat.lt_ge_cases h (Afun (S t) - 1)) as [Hs|Hs].
    + apply (good_TS3 (W2 - 2) _ W2 ltac:(unfold W2; lia)).
      * lia.
      * lia.
      * unfold W2, W0; lia.
      * intros r2 G2 _ Hr2.
        pose proof (pw_le h (Afun (S t) - 1) ltac:(lia)) as P3. pose proof (pw_pos (h - 2)) as P4.
        assert (Hs2 : pw (S (W2 - 2)) + G = pw r2 * (2 * G2 + 1) + y1e t) by (rewrite pw_S; lia).
        pose proof (TS_small (W2 - 2) r2 G2 (y1e t) (Ya (S t)) (Afun (S t) - 1) G eq_refl ltac:(lia) ltac:(lia) ltac:(unfold W2, W0; lia) Hs2) as Hsm.
        unfold W2, W0. lia.
    + apply (good_TS2 (W2 - 2) _ (y1e t - G) (Afun (S t) + (S t + 1)) W2 ltac:(unfold W2; lia)); try lia.
      all: unfold W2, W0; lia.
Qed.

End Part_Close12.
Import Part_Close12.

Module Part_Close13.

Local Open Scope N_scope.

Lemma pc_pos : forall x, x <> 0 -> (1 <= pc x)%nat.
Proof. intros [|p] H; [contradiction|]. simpl. induction p; simpl; lia. Qed.

Lemma pc_ge2 : forall W, W <> 0 -> (forall x, W <> pw x) -> (2 <= pc W)%nat.
Proof.
  intros W H0 Hp. destruct (N_tz W H0) as [t [C HC]].
  assert (E : pc W = S (pc C)).
  { rewrite HC. pose proof (pc_split t 0 (2 * C + 1) ltac:(pose proof (pw_pos t); lia)) as H.
    replace (0 + pw t * (2 * C + 1)) with (pw t * (2 * C + 1)) in H by lia.
    rewrite H, pc_double1. reflexivity. }
  assert (HC0 : C <> 0).
  { intros E0. apply (Hp t). rewrite HC, E0. lia. }
  pose proof (pc_pos C HC0). lia.
Qed.

Lemma pc_rhs : forall a b theta, (theta = 0 \/ exists x, theta = pw x) -> (pc (pw a + pw b + theta) <= 3)%nat.
Proof.
  intros a b theta [H|[x H]]; subst theta.
  - replace (pw a + pw b + 0) with (pw a + pw b) by lia. pose proof (pc_two a b). lia.
  - apply pc_three.
Qed.

(* The middle term W *)
Lemma W_bounds : forall a3 Lam Sv W, (Lam <= a3 + 1)%nat -> Sv <> 0 -> Sv < pw a3 ->
  W + pw Lam = 3 * pw a3 + Sv ->
  pw a3 < W /\ W < 4 * pw a3 /\ (forall x, W <> pw x).
Proof.
  intros a3 Lam Sv W H1 H2 H3 H4.
  pose proof (pw_pos Lam) as P0.
  assert (HL : pw Lam = 2 * pw a3 /\ W = pw a3 + Sv \/ pw Lam = pw a3 /\ W = 2 * pw a3 + Sv \/
               2 * pw Lam <= pw a3 /\ 2 * pw a3 < W).
  { destruct (Nat.lt_trichotomy Lam a3) as [E|[E|E]].
    - right; right. pose proof (pw_lt Lam a3 E). lia.
    - right; left. subst Lam. lia.
    - left. assert (E2 : Lam = S a3) by lia. subst Lam. rewrite pw_S in *. lia. }
  assert (HR : pw a3 < W /\ W < 4 * pw a3) by lia.
  split; [lia|]. split; [lia|].
  intros x E.
  destruct (Nat.lt_ge_cases a3 x) as [X|X].
  - destruct (Nat.eq_dec x (S a3)) as [X2|X2].
    + subst x. rewrite pw_S in E. lia.
    + pose proof (pw_le (S (S a3)) x ltac:(lia)) as P. rewrite !pw_S in P. lia.
  - pose proof (pw_le x a3 X). lia.
Qed.

Lemma top_le : forall Lp Lam f a1 a2 a3 a4 Xl theta,
  pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta ->
  Xl < pw f -> (f <= Lam)%nat -> (a1 < a3)%nat -> (a3 + 3 <= a4)%nat -> (a4 <= Lp + 1)%nat.
Proof.
  intros Lp Lam f a1 a2 a3 a4 Xl theta HE H1 H2 H3 H4.
  destruct (Nat.le_gt_cases a4 (Lp + 1)) as [H|H]; [exact H|exfalso].
  pose proof (pw_lt (Lp + 1) a4 H) as P1.
  pose proof (pw_le (a3 + 3) a4 H4) as P2. rewrite pw_add in P2. change (pw 3) with 8 in P2.
  pose proof (pw_lt a1 a3 H3) as P3.
  pose proof (pw_le f Lam H2) as P4.
  lia.
Qed.

(* A low start of the run is impossible: too many ones *)
Lemma lam_le : forall Lam Lp f a a1 a2 a3 a4 Xl theta,
  pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta ->
  (theta = 0 \/ exists x, theta = pw x) ->
  (Lam + 3 <= Lp + 1)%nat -> Xl < pw f -> Lam = (f + a)%nat -> (26 <= a)%nat -> (a1 < a3)%nat ->
  (Lam <= a3 + 1)%nat.
Proof.
  intros Lam Lp f a a1 a2 a3 a4 Xl theta HE Hth H1 H2 H3 H4 H5.
  destruct (Nat.le_gt_cases Lam (a3 + 1)) as [H|H]; [exact H|exfalso].
  pose proof (pw_lt a1 a3 H5) as P3.
  pose proof (pw_le (a3 + 2) Lam ltac:(lia)) as P2. rewrite pw_add_r2 in P2.
  pose proof (pw_le (f + 4) Lam ltac:(lia)) as P4. rewrite pw_add in P4. change (pw 4) with 16 in P4.
  pose proof (pw_pos a1) as P5.
  set (inner := Xl + 3 * pw a3 + pw a1) in *.
  assert (Hin : inner < pw Lam) by (unfold inner; lia).
  pose proof (pw_split Lam (Lp + 1) ltac:(lia)) as S1.
  pose proof (pw_pos (Lp + 1 - Lam)) as P6.
  assert (Hw : exists w, pw (Lp + 1 - Lam) = w + 1 /\ w = pw (Lp + 1 - Lam) - 1) by (exists (pw (Lp + 1 - Lam) - 1); lia).
  destruct Hw as [w [Ew Ew2]].
  rewrite Ew in S1. rewrite N.mul_add_distr_l, N.mul_1_r in S1.
  assert (E2 : inner + pw Lam * w = pw a4 + pw a2 + theta) by (unfold inner in *; lia).
  pose proof (pc_split Lam inner w Hin) as PC.
  rewrite E2 in PC. rewrite Ew2, pc_ones_n in PC.
  pose proof (pc_rhs a4 a2 theta Hth) as PR.
  assert (Hne : inner <> 0) by (unfold inner; lia).
  pose proof (pc_pos inner Hne) as PP. lia.
Qed.

End Part_Close13.
Import Part_Close13.

Module Part_Close14.

Local Open Scope N_scope.

Lemma shape_C : forall Lp a2 a3 a4 W theta, (theta = 0 \/ exists x, theta = pw x) ->
  pw (Lp + 1) + W = pw a4 + pw a2 + theta -> (a3 + 2 <= a2)%nat -> (a3 + 2 <= a4)%nat -> (a3 + 2 <= Lp + 1)%nat ->
  W <> 0 -> W < 4 * pw a3 -> (forall x, W <> pw x) -> False.
Proof.
  intros Lp a2 a3 a4 W theta Hth HE H1 H2 H3 H0 H4 Hnp.
  pose proof (pw_add_r2 a3) as M.
  pose proof (pw_split _ _ H1) as S1. pose proof (pw_split _ _ H2) as S2. pose proof (pw_split _ _ H3) as S3.
  rewrite S1, S2, S3 in HE. rewrite <- M in H4.
  pose proof (pw_pos (a3 + 2)) as P9.
  destruct Hth as [E|[x E]]; subst theta.
  - assert (E2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W = (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2))) * pw (a3 + 2) + 0) by lia.
    destruct (mod_uniq (pw (a3 + 2)) _ _ W 0 H4 ltac:(lia) E2) as [_ E3]. contradiction.
  - destruct (Nat.lt_ge_cases x (a3 + 2)) as [X|X].
    + pose proof (pw_lt x (a3 + 2) X) as P. pose proof (pw_pos x) as P0.
      assert (E2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W = (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2))) * pw (a3 + 2) + pw x) by lia.
      destruct (mod_uniq (pw (a3 + 2)) _ _ W (pw x) H4 ltac:(lia) E2) as [_ E3]. apply (Hnp x E3).
    + pose proof (pw_split (a3 + 2) x X) as S4.
      assert (E2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W = (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2)) + pw (x - (a3 + 2))) * pw (a3 + 2) + 0) by lia.
      destruct (mod_uniq (pw (a3 + 2)) _ _ W 0 H4 ltac:(lia) E2) as [_ E3]. contradiction.
Qed.

Lemma a4_eq : forall Lp a2 a3 a4 W theta, (theta = 0 \/ exists x, theta = pw x) ->
  pw (Lp + 1) + W = pw a4 + pw a2 + theta -> (a4 <= Lp + 1)%nat -> (a3 + 3 <= a4)%nat -> (a2 <= a3 + 1)%nat ->
  W <> 0 -> W < 4 * pw a3 -> (forall x, W <> pw x) -> a4 = (Lp + 1)%nat.
Proof.
  intros Lp a2 a3 a4 W theta Hth HE H1 H2 H3 H0 H4 Hnp.
  destruct (Nat.eq_dec a4 (Lp + 1)) as [E|E]; [exact E|exfalso].
  assert (EL : pw (Lp + 1) = 2 * pw Lp) by (replace (Lp + 1)%nat with (S Lp) by lia; apply pw_S).
  pose proof (pw_le (a3 + 3) Lp ltac:(lia)) as P1. rewrite pw_add in P1. change (pw 3) with 8 in P1.
  pose proof (pw_le a4 Lp ltac:(lia)) as P2.
  pose proof (pw_le a2 (a3 + 1) H3) as P3.
  assert (EA : pw (a3 + 1) = 2 * pw a3) by (replace (a3 + 1)%nat with (S a3) by lia; apply pw_S).
  pose proof (pw_le (a3 + 3) a4 H2) as P4. rewrite pw_add in P4. change (pw 3) with 8 in P4.
  destruct Hth as [Et|[x Et]]; subst theta.
  - lia.
  - destruct (Nat.lt_trichotomy x Lp) as [X|[X|X]].
    + pose proof (pw_lt x Lp X). lia.
    + subst x. destruct (Nat.eq_dec a4 Lp) as [X|X].
      * subst a4. apply (Hnp a2). lia.
      * pose proof (pw_lt a4 Lp ltac:(lia)). lia.
    + destruct (Nat.eq_dec x (Lp + 1)) as [X2|X2].
      * subst x. lia.
      * pose proof (pw_le (Lp + 2) x ltac:(lia)) as P5. rewrite pw_add in P5. change (pw 2) with 4 in P5. lia.
Qed.

Lemma low_case : forall Lam a1 a2 a3 f x Xl W, (Lam < a3)%nat -> Xl <> 0 -> Xl < pw f -> (f + 4 <= Lam)%nat ->
  W + pw Lam = 3 * pw a3 + (Xl + pw a1) -> W = pw a2 + pw x -> (a2 <= a3 + 1)%nat -> Xl + pw a1 < pw a3 -> False.
Proof.
  intros Lam a1 a2 a3 f x Xl W H1 H2 H3 H4 H5 H6 H7 H8.
  pose proof (pw_lt Lam a3 H1) as P1.
  assert (E2 : pw (S a3) = 2 * pw a3) by apply pw_S.
  assert (Hc : exists c, W = 2 * pw a3 + pw c).
  { destruct (Nat.le_gt_cases (S (S a3)) x) as [X|X].
    - pose proof (pw_le _ _ X) as P. rewrite pw_S, E2 in P. lia.
    - destruct (Nat.eq_dec a2 (S a3)) as [A|A].
      + subst a2. exists x. lia.
      + destruct (Nat.eq_dec x (S a3)) as [B|B].
        * subst x. exists a2. lia.
        * exfalso. pose proof (pw_le a2 a3 ltac:(lia)). pose proof (pw_le x a3 ltac:(lia)). lia. }
  destruct Hc as [c Ec].
  assert (Ec3 : c = a3).
  { destruct (Nat.lt_trichotomy c a3) as [X|[X|X]].
    - exfalso. pose proof (pw_lt c a3 X). lia.
    - exact X.
    - exfalso. pose proof (pw_lt a3 c X). lia. }
  subst c.
  assert (E3 : Xl + pw a1 = pw Lam) by lia.
  pose proof (pw_lt_inv a1 Lam ltac:(lia)) as X.
  pose proof (pw_lt a1 Lam X) as P2.
  pose proof (pw_le (f + 4) Lam H4) as P3. rewrite pw_add in P3. change (pw 4) with 16 in P3.
  lia.
Qed.

Lemma eq_case : forall a2 a3 x Sv W, W = 2 * pw a3 + Sv -> W = pw a2 + pw x -> (a2 <= a3 + 1)%nat ->
  Sv <> 0 -> Sv < pw a3 -> exists b, Sv = pw b /\ (b = a2 \/ a2 = a3 + 1)%nat.
Proof.
  intros a2 a3 x Sv W H1 H2 H3 H4 H5.
  assert (E2 : pw (S a3) = 2 * pw a3) by apply pw_S.
  destruct (Nat.eq_dec a2 (S a3)) as [A|A].
  - subst a2. exists x. split; [lia|right; lia].
  - destruct (Nat.le_gt_cases (S (S a3)) x) as [X|X].
    + exfalso. pose proof (pw_le _ _ X) as P. rewrite pw_S, E2 in P. lia.
    + destruct (Nat.eq_dec x (S a3)) as [B|B].
      * subst x. exists a2. split; [lia|left; lia].
      * exfalso. pose proof (pw_le a2 a3 ltac:(lia)). pose proof (pw_le x a3 ltac:(lia)). lia.
Qed.

Lemma eq1_case : forall a2 a3 x Sv W, W = pw a3 + Sv -> W = pw a2 + pw x -> (a2 <= a3 + 1)%nat ->
  Sv <> 0 -> Sv < pw a3 -> exists b, Sv = pw b /\ (b = a2 \/ a2 = a3)%nat.
Proof.
  intros a2 a3 x Sv W H1 H2 H3 H4 H5.
  assert (E2 : pw (S a3) = 2 * pw a3) by apply pw_S.
  assert (A1 : (a2 <= a3)%nat).
  { destruct (Nat.eq_dec a2 (S a3)) as [A|A]; [|lia]. subst a2. lia. }
  assert (A2 : (x <= a3)%nat).
  { destruct (Nat.le_gt_cases x a3) as [X|X]; [exact X|exfalso].
    pose proof (pw_le (S a3) x X). lia. }
  destruct (Nat.eq_dec a2 a3) as [A|A].
  - subst a2. exists x. split; [lia|right; reflexivity].
  - destruct (Nat.eq_dec x a3) as [B|B].
    + subst x. exists a2. split; [lia|left; reflexivity].
    + exfalso. pose proof (pw_lt a2 a3 ltac:(lia)). pose proof (pw_lt x a3 ltac:(lia)). lia.
Qed.

End Part_Close14.
Import Part_Close14.

Module Part_Close15.

Local Open Scope N_scope.

Lemma S_small : forall Lam f a a1 a3 Xl, (Lam <= a3 + 1)%nat -> Lam = (f + a)%nat -> (26 <= a)%nat -> (a1 < a3)%nat ->
  Xl < pw f -> Xl + pw a1 < pw a3.
Proof.
  intros Lam f a a1 a3 Xl H1 H2 H3 H4 H5.
  pose proof (pw_lt a1 a3 H4) as P1.
  pose proof (pw_le (f + 2) a3 ltac:(lia)) as P2. rewrite pw_add_r2 in P2.
  lia.
Qed.

Lemma core_even : forall Lp Lam f a a1 a2 a3 a4 Xl theta,
  pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta ->
  (theta = 0 \/ exists x, theta = pw x) ->
  (Lam + 3 <= Lp + 1)%nat -> Xl < pw f -> Lam = (f + a)%nat -> (26 <= a)%nat -> (a1 < a3)%nat -> (a3 + 3 <= a4)%nat -> Xl <> 0 ->
  a4 = (Lp + 1)%nat /\ (Lam = a3 + 1 \/ Lam = a3)%nat /\
  exists b, Xl + pw a1 = pw b /\ (b = a2 \/ a2 = a3 \/ a2 = a3 + 1)%nat.
Proof.
  intros Lp Lam f a a1 a2 a3 a4 Xl theta HE Hth H1 H2 H3 H4 H5 H6 H7.
  pose proof (top_le Lp Lam f a1 a2 a3 a4 Xl theta HE H2 ltac:(lia) H5 H6) as Ht.
  pose proof (lam_le Lam Lp f a a1 a2 a3 a4 Xl theta HE Hth H1 H2 H3 H4 H5) as Hl.
  pose proof (S_small Lam f a a1 a3 Xl Hl H3 H4 H5 H2) as HS.
  pose proof (pw_le Lam (S a3) ltac:(lia)) as PL. rewrite pw_S in PL.
  pose proof (pw_pos a1) as P0.
  set (Sv := Xl + pw a1) in *.
  set (W := 3 * pw a3 + Sv - pw Lam).
  assert (HW : W + pw Lam = 3 * pw a3 + Sv) by (unfold W; lia).
  assert (Sv0 : Sv <> 0) by (unfold Sv; lia).
  destruct (W_bounds a3 Lam Sv W Hl Sv0 HS HW) as [W1 [W2 Wnp]].
  assert (E3 : pw (Lp + 1) + W = pw a4 + pw a2 + theta) by (unfold Sv in *; lia).
  destruct (Nat.le_gt_cases (a3 + 2) a2) as [Sh|Sh].
  { exfalso. apply (shape_C Lp a2 a3 a4 W theta Hth E3 Sh ltac:(lia) ltac:(lia) ltac:(lia) W2 Wnp). }
  pose proof (a4_eq Lp a2 a3 a4 W theta Hth E3 Ht H6 ltac:(lia) ltac:(lia) W2 Wnp) as Ea.
  split; [exact Ea|].
  rewrite Ea in E3.
  assert (E4 : W = pw a2 + theta) by lia.
  destruct Hth as [Et|[x Et]].
  { exfalso. apply (Wnp a2). lia. }
  subst theta.
  destruct (Nat.lt_trichotomy Lam a3) as [X|[X|X]].
  - exfalso. apply (low_case Lam a1 a2 a3 f x Xl W X H7 H2 ltac:(lia) HW E4 ltac:(lia) HS).
  - split; [right; exact X|].
    destruct (eq_case a2 a3 x Sv W ltac:(rewrite X in HW; lia) E4 ltac:(lia) Sv0 HS) as [b [Eb Hb]].
    exists b. split; [exact Eb|]. lia.
  - split; [left; lia|].
    assert (E5 : Lam = S a3) by lia.
    destruct (eq1_case a2 a3 x Sv W ltac:(rewrite E5, pw_S in HW; lia) E4 ltac:(lia) Sv0 HS) as [b [Eb Hb]].
    exists b. split; [exact Eb|]. lia.
Qed.

Lemma core_odd : forall Lp Lam f a a1 a2 a3 a4 Xl theta,
  pw Lp + pw (Lp - 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta ->
  (theta = 0 \/ exists x, theta = pw x) ->
  (Lam + 3 <= Lp - 1)%nat -> Xl < pw f -> Lam = (f + a)%nat -> (26 <= a)%nat -> (a1 < a3)%nat -> (a3 + 3 <= a4)%nat ->
  (a4 = a3 + 3 -> a2 <= a3 -> a3 < 28)%nat -> False.
Proof.
  intros Lp Lam f a a1 a2 a3 a4 Xl theta HE Hth H1 H2 H3 H4 H5 H6 Hcoll.
  assert (EL : pw Lp = 2 * pw (Lp - 1)) by (apply pw_pred2; lia).
  pose proof (pw_lt a1 a3 H5) as P1.
  pose proof (pw_le (a3 + 3) a4 H6) as P2. rewrite pw_add in P2. change (pw 3) with 8 in P2.
  pose proof (pw_le f Lam ltac:(lia)) as P3.
  pose proof (pw_pos a1) as P0.
  assert (Ht : (a4 <= Lp + 1)%nat).
  { destruct (Nat.le_gt_cases a4 (Lp + 1)) as [H|H]; [exact H|exfalso].
    pose proof (pw_le (Lp + 2) a4 ltac:(lia)) as P4. rewrite pw_add in P4. change (pw 2) with 4 in P4.
    lia. }
  assert (Hl : (Lam <= a3 + 1)%nat).
  { destruct (Nat.le_gt_cases Lam (a3 + 1)) as [H|H]; [exact H|exfalso].
    pose proof (pw_le (a3 + 2) Lam ltac:(lia)) as P4. rewrite pw_add_r2 in P4.
    pose proof (pw_le (f + 4) Lam ltac:(lia)) as P5. rewrite pw_add in P5. change (pw 4) with 16 in P5.
    set (inner := Xl + 3 * pw a3 + pw a1) in *.
    assert (Hin : inner < pw Lam) by (unfold inner; lia).
    pose proof (pw_split Lam (Lp - 1) ltac:(lia)) as S1.
    pose proof (pw_pos (Lp - 1 - Lam)) as P6.
    assert (Hw : exists w, pw (Lp - 1 - Lam) = w + 1 /\ w = pw (Lp - 1 - Lam) - 1) by (exists (pw (Lp - 1 - Lam) - 1); lia).
    destruct Hw as [w [Ew Ew2]].
    rewrite Ew in S1. rewrite N.mul_add_distr_l, N.mul_1_r in S1.
    assert (Hx0 : inner + pw Lam * w < pw Lp) by lia.
    assert (E2 : (inner + pw Lam * w) + pw Lp * 1 = pw a4 + pw a2 + theta) by (unfold inner in *; lia).
    pose proof (pc_split Lam inner w Hin) as PC1.
    pose proof (pc_split Lp _ 1 Hx0) as PC2.
    rewrite E2, PC1 in PC2. rewrite Ew2, pc_ones_n in PC2.
    change (pc 1) with 1%nat in PC2.
    pose proof (pc_rhs a4 a2 theta Hth) as PR.
    assert (Hne : inner <> 0) by (unfold inner; lia).
    pose proof (pc_pos inner Hne) as PP. lia. }
  pose proof (S_small Lam f a a1 a3 Xl Hl H3 H4 H5 H2) as HS.
  pose proof (pw_le Lam (S a3) ltac:(lia)) as PL. rewrite pw_S in PL.
  set (Sv := Xl + pw a1) in *.
  set (W := 3 * pw a3 + Sv - pw Lam).
  assert (HW : W + pw Lam = 3 * pw a3 + Sv) by (unfold W; lia).
  assert (Sv0 : Sv <> 0) by (unfold Sv; lia).
  destruct (W_bounds a3 Lam Sv W Hl Sv0 HS HW) as [W1 [W2 Wnp]].
  assert (E3 : pw Lp + pw (Lp - 1) + W = pw a4 + pw a2 + theta) by (unfold Sv in *; lia).
  destruct (Nat.le_gt_cases (a3 + 2) (Lp - 1)) as [C|C].
  - pose proof (pw_le (a3 + 2) (Lp - 1) C) as P4. rewrite pw_add_r2 in P4.
    assert (E5 : W + pw (Lp - 1) * 3 = pw a4 + pw a2 + theta) by lia.
    pose proof (pc_split (Lp - 1) W 3 ltac:(lia)) as PC.
    rewrite E5 in PC. change (pc 3) with 2%nat in PC.
    pose proof (pc_rhs a4 a2 theta Hth) as PR.
    pose proof (pc_ge2 W ltac:(lia) Wnp) as PG. lia.
  - assert (E6 : Lp = (a3 + 2)%nat) by lia. subst Lp.
    assert (E7 : a4 = (a3 + 3)%nat) by lia. subst a4.
    replace (a3 + 2 - 1)%nat with (S a3) in * by lia.
    rewrite pw_add_r2 in E3. rewrite pw_S in E3.
    assert (Ha2 : pw a2 < pw (S a3)) by (rewrite pw_S; lia).
    pose proof (pw_lt_inv a2 (S a3) Ha2) as Ha3.
    pose proof (Hcoll eq_refl ltac:(lia)) as Hc. lia.
Qed.

End Part_Close15.
Import Part_Close15.

Module Part_Close16.

Local Open Scope N_scope.

Lemma y1o_add : forall t r, y1o t r + 3 * pw (Apr r + Afun (S t)) + pw (Apr r - 1) =
  pw (Apr r + Afun (S t) + (S t + 2)) + pw (Apr r + r + 1).
Proof.
  intros t r. rewrite y1o_split, Yc_exact. unfold Ya.
  rewrite (pw_add (Apr r + Afun (S t)) (S t + 2)).
  pose proof (Apr_pos r) as Ha.
  pose proof (pw_lt (Apr r - 1) (Apr r + r + 1) ltac:(lia)) as P.
  assert (Hw : exists w, pw (S t + 2) = w + 3).
  { exists (pw (S t + 2) - 3). rewrite pw_add_r2. pose proof (pw_pos (S t)). lia. }
  destruct Hw as [w Ew]. rewrite Ew. replace (w + 3 - 3) with w by lia.
  rewrite N.mul_add_distr_l. lia.
Qed.

(* The low digits of a number with a known top *)
Lemma split_Z : forall Z t C q C1 un p0 v f, Z = pw t * (2 * C + 1) -> C = pw q * (2 * C1 + 1) ->
  Z + pw p0 = pw un + v -> v <> 0 -> v < pw f -> (forall x, v <> pw x) -> (f <= p0)%nat -> (p0 <= un)%nat ->
  (t + q + 2 <= f)%nat /\
  exists Xl, v = pw t + pw (t + S q) + pw (S (t + S q)) * Xl /\
    C1 + pw (p0 - S (t + S q)) = pw (un - S (t + S q)) + Xl /\ Xl < pw (f - S (t + S q)).
Proof.
  intros Z t C q C1 un p0 v f HZ HC HE H0 Hv Hnp H1 H2.
  pose proof (pw_split f un ltac:(lia)) as S1. pose proof (pw_split f p0 H1) as S2.
  pose proof (pw_le (p0 - f) (un - f) ltac:(lia)) as P1.
  assert (Ht : (t + q + 2 <= f)%nat).
  { apply (second_bit (pw (un - f) - pw (p0 - f)) v f t C q C1 H0 Hv Hnp); [|exact HC].
    rewrite N.mul_sub_distr_r. rewrite <- HZ.
    rewrite S1, S2 in HE. rewrite (N.mul_comm (pw (un - f))), (N.mul_comm (pw (p0 - f))).
    assert (P2 : pw f * pw (p0 - f) <= pw f * pw (un - f)) by (apply N.mul_le_mono_l; exact P1).
    lia. }
  split; [exact Ht|].
  set (p2 := (t + S q)%nat) in *.
  assert (HZ2 : Z = pw t + pw p2 + 2 * pw p2 * C1).
  { rewrite HZ, HC. unfold p2. rewrite (pw_add t (S q)), pw_S. lia. }
  assert (M : pw (S p2) = 2 * pw p2) by apply pw_S.
  pose proof (pw_lt t p2 ltac:(unfold p2; lia)) as P3.
  pose proof (pw_pos t) as P4.
  assert (M0 : pw (S p2) <> 0) by (pose proof (pw_pos (S p2)); lia).
  pose proof (N.div_mod v (pw (S p2)) M0) as Dv.
  pose proof (N.mod_lt v (pw (S p2)) M0) as Mv.
  set (Xl := v / pw (S p2)) in *. set (rr := v mod pw (S p2)) in *.
  pose proof (pw_split (S p2) un ltac:(unfold p2; lia)) as S3.
  pose proof (pw_split (S p2) p0 ltac:(unfold p2; lia)) as S4.
  assert (E2 : (C1 + pw (p0 - S p2)) * pw (S p2) + (pw t + pw p2) = (pw (un - S p2) + Xl) * pw (S p2) + rr).
  { rewrite S3, S4 in HE. rewrite HZ2 in HE. rewrite M in *. lia. }
  destruct (mod_uniq (pw (S p2)) (C1 + pw (p0 - S p2)) (pw (un - S p2) + Xl) (pw t + pw p2) rr ltac:(lia) Mv E2) as [E3 E4].
  exists Xl. split; [lia|]. split; [exact E3|].
  destruct (N.lt_ge_cases Xl (pw (f - S p2))) as [X|X]; [exact X|exfalso].
  pose proof (pw_split (S p2) f ltac:(unfold p2; lia)) as S5.
  assert (P5 : pw (S p2) * pw (f - S p2) <= pw (S p2) * Xl) by (apply N.mul_le_mono_l; exact X).
  lia.
Qed.

(* v lies between 5/2 and 7/2 powers of U0 *)
Lemma v_np : forall v U0, 5 * pw U0 < 2 * v -> 2 * v < 7 * pw U0 -> (forall x, v <> pw x).
Proof.
  intros v U0 H1 H2 x E. subst v.
  destruct (Nat.le_gt_cases x (S U0)) as [X|X].
  - destruct (Nat.eq_dec x (S U0)) as [X2|X2].
    + subst x. rewrite pw_S in *. lia.
    + pose proof (pw_le x U0 ltac:(lia)). lia.
  - pose proof (pw_le (S (S U0)) x X) as P. rewrite !pw_S in P. lia.
Qed.

Lemma Xl_ne : forall v U0 t' p2 R j Xl, 5 * pw U0 < 2 * v -> 2 * v < 7 * pw U0 ->
  v = pw t' + pw p2 + pw (S p2) * Xl -> p2 = (t' + S R)%nat -> R = (2 * j + 1)%nat -> Xl <> 0.
Proof.
  intros v U0 t' p2 R j Xl H1 H2 Hv Hp HR E. subst Xl.
  replace (pw (S p2) * 0) with 0 in Hv by lia.
  pose proof (pw_lt t' p2 ltac:(lia)) as P1.
  pose proof (pw_pos t') as P0.
  assert (Ep : p2 = S U0).
  { destruct (Nat.lt_trichotomy p2 (S U0)) as [X|[X|X]].
    - exfalso. pose proof (pw_le p2 U0 ltac:(lia)). lia.
    - exact X.
    - exfalso. pose proof (pw_le (S (S U0)) p2 X) as P. rewrite !pw_S in P. lia. }
  rewrite Ep, pw_S in Hv.
  assert (Et : t' = U0).
  { destruct (Nat.lt_trichotomy t' U0) as [X|[X|X]].
    - exfalso. pose proof (pw_lt t' U0 X). lia.
    - exact X.
    - lia. }
  lia.
Qed.

Lemma block : forall v U0 t' p2 Xl a1 b, 5 * pw U0 < 2 * v -> 2 * v < 7 * pw U0 ->
  v = pw t' + pw p2 + pw (S p2) * Xl -> (t' < p2)%nat -> Xl <> 0 -> Xl + pw a1 = pw b ->
  (a1 < b)%nat /\ (b <= a1 + 2)%nat /\ (p2 + b = U0 + 1)%nat.
Proof.
  intros v U0 t' p2 Xl a1 b H1 H2 Hv Ht H0 Eb.
  assert (Hab : (a1 < b)%nat) by (apply pw_lt_inv; lia).
  split; [exact Hab|].
  pose proof (pw_lt t' p2 Ht) as P1. pose proof (pw_pos t') as P0.
  assert (M : pw (S p2) = 2 * pw p2) by apply pw_S.
  assert (EMb : pw (S p2) * Xl + pw (S p2 + a1) = pw (S p2 + b)).
  { rewrite (pw_add (S p2) a1), (pw_add (S p2) b), <- Eb. lia. }
  pose proof (pw_lt (S p2 + a1) (S p2 + b) ltac:(lia)) as P2.
  pose proof (pw_le (S p2) (S p2 + a1) ltac:(lia)) as P3.
  set (MX := pw (S p2) * Xl) in *.
  assert (Hs : (S p2 + b = U0 + 2)%nat).
  { destruct (Nat.lt_trichotomy (S p2 + b) (U0 + 2)) as [X|[X|X]].
    - exfalso. pose proof (pw_le (S p2 + b) (S U0) ltac:(lia)) as P. rewrite pw_S in P. lia.
    - exact X.
    - exfalso. pose proof (pw_le (U0 + 3) (S p2 + b) ltac:(lia)) as P. rewrite pw_add in P. change (pw 3) with 8 in P. lia. }
  split; [|lia].
  destruct (Nat.le_gt_cases b (a1 + 2)) as [X|X]; [exact X|exfalso].
  pose proof (pw_le (S p2 + a1 + 3) (S p2 + b) ltac:(lia)) as P4. rewrite (pw_add (S p2 + a1) 3) in P4. change (pw 3) with 8 in P4.
  rewrite Hs in *. rewrite pw_add_r2 in EMb, P4.
  lia.
Qed.

Lemma sizes_even : forall m R r a h U0 Lam b A' Ap' A Ap,
  (5 * m <= 2 * A' <= 5 * m + 1)%nat -> (5 * R + 1 <= 2 * Ap' <= 5 * R + 2)%nat ->
  (5 * a <= 2 * A <= 5 * a + 1)%nat -> (5 * r + 1 <= 2 * Ap <= 5 * r + 2)%nat -> U0 = (Ap + A)%nat ->
  (Ap' + A' + (m + 2) + (m + R) = U0 + a + h + 1)%nat ->
  (Lam + (m + R) + 1 = U0 + a + 2)%nat -> (Lam = Ap' + A' + 1 \/ Lam = Ap' + A')%nat ->
  (m + R + b = U0 + 1)%nat -> (Ap' - 1 < b)%nat -> (b <= Ap' - 1 + 2)%nat -> (1 <= Ap')%nat ->
  (R + 1 = A' \/ R = A')%nat -> (r + 3 <= h)%nat -> (26 <= a)%nat -> False.
Proof. intros. lia. Qed.

End Part_Close16.
Import Part_Close16.

Module Part_Close17.

Local Open Scope N_scope.

Lemma v_bounds : forall t r G1 v, v + pw (Apr r + r + 1) = G1 + 3 * pw (Apr r + Afun (S t)) + pw (Apr r - 1) ->
  2 * G1 < pw (Apr r + Afun (S t)) -> (r + 2 <= Afun (S t))%nat ->
  5 * pw (Apr r + Afun (S t)) < 2 * v /\ 2 * v < 7 * pw (Apr r + Afun (S t)).
Proof.
  intros t r G1 v H1 H2 H3.
  pose proof (pw_lt (Apr r + r + 1) (Apr r + Afun (S t)) ltac:(lia)) as P1.
  pose proof (pw_le (Apr r - 1) (Apr r + r + 1) ltac:(lia)) as P2.
  pose proof (pw_pos (Apr r - 1)) as P3.
  lia.
Qed.

(* What the levels with a negative first difference share *)
Lemma low_setup : forall t r G1 Z un, Z + y1o t r = pw un + G1 ->
  2 * G1 < pw (Apr r + Afun (S t)) -> (r <= S t)%nat -> (26 <= S t)%nat ->
  exists v, Z + pw (Apr r + Afun (S t) + (S t + 2)) = pw un + v /\ v <> 0 /\ v < pw (Apr r + Afun (S t) + 2) /\
    5 * pw (Apr r + Afun (S t)) < 2 * v /\ 2 * v < 7 * pw (Apr r + Afun (S t)) /\
    (forall x, v <> pw x).
Proof.
  intros t r G1 Z un HZ H1 H2 H3.
  pose proof (Afun_bd (S t)) as BA.
  pose proof (pw_lt (Apr r + r + 1) (Apr r + Afun (S t)) ltac:(lia)) as P1.
  pose proof (y1o_add t r) as Y.
  set (v := G1 + 3 * pw (Apr r + Afun (S t)) + pw (Apr r - 1) - pw (Apr r + r + 1)).
  assert (Hv : v + pw (Apr r + r + 1) = G1 + 3 * pw (Apr r + Afun (S t)) + pw (Apr r - 1)) by (unfold v; lia).
  destruct (v_bounds t r G1 v Hv H1 ltac:(lia)) as [B1 B2].
  pose proof (pw_add_r2 (Apr r + Afun (S t))) as P2.
  exists v. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B1|]. split; [exact B2|].
  exact (v_np v _ B1 B2).
Qed.

Lemma short_B : forall t r G1 h t' C' q C1' c1' j Z theta u,
  Z = pw t' * (2 * C' + 1) -> C' = pw q * (2 * C1' + 1) -> q = (2 * j + 1)%nat -> u = (t' + S (q + S c1'))%nat ->
  u = (Apr r + Afun (S t) + S t + h + 1)%nat ->
  Z + y1o t r = pw u + G1 -> 2 * G1 < pw (Apr r + Afun (S t)) -> (r + 3 <= h)%nat -> (r <= S t)%nat -> (26 <= S t)%nat ->
  (theta = 0 \/ exists x, theta = pw x) -> C1' + pw c1' = y1o t' q + theta -> False.
Proof.
  intros t r G1 h t' C' q C1' c1' j Z theta u HZ HC Hq Hu1 Hu2 HE H1 H2 H3 H4 Hth HX.
  destruct (low_setup t r G1 Z u HE H1 H3 H4) as [v [HZv [V0 [Vf [B1 [B2 Vn]]]]]].
  destruct (split_Z Z t' C' q C1' u _ v _ HZ HC HZv V0 Vf Vn ltac:(lia) ltac:(lia)) as [Ht [Xl [Hv [HC1 HXl]]]].
  pose proof (Xl_ne v _ t' (t' + S q) q j Xl B1 B2 Hv eq_refl Hq) as Xn.
  pose proof (y1o_add t' q) as Y.
  pose proof (pw_S c1') as P1.
  replace (u - S (t' + S q))%nat with c1' in HC1 by lia.
  set (Lam := (Apr r + Afun (S t) + (S t + 2) - S (t' + S q))%nat) in *.
  assert (HE2 : pw (c1' + 1) + Xl + 3 * pw (Apr q + Afun (S t')) + pw (Apr q - 1) =
    pw (Apr q + Afun (S t') + (S t' + 2)) + pw (Apr q + q + 1) + pw Lam + theta).
  { replace (c1' + 1)%nat with (S c1') by lia. lia. }
  pose proof (Apr_pos q) as Pq. pose proof (Afun_pos t') as Pa.
  destruct (core_even c1' Lam (Apr r + Afun (S t) + 2 - S (t' + S q)) (S t) (Apr q - 1) (Apr q + q + 1)
     (Apr q + Afun (S t')) (Apr q + Afun (S t') + (S t' + 2)) Xl theta HE2 Hth ltac:(unfold Lam; lia) HXl
     ltac:(unfold Lam; lia) H4 ltac:(lia) ltac:(lia) Xn) as [Ea [Hlam [b [Eb Hb]]]].
  destruct (block v _ t' (t' + S q) Xl (Apr q - 1) b B1 B2 Hv ltac:(lia) Xn Eb) as [Bb [Bc Bd]].
  destruct Hb as [Hb|Hb].
  - lia.
  - apply (sizes_even (S t') q r (S t) h (Apr r + Afun (S t)) Lam b (Afun (S t')) (Apr q) (Afun (S t)) (Apr r)).
    + apply Afun_bd.
    + apply Apr_bd.
    + apply Afun_bd.
    + apply Apr_bd.
    + reflexivity.
    + lia.
    + unfold Lam; lia.
    + exact Hlam.
    + lia.
    + exact Bb.
    + exact Bc.
    + exact Pq.
    + lia.
    + exact H2.
    + exact H4.
Qed.

Lemma hcoll : forall t' j, (Apr (2 * j + 1) + Afun (S t') + (S t' + 2) = Apr (2 * j + 1) + Afun (S t') + 3)%nat ->
  (Apr (2 * j + 1) + (2 * j + 1) + 1 <= Apr (2 * j + 1) + Afun (S t'))%nat -> (Apr (2 * j + 1) + Afun (S t') < 28)%nat.
Proof.
  intros t' j H1 H2. assert (E : t' = 0%nat) by lia. subst t'.
  change (Afun 1) with 3%nat in *. assert (Ej : j = 0%nat) by lia. subst j.
  change (Apr (2 * 0 + 1)) with 3%nat. lia.
Qed.

Lemma short_C : forall t r G1 h t' C' q C1' c1' j Z theta u,
  Z = pw t' * (2 * C' + 1) -> C' = pw q * (2 * C1' + 1) -> q = (2 * j + 1)%nat -> u = (t' + S (q + S c1'))%nat ->
  u = (Apr r + Afun (S t) + S t + h + 3)%nat ->
  Z + y1o t r = pw (u - 1) + G1 -> 2 * G1 < pw (Apr r + Afun (S t)) -> (r + 3 <= h)%nat -> (r <= S t)%nat -> (26 <= S t)%nat ->
  (theta = 0 \/ exists x, theta = pw x) -> C1' + pw c1' = y1o t' q + theta -> False.
Proof.
  intros t r G1 h t' C' q C1' c1' j Z theta u HZ HC Hq Hu1 Hu2 HE H1 H2 H3 H4 Hth HX.
  destruct (low_setup t r G1 Z (u - 1) HE H1 H3 H4) as [v [HZv [V0 [Vf [B1 [B2 Vn]]]]]].
  destruct (split_Z Z t' C' q C1' (u - 1) _ v _ HZ HC HZv V0 Vf Vn ltac:(lia) ltac:(lia)) as [Ht [Xl [Hv [HC1 HXl]]]].
  pose proof (y1o_add t' q) as Y.
  replace (u - 1 - S (t' + S q))%nat with (c1' - 1)%nat in HC1 by lia.
  set (Lam := (Apr r + Afun (S t) + (S t + 2) - S (t' + S q))%nat) in *.
  assert (HE2 : pw c1' + pw (c1' - 1) + Xl + 3 * pw (Apr q + Afun (S t')) + pw (Apr q - 1) =
    pw (Apr q + Afun (S t') + (S t' + 2)) + pw (Apr q + q + 1) + pw Lam + theta) by lia.
  pose proof (Apr_pos q) as Pq. pose proof (Afun_pos t') as Pa.
  apply (core_odd c1' Lam (Apr r + Afun (S t) + 2 - S (t' + S q)) (S t) (Apr q - 1) (Apr q + q + 1)
     (Apr q + Afun (S t')) (Apr q + Afun (S t') + (S t' + 2)) Xl theta HE2 Hth ltac:(unfold Lam; lia) HXl
     ltac:(unfold Lam; lia) H4 ltac:(lia) ltac:(lia)).
  subst q. apply hcoll.
Qed.

End Part_Close17.
Import Part_Close17.

Module Part_Close18.

Local Open Scope N_scope.

Lemma cell_lo : forall V c, cell1 V c -> pw c <= V.
Proof. intros V c [a [b [H1 H2]]]. lia. Qed.

Lemma ones_lt : forall V p q n, ones_on V p q -> V < pw n -> (p < q)%nat -> (q <= n)%nat.
Proof.
  intros V p q n H1 H2 H3.
  pose proof (cell_lo V (q - 1) (ones_cell V p q (q - 1) H1 ltac:(lia))) as P.
  destruct (Nat.le_gt_cases q n) as [X|X]; [exact X|exfalso].
  pose proof (pw_le n (q - 1) ltac:(lia)). lia.
Qed.

Lemma not_LR_335 : LR 335 -> False.
Proof.
  intros [p [q [Hrun Hr]]].
  destruct (Nat.le_gt_cases p 4) as [C|C].
  - destruct (ones_cell 335 p q 4 Hrun ltac:(lia)) as [a [b [H1 H2]]].
    change (pw 4) with 16 in *. change (pw (S 4)) with 32 in *. lia.
  - destruct (Nat.le_gt_cases p 7) as [D|D].
    + destruct (ones_cell 335 p q 7 Hrun ltac:(lia)) as [a [b [H1 H2]]].
      change (pw 7) with 128 in *. change (pw (S 7)) with 256 in *. lia.
    + pose proof (cell_lo 335 (S p) (ones_cell 335 p q (S p) Hrun ltac:(lia))) as P.
      pose proof (pw_le 9 (S p) ltac:(lia)) as P2. change (pw 9) with 512 in P2. lia.
Qed.

Lemma pc_top : forall Z P0 un v, Z + pw P0 = pw un + v -> v < pw P0 -> (P0 <= un)%nat ->
  pc Z = (pc v + (un - P0))%nat.
Proof.
  intros Z P0 un v H1 H2 H3.
  pose proof (pw_split P0 un H3) as S1.
  pose proof (pw_pos (un - P0)) as P.
  assert (Hw : exists w, pw (un - P0) = w + 1 /\ w = pw (un - P0) - 1) by (exists (pw (un - P0) - 1); lia).
  destruct Hw as [w [Ew Ew2]].
  rewrite Ew in S1. rewrite N.mul_add_distr_l, N.mul_1_r in S1.
  assert (E : Z = v + pw P0 * w) by lia.
  rewrite E, (pc_split P0 v w H2), Ew2, pc_ones_n. reflexivity.
Qed.

Lemma Z_form : forall Z P0 un v f, Z + pw P0 = pw un + v -> (f <= P0)%nat -> (P0 <= un)%nat ->
  Z = (pw (un - f) - pw (P0 - f)) * pw f + v.
Proof.
  intros Z P0 un v f H1 H2 H3.
  pose proof (pw_split f un ltac:(lia)) as S1. pose proof (pw_split f P0 H2) as S2.
  pose proof (pw_le (P0 - f) (un - f) ltac:(lia)) as P1.
  rewrite N.mul_sub_distr_r.
  rewrite S1, S2 in H1. rewrite (N.mul_comm (pw (un - f))), (N.mul_comm (pw (P0 - f))).
  assert (P2 : pw f * pw (P0 - f) <= pw f * pw (un - f)) by (apply N.mul_le_mono_l; exact P1).
  lia.
Qed.

(* A wide run on top of a number: the run, and a form with two ones at its start *)
Lemma long_Z : forall Z E p0 un, Z + E = pw un -> E <> 0 -> E < pw p0 -> (p0 + 2 <= un)%nat ->
  ones_on Z p0 un /\
  exists v, Z + pw (p0 + 2) = pw un + v /\ v <> 0 /\ v < pw (p0 + 2) /\ (forall x, v <> pw x).
Proof.
  intros Z E p0 un H1 H2 H3 H4.
  pose proof (pw_le p0 un ltac:(lia)) as P1.
  pose proof (pw_add_r2 p0) as P2.
  pose proof (pw_pos p0) as P3.
  split.
  - split; [lia|]. exists 0, (pw p0 - E). split; [lia|]. lia.
  - exists (4 * pw p0 - E). split; [lia|]. split; [lia|]. split; [lia|].
    intros x Ex.
    destruct (Nat.lt_trichotomy x (S p0)) as [X|[X|X]].
    + pose proof (pw_le x p0 ltac:(lia)). lia.
    + subst x. rewrite pw_S in Ex. lia.
    + pose proof (pw_le (S (S p0)) x X) as Q. rewrite !pw_S in Q. lia.
Qed.

End Part_Close18.
Import Part_Close18.

Module Part_Close19.

Local Open Scope N_scope.

(* A level whose number carries a run with the LR ratio *)
Lemma level_run : forall Z t' c' C' u p0 q0 h Zh v W, Z = pw t' * (2 * C' + 1) -> C' < pw c' -> u = (t' + S c')%nat ->
  ones_on Z p0 q0 -> (2 * p0 + 25 <= 5 * (q0 - p0))%nat -> (q0 <= u)%nat ->
  Z = Zh * pw h + v -> v <> 0 -> v < pw h -> (forall x, v <> pw x) -> (h + 9 <= u)%nat ->
  (S t' + c' + 1 <= W)%nat -> (W <= S t' + c' + 2)%nat -> (90 <= W)%nat ->
  (t' = 0%nat -> W = (S t' + c' + 1)%nat -> C' <> 167) ->
  Good (D1 (S t') (TL (bin c' C') (U B0)) W).
Proof.
  intros Z t' c' C' u p0 q0 h Zh v W HZ HC Hu Hrun Hr Hq0 HZv V0 Vl Vn Hh W1 W2 Wb H83.
  pose proof (pc_on Z p0 q0 Hrun) as PC.
  apply (good_Z Z t' c' C' W Zh v h HZ HC HZv V0 Vl Vn ltac:(lia) ltac:(lia) W1 W2 ltac:(lia) H83).
  intros k q c1 C1 j Hk HC1 Hc Hq.
  apply (N2_run Z u t' C' q C1 c1 j p0 q0 HZ HC1 Hq ltac:(lia) Hrun Hq0 Hr).
Qed.

(* A level with a negative first difference *)
Lemma level_low : forall t r G1 h Z t' c' C' u un W,
  Z = pw t' * (2 * C' + 1) -> C' < pw c' -> u = (t' + S c')%nat -> (un <= u)%nat ->
  (un = Apr r + Afun (S t) + (S t + 2) + (h - 1) \/ un = Apr r + Afun (S t) + (S t + 2) + h)%nat ->
  Z + y1o t r = pw un + G1 -> G1 < y1o t r -> G1 < pw h -> (r + 3 <= h)%nat -> (r <= S t)%nat -> (26 <= S t)%nat ->
  (S t' + c' + 1 <= W)%nat -> (W <= S t' + c' + 2)%nat -> (90 <= W)%nat ->
  (t' = 0%nat -> W = (S t' + c' + 1)%nat -> C' <> 167) ->
  (2 * G1 < pw (Apr r + Afun (S t)) -> forall q C1 c1 j theta, C' = pw q * (2 * C1 + 1) -> c' = (q + S c1)%nat ->
     q = (2 * j + 1)%nat -> (theta = 0 \/ exists x, theta = pw x) -> C1 + pw c1 = y1o t' q + theta -> False) ->
  Good (D1 (S t') (TL (bin c' C') (U B0)) W).
Proof.
  intros t r G1 h Z t' c' C' u un W HZ HC Hu Hun Hun2 HE Hlt HGh Hr Hra Ha W1 W2 Wb H83 Hshort.
  pose proof (Afun_bd (S t)) as BA.
  set (U0 := (Apr r + Afun (S t))%nat) in *.
  set (p0 := (U0 + (S t + 2))%nat) in *.
  destruct (N.lt_ge_cases (2 * G1) (pw U0)) as [Sh|Lg].
  - destruct (low_setup t r G1 Z un HE Sh Hra Ha) as [v [HZv [V0 [Vf [B1 [B2 Vn]]]]]].
    fold U0 p0 in HZv, Vf, B1, B2.
    pose proof (Z_form Z p0 un v (U0 + 2) HZv ltac:(unfold p0; lia) ltac:(lia)) as HZf.
    pose proof (pw_le (U0 + 2) p0 ltac:(unfold p0; lia)) as P1.
    pose proof (pc_top Z p0 un v HZv ltac:(lia) ltac:(lia)) as PC.
    pose proof (pc_pos v V0) as PV.
    apply (good_Z Z t' c' C' W _ v (U0 + 2) HZ HC HZf V0 Vf Vn ltac:(unfold U0 in *; lia) ltac:(lia) W1 W2 ltac:(lia) H83).
    intros k q c1 C1 j Hk HC1 Hc Hq. split.
    + intros E. apply (Hshort Sh q C1 c1 j 0 HC1 Hc Hq (or_introl eq_refl)). lia.
    + intros x E. apply (Hshort Sh q C1 c1 j (pw x) HC1 Hc Hq (or_intror (ex_intro _ x eq_refl)) E).
  - assert (Hh : (U0 <= h)%nat).
    { destruct (Nat.le_gt_cases U0 h) as [X|X]; [exact X|exfalso].
      pose proof (pw_lt h U0 X). lia. }
    pose proof (y1o_lt4 t r ltac:(lia)) as Y4. fold U0 p0 in Y4.
    pose proof (Apr_pos r) as Pa.
    destruct (long_Z Z (y1o t r - G1) p0 un ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold p0, U0 in *; lia)) as [Hrun [v [HZv [V0 [Vf Vn]]]]].
    pose proof (Z_form Z (p0 + 2) un v (p0 + 2) HZv ltac:(lia) ltac:(unfold p0, U0 in *; lia)) as HZf.
    apply (level_run Z t' c' C' u p0 un (p0 + 2) _ v W HZ HC Hu Hrun ltac:(unfold p0, U0 in *; lia) Hun HZf V0 Vf Vn ltac:(unfold p0, U0 in *; lia) W1 W2 Wb H83).
Qed.

End Part_Close19.
Import Part_Close19.

Module Part_Close20.

Local Open Scope N_scope.

(* A step from a state with e = 0, a odd, r even *)
Lemma step_odd_even : forall t k h G j G1, S t = (2 * k + 1)%nat -> (26 <= S t)%nat ->
  pw (h - 2) <= G -> G < pw h -> G = pw (2 * j) * (2 * G1 + 1) -> (2 * j + 3 <= h)%nat -> (2 * j <= S t)%nat ->
  (y1o t (2 * j) <= G1 -> LR (G1 - y1o t (2 * j))) ->
  Good (F0 (S t) h (pw h - 1 - G)).
Proof.
  intros t k h G j G1 Hk Ha Hlo Hhi HG Hr Hra Hd.
  apply (good_back _ _ (F0_D1 t h G (pw h - 1 - G) ltac:(lia))).
  pose proof (G1_ne (2 * j) G1 h ltac:(lia) Hr) as G0.
  destruct (tz_bound h (2 * j) G1 ltac:(lia)) as [L [EL HL]].
  destruct (N_tz G1 G0) as [r2 [C2 HG1]].
  destruct (tz_bound L r2 C2 ltac:(lia)) as [c2 [EL2 Hc2]].
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_pos (2 * j)) as Pa.
  set (W0 := S (t + S h)) in *.
  set (W2 := (Apr (2 * j) + S (Afun (S t) + S W0) - 1)%nat).
  assert (EW2 : (Apr (2 * j) + S (Afun (S t) + S W0) = S W2)%nat) by (unfold W2; lia).
  assert (Wv : W2 = (Apr (2 * j) + Afun (S t) + S t + h + 2)%nat) by (unfold W2, W0; lia).
  pose proof (zv_lt2 t (2 * j) W0 ltac:(unfold W0; lia) ltac:(unfold W0; lia)) as HZv.
  pose proof (y1o_lt4 t (2 * j) ltac:(lia)) as Y4.
  pose proof (y2v_y1o t (2 * j)) as Hy2.
  assert (P1 : pw W2 = 2 * pw (W2 - 1)) by (apply pw_pred2; lia).
  pose proof (pw_le (Apr (2 * j) + Afun (S t) + (S t + 2)) (W2 - 1) ltac:(lia)) as P2.
  pose proof (pw_le h (W2 - 1) ltac:(lia)) as P3.
  pose proof (pw_S W2) as P4.
  assert (HK : y2v t (2 * j) + 2 * (pw W2 - 1 - y1o t (2 * j)) + 2 = pw (S W2)) by lia.
  assert (E1 : bin h G = bin (2 * j + S (r2 + S c2)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))).
  { rewrite <- HG1, <- HG, <- EL2, <- EL. reflexivity. }
  pose proof (pw_le L h ltac:(lia)) as P5.
  assert (HG2 : G1 < pw h) by lia.
  assert (Step : forall u t' c' C', (L <= S u)%nat -> G1 <= pw u ->
     G1 + (pw W2 - 1 - y1o t (2 * j)) + 1 = pw u + pw t' * (2 * C' + 1) -> u = (t' + S c')%nat ->
     pw t' * (2 * C' + 1) < pw u ->
     D1 (S t) (TL (bin h G) B0) W0 -->+ D1 (S t') (TL (bin c' C') (U B0)) (S W2)).
  { intros u t' c' C' H1 H2 H3 H4 H5. rewrite E1.
    apply (a_O0_next t k j r2 c2 C2 W0 _ u t' c' C' W2 Hk ltac:(unfold W0; lia) HZv EW2 HK); try rewrite <- HG1; try rewrite <- EL2; try assumption; lia. }
  destruct (N.le_gt_cases (y1o t (2 * j)) G1) as [Hle|Hlt].
  - pose proof (Hd Hle) as HLR. destruct HLR as [p0 [q0 [Hrun Hrat]]].
    destruct (ones_not_pow _ p0 q0 Hrun ltac:(lia)) as [D0 Dp].
    destruct (N_tz _ D0) as [t' [C' HD]].
    assert (Hlt2 : pw t' * (2 * C' + 1) < pw W2) by lia.
    destruct (tz_bound W2 t' C' Hlt2) as [c' [Eu HC']].
    apply (good_back _ _ (Step W2 t' c' C' ltac:(lia) ltac:(lia) ltac:(lia) Eu Hlt2)).
    pose proof (ones_lt _ p0 q0 h Hrun ltac:(lia) ltac:(lia)) as Hq0.
    apply (level_run (G1 - y1o t (2 * j)) t' c' C' W2 p0 q0 h 0 (G1 - y1o t (2 * j)) (S W2) HD HC' Eu Hrun Hrat ltac:(lia) ltac:(lia) D0 ltac:(lia) Dp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros Et _ E. subst t' C'. apply not_LR_335. exists p0, q0.
    change (pw 0 * (2 * 167 + 1)) with 335 in HD. rewrite <- HD. split; assumption.
  - set (Zl := pw (W2 - 1) + G1 - y1o t (2 * j)).
    assert (Z0 : Zl <> 0) by (unfold Zl; lia).
    destruct (N_tz _ Z0) as [t' [C' HD]].
    assert (Hlt2 : pw t' * (2 * C' + 1) < pw (W2 - 1)) by (rewrite <- HD; unfold Zl; lia).
    destruct (tz_bound (W2 - 1) t' C' Hlt2) as [c' [Eu HC']].
    apply (good_back _ _ (Step (W2 - 1)%nat t' c' C' ltac:(lia) ltac:(lia) ltac:(rewrite <- HD; unfold Zl; lia) Eu Hlt2)).
    apply (level_low t (2 * j) G1 h Zl t' c' C' (W2 - 1) (W2 - 1) (S W2) HD HC' Eu ltac:(lia) ltac:(left; lia) ltac:(unfold Zl; lia) Hlt HG2 Hr Hra Ha ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros Sh q C1 c1 j' theta HC1 Hc Hq Hth HX.
    apply (short_B t (2 * j) G1 h t' C' q C1 c1 j' Zl theta (W2 - 1) HD HC1 Hq ltac:(lia) ltac:(lia) ltac:(unfold Zl; lia) Sh Hr Hra Ha Hth HX).
Qed.

End Part_Close20.
Import Part_Close20.

Module Part_Close21.

Local Open Scope N_scope.

(* A step from a state with e = 0, a odd, r odd *)
Lemma step_odd_odd : forall t k h G j G1, S t = (2 * k + 1)%nat -> (26 <= S t)%nat ->
  pw (h - 2) <= G -> G < pw h -> G = pw (2 * j + 1) * (2 * G1 + 1) -> (2 * j + 1 + 3 <= h)%nat -> (2 * j + 1 <= S t)%nat ->
  (y1o t (2 * j + 1) <= G1 -> LR (G1 - y1o t (2 * j + 1))) ->
  Good (F0 (S t) h (pw h - 1 - G)).
Proof.
  intros t k h G j G1 Hk Ha Hlo Hhi HG Hr Hra Hd.
  apply (good_back _ _ (F0_D1 t h G (pw h - 1 - G) ltac:(lia))).
  destruct (tz_bound h (2 * j + 1) G1 ltac:(lia)) as [c1 [Eh Hc1]].
  pose proof (Afun_bd (S t)) as BA. pose proof (Apr_pos (2 * j + 1)) as Pa.
  set (W0 := S (t + S h)) in *.
  set (Wf := (Apr (2 * j + 1) + S (Afun (S t) + S W0))%nat).
  assert (Wv : Wf = (Apr (2 * j + 1) + Afun (S t) + S t + h + 3)%nat) by (unfold Wf, W0; lia).
  pose proof (zv_lt2 t (2 * j + 1) W0 ltac:(unfold W0; lia) ltac:(unfold W0; lia)) as HZv.
  pose proof (y1o_lt4 t (2 * j + 1) ltac:(lia)) as Y4.
  pose proof (y2v_y1o t (2 * j + 1)) as Hy2.
  assert (P1 : pw Wf = 2 * pw (Wf - 1)) by (apply pw_pred2; lia).
  assert (P0 : pw (Wf - 1) = 2 * pw (Wf - 2)).
  { replace (Wf - 2)%nat with (Wf - 1 - 1)%nat by lia. apply pw_pred2. lia. }
  pose proof (pw_le (Apr (2 * j + 1) + Afun (S t) + (S t + 2)) (Wf - 2) ltac:(lia)) as P2.
  pose proof (pw_le h (Wf - 2) ltac:(lia)) as P3.
  pose proof (pw_le 9 (Wf - 2) ltac:(lia)) as P9. change (pw 9) with 512 in P9.
  pose proof (pw_le c1 h ltac:(lia)) as P5.
  assert (HG2 : G1 < pw h) by lia.
  assert (HK : y2v t (2 * j + 1) + 1 + 2 * (pw (Wf - 1) - 1 - y1o t (2 * j + 1)) + 1 = pw Wf) by lia.
  assert (E1 : bin h G = bin (2 * j + 1 + S c1) (pw (2 * j + 1) * (2 * G1 + 1))).
  { rewrite <- HG, <- Eh. reflexivity. }
  set (Z := G1 + pw (Wf - 1) - y1o t (2 * j + 1)).
  assert (Z1 : Z + y1o t (2 * j + 1) = pw (Wf - 1) + G1) by (unfold Z; lia).
  assert (Z0 : Z <> 0) by lia.
  destruct (N_tz Z Z0) as [t' [C' HD]].
  assert (Hlt2 : pw t' * (2 * C' + 1) < pw Wf) by lia.
  destruct (tz_bound Wf t' C' Hlt2) as [c' [Ew HC']].
  assert (Ew2 : (t' + S c')%nat = Wf) by (symmetry; exact Ew).
  assert (Hstep : D1 (S t) (TL (bin h G) B0) W0 -->+ D1 (S t') (TL (bin c' C') (U B0)) (S Wf)).
  { rewrite E1, <- Ew2.
    apply (a_O1_next t k j c1 G1 W0 (pw (Wf - 1) - 1 - y1o t (2 * j + 1)) t' c' C' Hk ltac:(unfold W0; lia) HZv).
    all: rewrite ?Ew2.
    - exact HK.
    - reflexivity.
    - lia.
    - exact Hc1.
    - lia.
    - rewrite <- HD. unfold Z. lia.
    - rewrite <- HD. lia. }
  apply (good_back _ _ Hstep).
  assert (H83 : t' = 0%nat -> (S Wf = S t' + c' + 1)%nat -> C' <> 167).
  { intros Et _ E. subst t' C'. change (pw 0 * (2 * 167 + 1)) with 335 in HD. lia. }
  destruct (N.le_gt_cases (y1o t (2 * j + 1)) G1) as [Hle|Hlt].
  - destruct (Hd Hle) as [p0 [q0 [Hrun Hrat]]].
    destruct (ones_not_pow _ p0 q0 Hrun ltac:(lia)) as [D0 Dp].
    pose proof (ones_lt _ p0 q0 h Hrun ltac:(lia) ltac:(lia)) as Hq0.
    pose proof (ones_high _ p0 q0 (Wf - 1) Hrun ltac:(lia)) as Hr2.
    assert (EZ : G1 - y1o t (2 * j + 1) + pw (Wf - 1) = Z) by (unfold Z; lia).
    rewrite EZ in Hr2.
    pose proof (pw_split h (Wf - 1) ltac:(lia)) as S1.
    apply (level_run Z t' c' C' Wf p0 q0 h (pw (Wf - 1 - h)) (G1 - y1o t (2 * j + 1)) (S Wf) HD HC' Ew Hr2 Hrat ltac:(lia) ltac:(lia) D0 ltac:(lia) Dp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H83).
  - apply (level_low t (2 * j + 1) G1 h Z t' c' C' Wf (Wf - 1) (S Wf) HD HC' Ew ltac:(lia) ltac:(right; lia) Z1 Hlt HG2 Hr Hra Ha ltac:(lia) ltac:(lia) ltac:(lia) H83).
    intros Sh q C1 c2 j' theta HC1 Hc Hq Hth HX.
    apply (short_C t (2 * j + 1) G1 h t' C' q C1 c2 j' Z theta Wf HD HC1 Hq ltac:(lia) Wv ltac:(exact Z1) Sh Hr Hra Ha Hth HX).
Qed.

Theorem inv_step : forall e a h G, Inv e a h G -> Good (FC e a h (pw h - 1 - G)).
Proof.
  intros e a h G HI. destruct e.
  - apply step_e1. exact HI.
  - destruct a as [|t].
    { destruct HI as [Ha _]. lia. }
    destruct (Nat.Even_or_Odd (S t)) as [[k Hk]|[k Hk]].
    + apply (step_e0_even t k h G Hk HI).
    + destruct HI as [Ha [Hh [Hlo [Hhi [r [G1 [HG [Hr [_ [Hra HD]]]]]]]]]].
      change (Good (F0 (S t) h (pw h - 1 - G))).
      destruct (HD t eq_refl) as [_ [Hd _]].
      assert (Hev : Nat.even (S t) = false) by (rewrite Hk; apply even_2j1).
      pose proof (Hd Hev eq_refl) as Hd2.
      destruct (Nat.Even_or_Odd r) as [[j Hj]|[j Hj]]; subst r.
      * apply (step_odd_even t k h G j G1 Hk Ha Hlo Hhi HG Hr Hra Hd2).
      * apply (step_odd_odd t k h G j G1 Hk Ha Hlo Hhi HG Hr Hra Hd2).
Qed.

End Part_Close21.
Import Part_Close21.

Module Part_Start0.

Local Open Scope N_scope.

(* The first F state with W = 24, by plain steps from the blank tape *)
Lemma start0 : c0 -->+ F0 11 12 458.
Proof.
  unfold F0, AC, B0.
  assert (E : zL 11 ++ true :: bin 12 458 =
    [false;false;false;false;false;false;false;false;false;false;false;true;
     false;true;false;true;false;false;true;true;true;false;false;false]) by reflexivity.
  rewrite E. cbn [X sb].
  change c0 with (A, (const S0, S0, const S0)).
  do 2741 step.
  finish.
Qed.

End Part_Start0.
Import Part_Start0.

Module Part_Start.

Local Open Scope N_scope.

(* One explicit stage from W = 24 to W = 193 *)
Definition Gs : N := 2296833611741004516.
Definition G1s : N := 287104201467625564.
Definition Cp : N := 4501401409422219.
Definition C2p : N := 1125350352355554.
Definition Kp : N := 18010002073583612.
Definition xs : N := 2198217948444.

Lemma s1 : F0 11 12 458 -->+ D1 1 (TL (bin 52 Cp) (U B0)) 55.
Proof.
  eapply progress_trans.
  - apply (F0_D1 10 12 3637 458). vm_compute. reflexivity.
  - apply (a_O0_next 10 5 0 1 9 454 24 Kp 53 0 52 Cp 54).
    + reflexivity.
    + lia.
    + vm_compute. reflexivity.
    + reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + lia.
    + vm_compute. discriminate.
    + vm_compute. discriminate.
    + vm_compute. reflexivity.
    + reflexivity.
    + vm_compute. reflexivity.
Qed.

Lemma s2 : D1 1 (TL (bin 52 Cp) (U B0)) 55 -->+ AC (TL (zL 52) (D3 B0)) (bin 61 xs).
Proof.
  apply (b_O0 0 0 0 0 50 C2p 55).
  - reflexivity.
  - lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma s3 : AC (TL (zL 52) (D3 B0)) (bin 61 xs) -->+ FC false 131 61 (pw 61 - 1 - Gs).
Proof.
  apply (d3_fin 52 61 xs). vm_compute. reflexivity.
Qed.

Lemma inv0 : Inv false 131 61 Gs.
Proof.
  unfold Inv. split; [lia|]. split; [lia|]. split; [vm_compute; discriminate|]. split; [vm_compute; reflexivity|].
  exists 2%nat, G1s. split; [vm_compute; reflexivity|]. split; [lia|]. split; [discriminate|]. split; [lia|].
  unfold DCond. intros t Ht.
  assert (Et : t = 130%nat) by lia. subst t.
  split; [|split].
  - intros H _ _. vm_compute in H. discriminate.
  - intros _ _ Hle. exfalso. pose proof (y1o_lo 130 2) as P.
    pose proof (pw_le 61 (Apr 2 + Afun (S 130) + (S 130 + 1)) ltac:(vm_compute; lia)) as P2.
    assert (H61 : G1s < pw 61) by (vm_compute; reflexivity). lia.
  - intros _ He. discriminate.
Qed.

Definition Cst (x : bool * nat * nat * N) : Q * tape :=
  match x with (e, a, h, G) => FC e a h (pw h - 1 - G) end.
Definition Pst (x : bool * nat * nat * N) : Prop :=
  match x with (e, a, h, G) => Inv e a h G end.

End Part_Start.
Import Part_Start.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (c' := Cst (false, 131%nat, 61%nat, Gs)).
  - apply progress_evstep.
    eapply progress_trans; [apply start0|].
    eapply progress_trans; [apply s1|].
    eapply progress_trans; [apply s2|].
    apply s3.
  - apply (progress_nonhalt_cond tm _ _ Cst Pst).
    + intros [[[e a] h] G] HI.
      destruct (inv_step e a h G HI) as [e' [a' [h' [G' [H1 H2]]]]].
      exists (e', a', h', G'). split; [exact H1|exact H2].
    + exact inv0.
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
