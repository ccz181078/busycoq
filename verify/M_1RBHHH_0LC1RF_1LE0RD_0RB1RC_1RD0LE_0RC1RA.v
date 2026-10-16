(* 1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA never halts.
   Sync bouncer counter: a binary counter on the left (TM4's digits d0 = 0010, d1 = 1010),
   a row of 5-cell blocks on the right (A = 00111, B = 10111), and a 3-cell front 111
   that walks right through the A blocks after each counter overflow.
   Adapted from the proof of 1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC--- (the parent), which is
   adapted from verify/SBCv7.v, Module TM4 (1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0RA---).
   This machine is the parent's table with its states renamed
   sigma = (A,B,C,D,E,F) -> (E,D,B,C,F,A), no mirror, started in the parent's state F; so the moving
   particle is <E 001 / 001 F> and the right-edge head state is B.
   The state renaming is applied to every shift rule and to the gadget's Hit0/Hit1.
   The opening reaches CfgF 5 0 14 4 = Q(7,65,1,14,4) in 16,590 steps.
   The counter, conversion gadget and invariant are shared with the parent's proof.
   Informal proof: the accompanying write-up.
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62.
Require Import Arith Lia.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation bA := <[0;0;1;1;1].
Notation bB := <[1;0;1;1;1].
Notation bAr := [0;0;1;0;1].
Notation bBr := [0;0;0;0;1].

Ltac fw H := eapply evstep_trans; [solve [apply H; lia] | ].
Ltac fp H := eapply progress_evstep_trans; [solve [apply H; lia] | ].

Lemma ev_eq {c1 c2 c2'} : c1 -->* c2 -> c2 = c2' -> c1 -->* c2'.
Proof. intros H E. subst. exact H. Qed.

Lemma prog_eq {c1 c2 c2'} : c1 -->+ c2 -> c2 = c2' -> c1 -->+ c2'.
Proof. intros H E. subst. exact H. Qed.

(** * Shift rules (proof.md 3.1) *)

Lemma ENDL l : l <* <[0;0] {{B}}> 0inf -->+ l <{{E}} [0;0;1] *> 0inf. Proof. es. Qed.
Lemma AL l r : l <* bA <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> bAr *> r. Proof. es. Qed.
Lemma BL l r : l <* bB <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> bBr *> r. Proof. es. Qed.
Lemma AR l r : l <* <[0;0;1] {{F}}> bAr *> r -->* l <* bA <* <[0;0;1] {{F}}> r. Proof. es. Qed.
Lemma BR l r : l <* <[0;0;1] {{F}}> bBr *> r -->* l <* bB <* <[0;0;1] {{F}}> r. Proof. es. Qed.
Lemma ENDR l : l <* <[0;0;1] {{F}}> 0inf -->* l <* bB <* <[0;0] {{B}}> 0inf. Proof. es. Qed.
Lemma D1L l r : l <* d1 <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> [0;1;0;1] *> r. Proof. es. Qed.
Lemma FLIP l r : l <* d0 <{{E}} [0;0;1] *> r -->* l <* d1 <* <[0;0;1] {{F}}> r. Proof. es. Qed.
Lemma D0R l r : l <* <[0;0;1] {{F}}> [0;1;0;1] *> r -->* l <* d0 <* <[0;0;1] {{F}}> r. Proof. es. Qed.
Lemma D0R' l r : l <* <[0;0;1] {{F}}> [0;1] *> [0;1;0;1] *> r -->* l <* d0 <* <[0;0;1] {{F}}> [0;1] *> r.
Proof. es. Qed.
Lemma OVL r : 0inf <{{E}} [0;0;1] *> [0;1;0;1] *> r -->* 0inf <* d1 <* <[0;0;1] {{F}}> [0;1] *> r.
Proof. es. Qed.
Lemma OVR l r : l <* <[0;0;1] {{F}}> [0;1] *> bAr *> r -->* l <* d0 <{{E}} [0;0;1] *> [1;0;1] *> r.
Proof. es. Qed.
Lemma FL l r : l <* bA <* <[1;1;1] <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> [0;0;1] *> bBr *> r.
Proof. es. Qed.
Lemma FR1 l r : l <* <[0;0;1] {{F}}> [0;0;1] *> bBr *> r -->* l <* bA <{{E}} [0;0;1] *> [0;0;1] *> r.
Proof. es. Qed.
Lemma FR2 l r : l <* <[0;0;1] {{F}}> [0;0;1] *> bAr *> r -->* l <* bA <{{E}} [0;0;1] *> [1;0;1] *> r.
Proof. es. Qed.
Lemma FR3 l r : l <* <[0;0;1] {{F}}> [1;0;1] *> bAr *> r -->* l <* bA <* <[1;1;1] <* <[0;0;1] {{F}}> r.
Proof. es. Qed.
Lemma FR4 l r : l <* <[0;0;1] {{F}}> [1;0;1] *> bBr *> r -->* l <{{E}} [0;0;1] *> [0;0;1] *> bAr *> r.
Proof. es. Qed.
Lemma FE0 l : l <* <[0;0;1] {{F}}> [0;0;1] *> 0inf -->* l <* bA <* <[0;0] {{B}}> 0inf.
Proof. es. Qed.
Lemma FE1 l : l <* <[0;0;1] {{F}}> [1;0;1] *> 0inf -->* l <{{E}} [0;0;1] *> [0;0;1] *> [0;0;1] *> 0inf.
Proof. es. Qed.
Lemma FE2 l : l <* <[0;0;1] {{F}}> [0;0;1] *> [0;0;1] *> 0inf -->* l <* bA <{{E}} [0;0;1] *> [1] *> 0inf.
Proof. es. Qed.
Lemma FE3 l : l <* <[0;0;1] {{F}}> [1] *> 0inf -->* l <{{E}} [0;0;1] *> [0;0;1;1] *> 0inf.
Proof. es. Qed.
Lemma FE4 l : l <* <[0;0;1] {{F}}> [0;0;1;1] *> 0inf -->* l <* bA <{{E}} [0;0;1] *> [0;0;1] *> 0inf.
Proof. es. Qed.

(** * Repeated rules (proof.md 3.2) *)

Lemma ALs a : forall l r, l <* bA^^a <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> bAr^^a *> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow AL; follow IH; rewrite lpow_shift'; finish].
Qed.
Lemma BLs a : forall l r, l <* bB^^a <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> bBr^^a *> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow BL; follow IH; rewrite lpow_shift'; finish].
Qed.
Lemma ARs a : forall l r, l <* <[0;0;1] {{F}}> bAr^^a *> r -->* l <* bA^^a <* <[0;0;1] {{F}}> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow AR; follow IH; rewrite <-lpow_shift'; finish].
Qed.
Lemma BRs a : forall l r, l <* <[0;0;1] {{F}}> bBr^^a *> r -->* l <* bB^^a <* <[0;0;1] {{F}}> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow BR; follow IH; rewrite <-lpow_shift'; finish].
Qed.
Lemma D1Ls a : forall l r, l <* d1^^a <{{E}} [0;0;1] *> r -->* l <{{E}} [0;0;1] *> [0;1;0;1]^^a *> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow D1L; follow IH; rewrite lpow_shift'; finish].
Qed.
Lemma D0R's a : forall l r, l <* <[0;0;1] {{F}}> [0;1] *> [0;1;0;1]^^a *> r -->* l <* d0^^a <* <[0;0;1] {{F}}> [0;1] *> r.
Proof.
  induction a as [|a IH]; intros; [finish | rewrite !lpow_S, !Str_app_assoc; follow D0R'; follow IH; rewrite <-lpow_shift'; finish].
Qed.

(** * The binary counter: k digits, MSB first (proof.md: C_k(n)) *)

Fixpoint ctr (k n : nat) : side :=
  match k with
  | O => 0inf
  | S k => ctr k (Nat.div2 n) <* (if Nat.odd n then d1 else d0)
  end.

Lemma ctr_even k q : ctr (S k) (2*q) = ctr k q <* d0.
Proof. cbn [ctr]. rewrite Nat.div2_double, Nat.odd_even. reflexivity. Qed.

Lemma ctr_odd k q : ctr (S k) (S (2*q)) = ctr k q <* d1.
Proof. cbn [ctr]. rewrite Nat.div2_succ_double, Nat.odd_succ, Nat.even_even. reflexivity. Qed.

Lemma pow2_pos k : 1 <= 2^k.
Proof. pose proof (Nat.pow_nonzero 2 k). lia. Qed.

(** CTR: one increment, n+1 <= 2^k - 1 *)
Lemma CTR k : forall n r, S n < 2^k ->
  ctr k n <{{E}} [0;0;1] *> r -->* ctr k (S n) <* <[0;0;1] {{F}}> r.
Proof.
  induction k as [|k IH]; intros n r H.
  - cbn in H. lia.
  - rewrite Nat.pow_succ_r' in H.
    destruct (Nat.Even_or_Odd n) as [[q Hq]|[q Hq]]; subst n.
    + rewrite ctr_even, ctr_odd.
      fw FLIP. finish.
    + replace (S (2*q+1)) with (2 * S q) by lia.
      replace (2*q+1) with (S (2*q)) by lia.
      rewrite ctr_even, ctr_odd.
      fw D1L. fw (IH q). fw D0R. finish.
Qed.

Lemma ctr_ones k : ctr k (2^k - 1) = 0inf <* d1^^k.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - pose proof (pow2_pos k).
    replace (2^(S k) - 1) with (S (2 * (2^k - 1))) by (rewrite Nat.pow_succ_r'; lia).
    rewrite ctr_odd, IH. reflexivity.
Qed.

Lemma ctr_pow k : ctr (S k) (2^k) = 0inf <* d1 <* d0^^k.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r', ctr_even, IH. reflexivity.
Qed.

Lemma ctr_ov k : ctr (S (S k)) (2^(S k) + 1) = 0inf <* d1 <* d0^^k <* d1.
Proof.
  replace (2^(S k) + 1) with (S (2 * 2^k)) by (rewrite Nat.pow_succ_r'; lia).
  rewrite ctr_odd, ctr_pow. reflexivity.
Qed.

(** OV: the counter overflows; it gains a digit and a new front 111 appears *)
Lemma OV k r :
  ctr (S k) (2^(S k) - 1) <{{E}} [0;0;1] *> bAr *> bAr *> r -->*
  ctr (S (S k)) (2^(S k) + 1) <* bA <* <[1;1;1] <* <[0;0;1] {{F}}> r.
Proof.
  rewrite ctr_ones, ctr_ov.
  fw D1Ls. rewrite lpow_S, Str_app_assoc.
  fw OVL. fw D0R's. fw OVR. fw FLIP. fw FR3. finish.
Qed.

(** RT: a round trip of the head through the counter (no overflow) *)
Lemma RT K n a r : S n < 2^K ->
  ctr K n <* bA^^a <{{E}} [0;0;1] *> r -->* ctr K (S n) <* bA^^a <* <[0;0;1] {{F}}> r.
Proof.
  intros H. fw ALs. fw CTR. fw ARs. finish.
Qed.

(** OVRT: a round trip that overflows the counter *)
Lemma OVRT k a r :
  ctr (S k) (2^(S k) - 1) <* bA^^(S (S a)) <{{E}} [0;0;1] *> r -->*
  ctr (S (S k)) (2^(S k) + 1) <* bA <* <[1;1;1] <* bA^^a <* <[0;0;1] {{F}}> r.
Proof.
  fw ALs. rewrite !lpow_S, !Str_app_assoc. fw OV. fw ARs. finish.
Qed.

(** QC: one step of the front (3 round trips, the front moves 2 blocks right) *)
Lemma QC K n x y r : 3 + n < 2^K ->
  ctr K n <* bA^^(S x) <* <[1;1;1] <* bA^^(S (S y)) <{{E}} [0;0;1] *> r -->*
  ctr K (3 + n) <* bA^^(S (S (S x))) <* <[1;1;1] <* bA^^y <* <[0;0;1] {{F}}> r.
Proof.
  intros H.
  fw ALs.
  fw (FL (ctr K n <* bA^^x) (bAr^^(S (S y)) *> r)).
  fw (RT K n x).
  fw FR1.
  fw (RT K (S n) (S x)).
  fw (FR2 (ctr K (S (S n)) <* bA^^(S x)) (bAr^^(S y) *> r)).
  fw (RT K (S (S n)) (S (S x))).
  fw (FR3 (ctr K (S (S (S n))) <* bA^^(S (S x))) (bAr^^y *> r)).
  fw ARs.
  finish.
Qed.

(** * Configurations at the right edge (proof.md 1) *)

Definition Pc K n X z := ctr K n <* bA^^X <* bB^^z <* <[0;0] {{B}}> 0inf.
Definition Qc K n x y z := ctr K n <* bA^^x <* <[1;1;1] <* bA^^y <* bB^^z <* <[0;0] {{B}}> 0inf.

Lemma R1 K n X z : S n < 2^K -> Pc K n X z -->+ Pc K (S n) X (S z).
Proof.
  intros H. unfold Pc.
  fp ENDL. fw BLs. fw RT. fw BRs. fw ENDR. finish.
Qed.

Lemma R1s K c : forall n X z, c + n < 2^K -> Pc K n X z -->* Pc K (c + n) X (c + z).
Proof.
  induction c as [|c IH]; intros n X z H.
  - finish.
  - eapply evstep_trans. { apply progress_evstep, R1. lia. }
    eapply ev_eq. { apply IH. lia. }
    f_equal; lia.
Qed.

Lemma R2 k X z : Pc (S k) (2^(S k) - 1) (S (S X)) z -->+ Qc (S (S k)) (2^(S k) + 1) 1 X (S z).
Proof.
  unfold Pc, Qc.
  fp ENDL. fw BLs. fw OVRT. fw BRs. fw ENDR. finish.
Qed.

(** Pfin: the rest of a P phase (R1 repeatedly, then R2) *)
Lemma Pfin (k n X z n' x' X' z' : nat) :
  n < 2^(S k) -> X = 2 + X' -> n' = 2^(S k) + 1 -> x' = 1%nat -> z' = z + 2^(S k) - n ->
  Pc (S k) n X z -->+ Qc (S (S k)) n' x' X' z'.
Proof.
  intros H1 H2 H3 H4 H5. subst.
  eapply evstep_progress_trans. { apply (R1s (S k) (2^(S k) - 1 - n) n). lia. }
  replace (2^(S k) - 1 - n + n) with (2^(S k) - 1) by lia.
  eapply prog_eq. { apply R2. }
  f_equal; lia.
Qed.

Lemma R3 K n x y z : 3 + n < 2^K ->
  Qc K n (S x) (S (S y)) z -->+ Qc K (3 + n) (S (S (S x))) y (S z).
Proof.
  intros H. unfold Qc.
  fp ENDL. fw BLs. fw QC. fw BRs. fw ENDR. finish.
Qed.

(** * The conversion gadget (proof.md 3.3)

    After FL, the old front plus the B blocks form a word G right of the head.  Each round
    the head goes through the counter and back (+1) and then hits G: a hit either reflects
    the head, with 0 or 1 new A block (Hit0 / Hit1), or ends at the right edge (FE0).
    Gad G T D: G takes T rounds in all, which add D A blocks. *)

Definition Hit0 (G G' : side) := forall l, l <* <[0;0;1] {{F}}> G -->* l <{{E}} [0;0;1] *> G'.
Definition Hit1 (G G' : side) := forall l, l <* <[0;0;1] {{F}}> G -->* l <* bA <{{E}} [0;0;1] *> G'.

Inductive Gad : side -> nat -> nat -> Prop :=
  | Gad_end : Gad ([0;0;1] *> 0inf) 1%nat 1%nat
  | Gad_h0 G G' T D : Hit0 G G' -> Gad G' T D -> Gad G (S T) D
  | Gad_h1 G G' T D : Hit1 G G' -> Gad G' T D -> Gad G (S T) (S D).

Lemma Gad_DT G T D : Gad G T D -> D <= T.
Proof. induction 1; lia. Qed.

Lemma Gad_eq {G T D T' D'} : T = T' -> D = D' -> Gad G T D -> Gad G T' D'.
Proof. intros E1 E2 H. subst. exact H. Qed.

(** even (y = 0): FR1^(z+1), FE0 *)
Lemma gad_even z : Gad ([0;0;1] *> bBr^^z *> 0inf) (S z) (S z).
Proof.
  induction z as [|z IH].
  - apply Gad_end.
  - eapply Gad_h1; [intro l; apply (FR1 l (bBr^^z *> 0inf)) | exact IH].
Qed.

(** odd (y = 1): FR1, FR2, (FR4, FR2)^z, FE1, FE2, FE3, FE4, FE0 *)
Lemma gad_tail : Gad ([1;0;1] *> 0inf) 5 3.
Proof.
  eapply Gad_h0; [intro l; apply FE1 |].
  eapply Gad_h1; [intro l; apply FE2 |].
  eapply Gad_h0; [intro l; apply FE3 |].
  eapply Gad_h1; [intro l; apply FE4 |].
  apply Gad_end.
Qed.

Lemma gad_mid z : Gad ([1;0;1] *> bBr^^z *> 0inf) (5 + 2*z) (3 + z).
Proof.
  induction z as [|z IH].
  - exact gad_tail.
  - apply (Gad_eq (T := S (S (5 + 2*z))) (D := S (3 + z))); [lia | lia |].
    eapply Gad_h0; [intro l; apply (FR4 l (bBr^^z *> 0inf)) |].
    eapply Gad_h1; [intro l; apply FR2 |].
    exact IH.
Qed.

Lemma gad_odd z : Gad ([0;0;1] *> bBr *> bAr *> bBr^^z *> 0inf) (7 + 2*z) (5 + z).
Proof.
  apply (Gad_eq (T := S (S (5 + 2*z))) (D := S (S (3 + z)))); [lia | lia |].
  eapply Gad_h1; [intro l; apply FR1 |].
  eapply Gad_h1; [intro l; apply FR2 |].
  apply gad_mid.
Qed.

(** All T rounds without overflow (R4, R5) *)
Lemma ConvNo K : forall G T D, Gad G T D -> forall n a, n + T < 2^K ->
  ctr K n <* bA^^a <{{E}} [0;0;1] *> G -->* Pc K (n + T) (a + D) 0.
Proof.
  induction 1 as [|G G' T D HH HG IH|G G' T D HH HG IH]; intros n a Hn.
  - fw (RT K n a). fw FE0. unfold Pc.
    replace (n + 1) with (S n) by lia. replace (a + 1) with (S a) by lia. finish.
  - fw (RT K n a). fw HH. eapply ev_eq. { apply (IH (S n) a). lia. } f_equal; lia.
  - fw (RT K n a). fw HH. eapply ev_eq. { apply (IH (S n) (S a)). lia. } f_equal; lia.
Qed.

(** Rounds after an overflow: a new front (QC) runs while the old gadget converts *)
Lemma PostOV K : forall G T D, Gad G T D -> forall n x b y,
  b + D = 2*T + y -> 1 <= y -> 3*T + n < 2^K ->
  ctr K n <* bA^^(S x) <* <[1;1;1] <* bA^^b <{{E}} [0;0;1] *> G -->*
  Qc K (3*T + n) (2*T + S x) y 0.
Proof.
  induction 1 as [|G G' T D HH HG IH|G G' T D HH HG IH]; intros n x b y Hb Hy Hn.
  - destruct y as [|y]; [lia|].
    assert (b = S (S y)) by lia. subst b.
    fw (QC K n x y). fw FE0. unfold Qc. finish.
  - pose proof (Gad_DT _ _ _ HG).
    destruct b as [|[|b]]; [lia|lia|].
    fw (QC K n x b). fw HH.
    eapply ev_eq. { apply (IH (3 + n) (S (S x)) b y); lia. }
    f_equal; lia.
  - pose proof (Gad_DT _ _ _ HG).
    destruct b as [|[|b]]; [lia|lia|].
    fw (QC K n x b). fw HH.
    eapply ev_eq. { apply (IH (3 + n) (S (S x)) (S b) y); lia. }
    f_equal; lia.
Qed.

(** A conversion during which the counter overflows (R5o) *)
Lemma ConvOV k : forall G T D, Gad G T D -> forall n a m y,
  n + T = 2^(S k) + m -> n < 2^(S k) -> a + D = 2 + 2*m + y -> 1 <= y ->
  3*m + (2^(S k) + 1) < 2^(S (S k)) ->
  ctr (S k) n <* bA^^a <{{E}} [0;0;1] *> G -->*
  Qc (S (S k)) (3*m + (2^(S k) + 1)) (1 + 2*m) y 0.
Proof.
  pose proof (pow2_pos (S k)) as Hp.
  induction 1 as [|G G' T D HH HG IH|G G' T D HH HG IH]; intros n a m y E1 E2 E3 E4 E5.
  - assert (m = 0%nat) by lia. subst m.
    assert (n = 2^(S k) - 1) by lia. subst n.
    destruct y as [|y]; [lia|].
    assert (a = S (S y)) by lia. subst a.
    fw (OVRT k y). fw FE0. unfold Qc. finish.
  - pose proof (Gad_DT _ _ _ HG).
    destruct (Nat.eq_dec n (2^(S k) - 1)) as [En|En].
    + subst n. assert (m = T) by lia. subst m.
      destruct a as [|[|a]]; [lia|lia|].
      fw (OVRT k a). fw HH.
      eapply ev_eq. { apply (PostOV (S (S k)) _ _ _ HG (2^(S k) + 1) O a y); lia. }
      f_equal; lia.
    + fw (RT (S k) n a). fw HH.
      apply (IH (S n) a m y); lia.
  - pose proof (Gad_DT _ _ _ HG).
    destruct (Nat.eq_dec n (2^(S k) - 1)) as [En|En].
    + subst n. assert (m = T) by lia. subst m.
      destruct a as [|[|a]]; [lia|lia|].
      fw (OVRT k a). fw HH.
      eapply ev_eq. { apply (PostOV (S (S k)) _ _ _ HG (2^(S k) + 1) O (S a) y); lia. }
      f_equal; lia.
    + fw (RT (S k) n a). fw HH.
      apply (IH (S n) (S a) m y); lia.
Qed.

(** From a Q configuration with y in {0,1}: the front meets the B blocks *)
Lemma QG0 K n x z : Qc K n (S x) 0 z -->+
  ctr K n <* bA^^x <{{E}} [0;0;1] *> [0;0;1] *> bBr^^(S z) *> 0inf.
Proof.
  unfold Qc. fp ENDL. fw BLs. fw (FL (ctr K n <* bA^^x) (bBr^^z *> 0inf)). finish.
Qed.

Lemma QG1 K n x z : Qc K n (S x) 1 z -->+
  ctr K n <* bA^^x <{{E}} [0;0;1] *> [0;0;1] *> bBr *> bAr *> bBr^^z *> 0inf.
Proof.
  unfold Qc. fp ENDL. fw BLs.
  fw (AL (ctr K n <* bA^^(S x) <* <[1;1;1]) (bBr^^z *> 0inf)).
  fw (FL (ctr K n <* bA^^x) (bAr *> bBr^^z *> 0inf)). finish.
Qed.

(** R4 *)
Lemma Conv0 K n x z : n + z + 2 < 2^K ->
  Qc K n (S x) 0 z -->+ Pc K (n + z + 2) (x + z + 2) 0.
Proof.
  intros H. eapply progress_evstep_trans. { apply QG0. }
  eapply ev_eq. { apply (ConvNo K _ _ _ (gad_even (S z))). lia. }
  f_equal; lia.
Qed.

(** R5 *)
Lemma Conv1 K n x z : n + 2*z + 7 < 2^K ->
  Qc K n (S x) 1 z -->+ Pc K (n + 2*z + 7) (x + z + 5) 0.
Proof.
  intros H. eapply progress_evstep_trans. { apply QG1. }
  eapply ev_eq. { apply (ConvNo K _ _ _ (gad_odd z)). lia. }
  f_equal; lia.
Qed.

(** R5o *)
Lemma Conv1o (k m n x z n' x' y : nat) :
  n + 2*z + 7 = 2^(S k) + m -> n < 2^(S k) -> x + z + 5 = 2 + 2*m + y -> 1 <= y ->
  3*m + (2^(S k) + 1) < 2^(S (S k)) -> n' = 3*m + (2^(S k) + 1) -> x' = 1 + 2*m ->
  Qc (S k) n (S x) 1 z -->+ Qc (S (S k)) n' x' y 0.
Proof.
  intros. subst n' x'.
  eapply progress_evstep_trans. { apply QG1. }
  apply (ConvOV k _ _ _ (gad_odd z)); lia.
Qed.

(** * The cycle (proof.md 4)

    Index (k,i,y,z) stands for Q(k+2, 2^(k+1)+1+3i, 1+2i, y, z): the Q phase of the cycle
    whose counter has k+2 digits, after i front steps.  In proof.md's cycle coordinates
    N = 2^(k+1), Y = y+2i, Z = z-i.  Inv is the hexagon of proof.md 4 in these coordinates
    (Z = z-i may be negative), plus N >= 64. *)

Definition CfgF (k i y z : nat) := Qc (S (S k)) (3*i + (2^(S k) + 1)) (1 + 2*i) y z.

Definition Inv (k i y z : nat) : Prop :=
  64 <= 2^(S k) /\ 2^(S k) <= 8*(y + 2*i) /\ 8*(y + 2*i) <= 3 * 2^(S k) /\
  3*z <= 2^(S k) + 3*i /\ 8*i <= 8*z + 2^(S k) /\
  2^(S k) <= 4*y + 6*i + 2*z /\ 20*y + 24*i + 16*z <= 9 * 2^(S k).

Lemma cycle_step k i y z : Inv k i y z ->
  exists k' i' y' z', CfgF k i y z -->+ CfgF k' i' y' z' /\ Inv k' i' y' z'.
Proof.
  unfold Inv, CfgF. intros HI.
  pose proof (Nat.pow_succ_r' 2 (S k)) as HN.
  pose proof (Nat.pow_succ_r' 2 (S (S k))) as HN2.
  destruct y as [|[|y]].
  - (* y = 0: R4, R1^*, R2 *)
    exists (S k), O, (2*i + z), (2^(S k) - 3 - 3*i - z). split; [|lia].
    eapply progress_evstep_trans. { apply Conv0. lia. }
    apply progress_evstep. apply Pfin; lia.
  - destruct (Nat.lt_ge_cases (3*i + (2^(S k) + 1) + 2*z + 7) (2^(S (S k)))) as [Hno|Hov].
    + (* y = 1, no overflow: R5, R1^*, R2 *)
      exists (S k), O, (2*i + z + 3), (2^(S (S k)) - (3*i + (2^(S k) + 1) + 2*z + 7)).
      split; [|lia].
      eapply progress_evstep_trans. { apply Conv1. lia. }
      apply progress_evstep. apply Pfin; lia.
    + (* y = 1, overflow during the conversion: R5o *)
      remember (3*i + (2^(S k) + 1) + 2*z + 7 - 2^(S (S k))) as m eqn:Em.
      exists (S k), m, (2*i + z + 3 - 2*m), O. split; [|lia].
      apply (Conv1o (S k) m); lia.
  - (* y >= 2: R3 *)
    exists k, (S i), y, (S z). split; [|lia].
    eapply prog_eq. { apply R3. lia. }
    f_equal; lia.
Qed.

(** * Start: c0 reaches Q(7,65,1,14,4) = CfgF 5 0 14 4 in 16,590 steps *)

Lemma init0 : c0 -->* 0inf <* d1 <* d0^^5 <* d1 <* bA <* <[1;1;1] <* bA^^14 <* bB^^4 <* <[0;0] {{B}}> 0inf.
Proof. esx. Qed.

Lemma init : c0 -->* CfgF 5 0 14 4.
Proof. apply init0. Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt. { apply init. }
  apply (progress_nonhalt_cond tm _ (5,0,14,4)%nat
           (fun '(k,i,y,z) => CfgF k i y z) (fun '(k,i,y,z) => Inv k i y z)).
  - intros [[[k i] y] z] HI.
    destruct (cycle_step k i y z HI) as (k' & i' & y' & z' & H1 & H2).
    exists (k',i',y',z'). split; assumption.
  - unfold Inv. cbn. lia.
Qed.

(*
```
1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA
(= sigma of 1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---, sigma = EDBCFA, no mirror)

C_k(n): n in k bits MSB first, digit 1 -> 1010 (d1), digit 0 -> 0010 (d0)      [ctr k n]
A = 00111, B = 10111 left of the head;  A' = 00101, B' = 00001 right of the head
moving head: <E 001  /  001 F>  (sigma of TM4's hL / hR)

P(k,n,X,z)   := 0^inf C_k(n) A^X B^z 00 B> 0^inf                 [Pc]
Q(k,n,x,y,z) := 0^inf C_k(n) A^x 111 A^y B^z 00 B> 0^inf         [Qc]

R1  P(k,n,X,z)        -->+ P(k,n+1,X,z+1)              n+1 < 2^k
R2  P(k,2^k-1,X+2,z)  -->+ Q(k+1,2^k+1,1,X,z+1)
R3  Q(k,n,x+1,y+2,z)  -->+ Q(k,n+3,x+3,y,z+1)          n+3 < 2^k
R4  Q(k,n,x+1,0,z)    -->+ P(k,n+z+2,x+z+2,0)          n+z+2 < 2^k
R5  Q(k,n,x+1,1,z)    -->+ P(k,n+2z+7,x+z+5,0)         n+2z+7 < 2^k
R5o Q(k,n,x+1,1,z)    -->+ Q(k+1,2^k+1+3m,1+2m,y,0)    n+2z+7 = 2^k+m, n < 2^k,
                                                       x+z+5 = 2+2m+y, y >= 1, 3m+2^k+1 < 2^(k+1)

cycle index (k,i,y,z) = Q(k+2, 2^(k+1)+1+3i, 1+2i, y, z);  N = 2^(k+1), Y = y+2i, Z = z-i
  y >= 2:  R3                            ->  (k,   i+1, y-2,       z+1)
  y = 0:   R4, R1 repeated, R2           ->  (k+1, 0,   2i+z,      N-3-3i-z)
  y = 1:   R5, R1 repeated, R2           ->  (k+1, 0,   2i+z+3,    N-8-3i-2z)   no overflow
           R5o, m = 3i+2z+8-N            ->  (k+1, m,   2i+z+3-2m, 0)           overflow
invariant: N >= 64, 8Y >= N, 8Y <= 3N, 3Z <= N, 8Z >= -N, 4Y+2Z >= N, 20Y+16Z <= 9N
start: c0 -->(16590) Q(7,65,1,14,4), index (5,0,14,4)   [parent: c0 -->(17215) Q(7,65,1,16,0)]
```
*)
