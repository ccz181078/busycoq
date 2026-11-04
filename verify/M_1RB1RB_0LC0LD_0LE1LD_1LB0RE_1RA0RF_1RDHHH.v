(* 1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN NArith PArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope bool_scope.
Open Scope N_scope.

Definition tm : TM := Eval compute in
  (TM_from_str "1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---").

Arguments tm _ : simpl never.

Definition fuel64  : nat := Eval vm_compute in N.to_nat 64.
Definition fuel124 : nat := Eval vm_compute in N.to_nat 124.
Definition fuel256 : nat := Eval vm_compute in N.to_nat 256.
Definition fuel512 : nat := Eval vm_compute in N.to_nat 512.

(* ========================================================================== *)
(* Layer 1: Unary Stack Encoding & Concrete One-Sweep Transducer              *)
(* ========================================================================== *)

Fixpoint encDigit (a : nat) (W : side) : side :=
  match a with
  | O => S0 >> S1 >> W
  | S a' => S0 >> encDigit a' W
  end.

Fixpoint encU (L : list nat) : side :=
  match L with
  | [] => const S0
  | a :: L' => encDigit a (encU L')
  end.

Definition encOp (op : nat) (Z : side) : side :=
  match op with
  | O => S0 >> S1 >> Z
  | S O => S1 >> S0 >> S1 >> Z
  | _ => S0 >> S1 >> S1 >> Z
  end.

Fixpoint encRevOps (rop : list nat) (Z : side) : side :=
  match rop with
  | [] => Z
  | op :: rop' => encOp op (encRevOps rop' Z)
  end.

Lemma encRevOps_app (r1 r2 : list nat) (Z : side) :
  encRevOps (r1 ++ r2) Z = encRevOps r1 (encRevOps r2 Z).
Proof.
  induction r1 as [|x xs IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Definition cfgSweep (L : list nat) : Q * tape :=
  E;; encU L {{S1}} const S0.

Definition cfgCarry (c : nat) (L : list nat) (Z : side) : Q * tape :=
  match c with
  | O => (S0 >> encU L) <{{D}} Z
  | _ => encU L <{{D}} Z
  end.

Definition cfgRet (r : nat) (M : list nat) (Z : side) : Q * tape :=
  match r with
  | O => encU (0%nat :: M) {{E}}> Z
  | S O => E;; encU (0%nat :: M) {{S0}} (S1 >> Z)
  | S (S O) => E;; encU (0%nat :: M) {{S0}} Z
  | _ => E;; encU (0%nat :: M) {{S1}} Z
  end.

Local Ltac step_once :=
  lazymatch goal with
  | |- _ -[ _ ]->+ _ => eapply progress_intro; [prove_step | simpl_tape]
  | |- _ -[ _ ]->* _ => eapply evstep_step; [prove_step | simpl_tape]
  end.

Lemma init_reaches_sweep0 : c0 -[ tm ]->+ cfgSweep [0%nat].
Proof.
  unfold c0, tape0, q0, s0, cfgSweep; cbn.
  do 14 step_once.
  apply evstep_refl.
Qed.

Lemma launch_sweep (L : list nat) :
  cfgSweep L -[ tm ]->+ cfgCarry 0%nat L (encRevOps [0%nat] (const S0)).
Proof.
  unfold cfgSweep, cfgCarry, encRevOps, encOp.
  do 4 step_once.
  apply evstep_refl.
Qed.

Lemma step_D_four_zeros (W Z : side) :
  (S0 >> S0 >> S0 >> S0 >> W) <{{D}} Z -[ tm ]->+
  (S0 >> S1 >> S0 >> S0 >> W) {{E}}> Z.
Proof.
  do 11 step_once.
  apply evstep_refl.
Qed.

Lemma encU_expand_one (a : nat) (L : list nat) :
  exists W : side, encU (a :: L) = S0 >> W.
Proof.
  destruct a; eexists; reflexivity.
Qed.

Lemma carry0_step0 (L : list nat) (Z : side) :
  cfgCarry 0%nat (0%nat :: L) Z -[ tm ]->+ cfgCarry 1%nat L (encOp 1%nat Z).
Proof.
  unfold cfgCarry, encOp; cbn [encU encDigit].
  do 3 step_once.
  apply evstep_refl.
Qed.

Lemma carry0_step1 (L : list nat) (Z : side) :
  cfgCarry 0%nat (1%nat :: L) Z -[ tm ]->+ cfgCarry 0%nat L (encOp 2%nat Z).
Proof.
  unfold cfgCarry, encOp; cbn [encU encDigit].
  do 7 step_once.
  apply evstep_refl.
Qed.

Lemma carry0_wall (a : nat) (L : list nat) (Z : side) :
  cfgCarry 0%nat (S (S a) :: L) Z -[ tm ]->+ cfgRet 0%nat (S a :: L) Z.
Proof.
  unfold cfgCarry, cfgRet.
  change (encU (S (S a) :: L)) with (S0 >> S0 >> encDigit a (encU L)).
  change (encU (0%nat :: S a :: L)) with (S0 >> S1 >> S0 >> encDigit a (encU L)).
  destruct a as [|a']; cbn [encDigit]; exact (step_D_four_zeros _ Z).
Qed.

Lemma carry0_nil (Z : side) :
  cfgCarry 0%nat [] Z -[ tm ]->+ cfgRet 0%nat [] Z.
Proof.
  unfold cfgCarry, cfgRet; cbn [encU encDigit].
  pose proof (step_D_four_zeros (const S0) Z) as H.
  rewrite <- !const_unfold in H.
  exact H.
Qed.

Lemma carry1_step0 (L : list nat) (Z : side) :
  cfgCarry 1%nat (0%nat :: L) Z -[ tm ]->+ cfgCarry 1%nat L (encOp 0%nat Z).
Proof.
  unfold cfgCarry, encOp; cbn [encU encDigit].
  do 2 step_once.
  apply evstep_refl.
Qed.

Lemma carry1_step1 (L : list nat) (Z : side) :
  cfgCarry 1%nat (1%nat :: L) Z -[ tm ]->+ cfgCarry 1%nat L (encOp 1%nat Z).
Proof.
  unfold cfgCarry, encOp; cbn [encU encDigit].
  do 3 step_once.
  apply evstep_refl.
Qed.

Lemma carry1_step2 (L : list nat) (Z : side) :
  cfgCarry 1%nat (2%nat :: L) Z -[ tm ]->+ cfgCarry 0%nat L (encOp 2%nat Z).
Proof.
  unfold cfgCarry, encOp; cbn [encU encDigit].
  do 7 step_once.
  apply evstep_refl.
Qed.

Lemma carry1_wall (a : nat) (L : list nat) (Z : side) :
  cfgCarry 1%nat (S (S (S a)) :: L) Z -[ tm ]->+ cfgRet 0%nat (S a :: L) Z.
Proof.
  exact (carry0_wall a L Z).
Qed.

Lemma carry1_nil (Z : side) :
  cfgCarry 1%nat [] Z -[ tm ]->+ cfgRet 0%nat [] Z.
Proof.
  unfold cfgCarry, cfgRet; cbn [encU encDigit].
  pose proof (step_D_four_zeros (const S0) Z) as H.
  rewrite <- !const_unfold in H.
  exact H.
Qed.

Lemma ret0_op0 (M : list nat) (Z : side) :
  cfgRet 0%nat M (encOp 0%nat Z) -[ tm ]->* cfgRet 1%nat M Z.
Proof.
  unfold cfgRet, encOp; cbn.
  apply evstep_refl.
Qed.

Lemma ret0_op1 (M : list nat) (Z : side) :
  cfgRet 0%nat M (encOp 1%nat Z) -[ tm ]->* cfgRet 0%nat (1%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 3 step_once.
  apply evstep_refl.
Qed.

Lemma ret0_op2 (M : list nat) (Z : side) :
  cfgRet 0%nat M (encOp 2%nat Z) -[ tm ]->* cfgRet 2%nat (0%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 4 step_once.
  apply evstep_refl.
Qed.

Lemma ret1_op0 (M : list nat) (Z : side) :
  cfgRet 1%nat M (encOp 0%nat Z) -[ tm ]->* cfgRet 0%nat (2%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 8 step_once.
  apply evstep_refl.
Qed.

Lemma ret1_op1 (M : list nat) (Z : side) :
  cfgRet 1%nat M (encOp 1%nat Z) -[ tm ]->* cfgRet 2%nat (0%nat :: 0%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 8 step_once.
  apply evstep_refl.
Qed.

Lemma ret1_op2 (M : list nat) (Z : side) :
  cfgRet 1%nat M (encOp 2%nat Z) -[ tm ]->* cfgRet 3%nat (2%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 8 step_once.
  apply evstep_refl.
Qed.

Lemma ret2_op0 (M : list nat) (Z : side) :
  cfgRet 2%nat M (encOp 0%nat Z) -[ tm ]->* cfgRet 2%nat (0%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 4 step_once.
  apply evstep_refl.
Qed.

Lemma ret2_op1 (M : list nat) (Z : side) :
  cfgRet 2%nat M (encOp 1%nat Z) -[ tm ]->* cfgRet 0%nat (2%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 8 step_once.
  apply evstep_refl.
Qed.

Lemma ret2_op2 (M : list nat) (Z : side) :
  cfgRet 2%nat M (encOp 2%nat Z) -[ tm ]->* cfgRet 1%nat (0%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 4 step_once.
  apply evstep_refl.
Qed.

Lemma ret3_op0 (M : list nat) (Z : side) :
  cfgRet 3%nat M (encOp 0%nat Z) -[ tm ]->* cfgRet 0%nat (1%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 3 step_once.
  apply evstep_refl.
Qed.

Lemma ret3_op2 (M : list nat) (Z : side) :
  cfgRet 3%nat M (encOp 2%nat Z) -[ tm ]->* cfgRet 3%nat (1%nat :: M) Z.
Proof.
  unfold cfgRet, encOp; cbn [encU encDigit].
  do 3 step_once.
  apply evstep_refl.
Qed.

Lemma close_ret0 (M : list nat) :
  cfgRet 0%nat M (const S0) -[ tm ]->+ cfgSweep (1%nat :: M).
Proof.
  unfold cfgRet, cfgSweep; cbn [encU encDigit hd tl].
  do 5 step_once.
  apply evstep_refl.
Qed.

Lemma close_ret1 (M : list nat) :
  cfgRet 1%nat M (const S0) -[ tm ]->+ cfgSweep (1%nat :: M).
Proof.
  unfold cfgRet, cfgSweep; cbn [encU encDigit].
  do 5 step_once.
  apply evstep_refl.
Qed.

Lemma close_ret2 (M : list nat) :
  cfgRet 2%nat M (const S0) -[ tm ]->+ cfgSweep (1%nat :: M).
Proof.
  exact (close_ret0 M).
Qed.

Fixpoint stepFwdHitWall (c : nat) (L : list nat) (rop : list nat) : list nat * list nat :=
  match L with
  | [] => ([], rop)
  | a :: L' =>
    match c with
    | O =>
      match a with
      | O => stepFwdHitWall 1%nat L' (1%nat :: rop)
      | S O => stepFwdHitWall 0%nat L' (2%nat :: rop)
      | S (S k) => (S k :: L', rop)
      end
    | S _ =>
      match a with
      | O => stepFwdHitWall 1%nat L' (0%nat :: rop)
      | S O => stepFwdHitWall 1%nat L' (1%nat :: rop)
      | S (S O) => stepFwdHitWall 0%nat L' (2%nat :: rop)
      | S (S (S k)) => (S k :: L', rop)
      end
    end
  end.

Lemma stepFwdHitWall_sound (L : list nat) :
  forall (c : nat) (rop : list nat) (Z : side),
  (c = 0%nat \/ c = 1%nat) ->
  cfgCarry c L (encRevOps rop Z) -[ tm ]->+
  cfgRet 0%nat (fst (stepFwdHitWall c L rop)) (encRevOps (snd (stepFwdHitWall c L rop)) Z).
Proof.
  induction L as [|a L' IH]; intros c rop Z [Hc | Hc]; subst c; cbn [stepFwdHitWall fst snd].
  - exact (carry0_nil (encRevOps rop Z)).
  - exact (carry1_nil (encRevOps rop Z)).
  - destruct a as [|[|k]].
    + eapply progress_trans; [exact (carry0_step0 L' (encRevOps rop Z)) |].
      exact (IH 1%nat (1%nat :: rop) Z (or_intror eq_refl)).
    + eapply progress_trans; [exact (carry0_step1 L' (encRevOps rop Z)) |].
      exact (IH 0%nat (2%nat :: rop) Z (or_introl eq_refl)).
    + exact (carry0_wall k L' (encRevOps rop Z)).
  - destruct a as [|[|[|k]]].
    + eapply progress_trans; [exact (carry1_step0 L' (encRevOps rop Z)) |].
      exact (IH 1%nat (0%nat :: rop) Z (or_intror eq_refl)).
    + eapply progress_trans; [exact (carry1_step1 L' (encRevOps rop Z)) |].
      exact (IH 1%nat (1%nat :: rop) Z (or_intror eq_refl)).
    + eapply progress_trans; [exact (carry1_step2 L' (encRevOps rop Z)) |].
      exact (IH 0%nat (2%nat :: rop) Z (or_introl eq_refl)).
    + exact (carry1_wall k L' (encRevOps rop Z)).
Qed.

Definition stepBwdOne (r op : nat) : option (nat * list nat) :=
  match r, op with
  | O, O => Some (1%nat, [])
  | O, S O => Some (0%nat, [1%nat])
  | O, _ => Some (2%nat, [0%nat])
  | S O, O => Some (0%nat, [2%nat])
  | S O, S O => Some (2%nat, [0%nat; 0%nat])
  | S O, _ => Some (3%nat, [2%nat])
  | S (S O), O => Some (2%nat, [0%nat])
  | S (S O), S O => Some (0%nat, [2%nat])
  | S (S O), _ => Some (1%nat, [0%nat])
  | S (S (S O)), O => Some (0%nat, [1%nat])
  | S (S (S O)), S O => None
  | S (S (S O)), _ => Some (3%nat, [1%nat])
  | _, _ => None
  end.

Lemma stepBwdOne_sound (r op r' : nat) (emit M : list nat) (Z : side) :
  stepBwdOne r op = Some (r', emit) ->
  cfgRet r M (encOp op Z) -[ tm ]->* cfgRet r' (emit ++ M) Z.
Proof.
  destruct r as [|[|[|[|r]]]]; destruct op as [|[|op]]; cbn [stepBwdOne];
    intro H; try discriminate; inversion H; subst; clear H; cbn [app].
  - exact (ret0_op0 M Z).
  - exact (ret0_op1 M Z).
  - exact (ret0_op2 M Z).
  - exact (ret1_op0 M Z).
  - exact (ret1_op1 M Z).
  - exact (ret1_op2 M Z).
  - exact (ret2_op0 M Z).
  - exact (ret2_op1 M Z).
  - exact (ret2_op2 M Z).
  - exact (ret3_op0 M Z).
  - exact (ret3_op2 M Z).
Qed.

Fixpoint bwdChunkAux (r : nat) (rop : list nat) (acc : list nat) : option (nat * list nat) :=
  match rop with
  | [] => Some (r, acc)
  | op :: rop' =>
    match stepBwdOne r op with
    | Some (r1, emit) => bwdChunkAux r1 rop' (emit ++ acc)
    | None => None
    end
  end.

Definition bwdChunk (r : nat) (rop : list nat) : option (nat * list nat) :=
  bwdChunkAux r rop [].

Lemma bwdChunkAux_acc (rop : list nat) :
  forall r acc r' out extra,
  bwdChunkAux r rop acc = Some (r', out) ->
  bwdChunkAux r rop (acc ++ extra) = Some (r', out ++ extra).
Proof.
  induction rop as [|op rop' IH]; intros r acc r' out extra H; cbn in *.
  - inversion H; subst; reflexivity.
  - destruct (stepBwdOne r op) as [[r1 emit]|]; [|discriminate].
    rewrite app_assoc.
    exact (IH r1 (emit ++ acc) r' out extra H).
Qed.

Lemma bwdChunkAux_app (r1 r2 : list nat) :
  forall f acc,
  bwdChunkAux f (r1 ++ r2) acc =
  match bwdChunkAux f r1 acc with
  | Some (f1, acc1) => bwdChunkAux f1 r2 acc1
  | None => None
  end.
Proof.
  induction r1 as [|op r1' IH]; intros f acc; cbn; [reflexivity |].
  destruct (stepBwdOne f op) as [[f1 emit]|]; [exact (IH f1 (emit ++ acc)) | reflexivity].
Qed.

Lemma bwdChunkAux_sound (rop : list nat) :
  forall r r' acc out Z,
  bwdChunkAux r rop acc = Some (r', out) ->
  cfgRet r acc (encRevOps rop Z) -[ tm ]->* cfgRet r' out Z.
Proof.
  induction rop as [|op rop' IH]; intros r r' acc out Z H; cbn in *.
  - inversion H; subst; apply evstep_refl.
  - destruct (stepBwdOne r op) as [[r1 emit]|] eqn:Hs; [|discriminate].
    eapply evstep_trans.
    + exact (stepBwdOne_sound r op r1 emit acc (encRevOps rop' Z) Hs).
    + exact (IH r1 r' (emit ++ acc) out Z H).
Qed.

Lemma bwdChunk_sound (rop : list nat) (r r' : nat) (pref M : list nat) (Z : side) :
  bwdChunk r rop = Some (r', pref) ->
  cfgRet r M (encRevOps rop Z) -[ tm ]->* cfgRet r' (pref ++ M) Z.
Proof.
  intro H. unfold bwdChunk in H.
  pose proof (bwdChunkAux_acc rop r [] r' pref M H) as Hacc.
  cbn [app] in Hacc.
  exact (bwdChunkAux_sound rop r r' M (pref ++ M) Z Hacc).
Qed.

Definition stepConcrete (L : list nat) : option (list nat) :=
  let '(rem, rop) := stepFwdHitWall 0%nat L [0%nat] in
  match bwdChunk 0%nat rop with
  | Some (O, pref) => Some (1%nat :: (pref ++ rem))
  | Some (S O, pref) => Some (1%nat :: (pref ++ rem))
  | Some (S (S O), pref) => Some (1%nat :: (pref ++ rem))
  | _ => None
  end.

Lemma stepConcrete_sound (L L' : list nat) :
  stepConcrete L = Some L' ->
  cfgSweep L -[ tm ]->+ cfgSweep L'.
Proof.
  unfold stepConcrete.
  pose proof (progress_trans tm _ _ _ (launch_sweep L)
    (stepFwdHitWall_sound L 0%nat [0%nat] (const S0) (or_introl eq_refl))) as H1.
  destruct (stepFwdHitWall 0%nat L [0%nat]) as [rem rop]; cbn [fst snd] in H1.
  destruct (bwdChunk 0%nat rop) as [[r pref]|] eqn:Hb; [|discriminate].
  pose proof (progress_evstep_trans tm _ _ _ H1
    (bwdChunk_sound rop 0%nat r pref rem (const S0) Hb)) as H12.
  destruct r as [|[|[|r]]]; intro H; try discriminate; inversion H; subst L'.
  - exact (progress_trans tm _ _ _ H12 (close_ret0 (pref ++ rem))).
  - exact (progress_trans tm _ _ _ H12 (close_ret1 (pref ++ rem))).
  - exact (progress_trans tm _ _ _ H12 (close_ret2 (pref ++ rem))).
Qed.

Fixpoint iterConcrete (n : nat) (L : list nat) : option (list nat) :=
  match n with
  | O => Some L
  | S n' =>
    match stepConcrete L with
    | Some L1 => iterConcrete n' L1
    | None => None
    end
  end.

Lemma iterConcrete_sound (n : nat) :
  forall L L',
  iterConcrete (S n) L = Some L' ->
  cfgSweep L -[ tm ]->+ cfgSweep L'.
Proof.
  induction n as [|n' IH]; intros L L' H; cbn [iterConcrete] in H.
  - destruct (stepConcrete L) as [L1|] eqn:Hs; [|discriminate].
    inversion H; subst L1.
    exact (stepConcrete_sound L L' Hs).
  - destruct (stepConcrete L) as [L1|] eqn:Hs; [|discriminate].
    exact (progress_trans tm _ _ _ (stepConcrete_sound L L1 Hs) (IH L1 L' H)).
Qed.

(* ========================================================================== *)
(* Layer 2: Parametric Word Algebra, Canonicalizer & Symbolic Transducer      *)
(* ========================================================================== *)

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma nat_list_eqb_eq (xs : list nat) :
  forall ys, nat_list_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs' IH]; intros [|y ys'] H; cbn in H; try discriminate.
  - reflexivity.
  - apply Bool.andb_true_iff in H as [Hx Hxs].
    apply Nat.eqb_eq in Hx. subst y.
    f_equal. exact (IH ys' Hxs).
Qed.

Definition list_nonempty {X : Type} (xs : list X) : bool :=
  match xs with
  | [] => false
  | _ :: _ => true
  end.

Record SymSeg : Type := mkSeg {
  word : list nat;
  cM : N;
  cP : N;
  cQ : N;
  b : N
}.

Definition symseg_eqb (s1 s2 : SymSeg) : bool :=
  nat_list_eqb (word s1) (word s2) &&
  N.eqb (cM s1) (cM s2) &&
  N.eqb (cP s1) (cP s2) &&
  N.eqb (cQ s1) (cQ s2) &&
  N.eqb (b s1) (b s2).

Lemma symseg_eqb_eq (s1 s2 : SymSeg) :
  symseg_eqb s1 s2 = true -> s1 = s2.
Proof.
  destruct s1, s2; unfold symseg_eqb; cbn.
  repeat rewrite Bool.andb_true_iff.
  intros [[[[Hw HM] HP] HQ] Hb].
  apply nat_list_eqb_eq in Hw.
  apply N.eqb_eq in HM.
  apply N.eqb_eq in HP.
  apply N.eqb_eq in HQ.
  apply N.eqb_eq in Hb.
  congruence.
Qed.

Fixpoint list_symseg_eqb (xs ys : list SymSeg) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => symseg_eqb x y && list_symseg_eqb xs' ys'
  | _, _ => false
  end.

Lemma list_symseg_eqb_eq (xs : list SymSeg) :
  forall ys, list_symseg_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs' IH]; intros [|y ys'] H; cbn in H; try discriminate.
  - reflexivity.
  - apply Bool.andb_true_iff in H as [Hx Hxs].
    f_equal; [exact (symseg_eqb_eq x y Hx) | exact (IH ys' Hxs)].
Qed.

Definition isLitSeg (sg : SymSeg) : bool :=
  N.eqb (cM sg) 0 && N.eqb (cP sg) 0 && N.eqb (cQ sg) 0.

Definition isUnitSeg (sg : SymSeg) : bool :=
  isLitSeg sg && N.eqb (b sg) 1.

Definition repWord (w : list nat) (n : N) : list nat :=
  match n with
  | N0 => []
  | Npos p => Pos.iter (fun acc => w ++ acc) [] p
  end.

Lemma repWord_0 (w : list nat) : repWord w 0 = [].
Proof. reflexivity. Qed.

Lemma repWord_succ (w : list nat) (n : N) :
  repWord w (N.succ n) = w ++ repWord w n.
Proof.
  destruct n as [|p]; [reflexivity |].
  cbn [N.succ repWord].
  apply Pos.iter_succ.
Qed.

Lemma repWord_1 (w : list nat) : repWord w 1 = w.
Proof.
  change 1 with (N.succ 0).
  rewrite repWord_succ, repWord_0, app_nil_r.
  reflexivity.
Qed.

Lemma repWord_add (w : list nat) (a b0 : N) :
  repWord w (a + b0) = repWord w a ++ repWord w b0.
Proof.
  induction a as [|a IHa] using N.peano_ind.
  - rewrite N.add_0_l, repWord_0. reflexivity.
  - rewrite N.add_succ_l, !repWord_succ, IHa, app_assoc. reflexivity.
Qed.

Lemma repWord_mul (w : list nat) (a b0 : N) :
  repWord w (a * b0) = repWord (repWord w a) b0.
Proof.
  induction b0 as [|b0 IHb] using N.peano_ind.
  - rewrite N.mul_0_r, !repWord_0. reflexivity.
  - rewrite N.mul_succ_r, N.add_comm, repWord_add, repWord_succ, IHb. reflexivity.
Qed.

Lemma repWord_comm (w : list nat) (n : N) :
  repWord w n ++ w = w ++ repWord w n.
Proof.
  induction n as [|n IHn] using N.peano_ind.
  - rewrite repWord_0, app_nil_r. reflexivity.
  - rewrite repWord_succ, <- app_assoc, IHn. reflexivity.
Qed.

Lemma rotate_repWord (u : list nat) (x : nat) (n : N) :
  x :: repWord (u ++ [x]) n = repWord (x :: u) n ++ [x].
Proof.
  induction n as [|n IHn] using N.peano_ind.
  - rewrite !repWord_0. reflexivity.
  - rewrite !repWord_succ, <- !app_assoc. cbn [app].
    f_equal. f_equal. exact IHn.
Qed.

Definition evalLin (sg : SymSeg) (vM vP vQ : N) : N :=
  cM sg * vM + cP sg * vP + cQ sg * vQ + b sg.

Definition evalSeg (sg : SymSeg) (vM vP vQ : N) : list nat :=
  repWord (word sg) (evalLin sg vM vP vQ).

Fixpoint evalSym (s : list SymSeg) (vM vP vQ : N) : list nat :=
  match s with
  | [] => []
  | sg :: rest => evalSeg sg vM vP vQ ++ evalSym rest vM vP vQ
  end.

Lemma evalSym_app (s1 s2 : list SymSeg) (vM vP vQ : N) :
  evalSym (s1 ++ s2) vM vP vQ = evalSym s1 vM vP vQ ++ evalSym s2 vM vP vQ.
Proof.
  induction s1 as [|sg rest IH]; [reflexivity | cbn; rewrite IH, app_assoc; reflexivity].
Qed.

Lemma evalSeg_unit (w : list nat) (vM vP vQ : N) :
  evalSeg (mkSeg w 0 0 0 1) vM vP vQ = w.
Proof.
  unfold evalSeg, evalLin; cbn. apply repWord_1.
Qed.

Lemma evalSeg_lit (w : list nat) (k vM vP vQ : N) :
  evalSeg (mkSeg w 0 0 0 k) vM vP vQ = repWord w k.
Proof.
  unfold evalSeg, evalLin; cbn. reflexivity.
Qed.

Lemma isLitSeg_eq (sg : SymSeg) (vM vP vQ : N) :
  isLitSeg sg = true -> evalLin sg vM vP vQ = b sg.
Proof.
  unfold isLitSeg, evalLin.
  repeat rewrite Bool.andb_true_iff.
  intros [[HM HP] HQ].
  apply N.eqb_eq in HM; apply N.eqb_eq in HP; apply N.eqb_eq in HQ.
  lia.
Qed.

Lemma isUnitSeg_eq (sg : SymSeg) (vM vP vQ : N) :
  isUnitSeg sg = true -> evalSeg sg vM vP vQ = word sg.
Proof.
  unfold isUnitSeg. rewrite Bool.andb_true_iff.
  intros [HL Hb]. apply N.eqb_eq in Hb.
  unfold evalSeg. rewrite (isLitSeg_eq sg vM vP vQ HL), Hb.
  apply repWord_1.
Qed.

Definition unrollLitSeg (sg : SymSeg) : SymSeg :=
  if isLitSeg sg then
    if N.leb (b sg) 32 then mkSeg (repWord (word sg) (b sg)) 0 0 0 1
    else sg
  else sg.

Lemma unrollLitSeg_sound (sg : SymSeg) (vM vP vQ : N) :
  evalSeg (unrollLitSeg sg) vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  unfold unrollLitSeg.
  destruct (isLitSeg sg) eqn:HL; [|reflexivity].
  destruct (N.leb (b sg) 32); [|reflexivity].
  rewrite evalSeg_unit. unfold evalSeg.
  rewrite (isLitSeg_eq sg vM vP vQ HL). reflexivity.
Qed.

Fixpoint unrollLitSegs (s : list SymSeg) : list SymSeg :=
  match s with
  | [] => []
  | sg :: rest => unrollLitSeg sg :: unrollLitSegs rest
  end.

Lemma unrollLitSegs_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (unrollLitSegs s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  induction s as [|sg rest IH]; [reflexivity | cbn; rewrite unrollLitSeg_sound, IH; reflexivity].
Qed.

Lemma evalLin_scale (u : list nat) (sg : SymSeg) (mult vM vP vQ : N) :
  evalLin (mkSeg u (mult * cM sg) (mult * cP sg) (mult * cQ sg) (mult * b sg)) vM vP vQ =
  mult * evalLin sg vM vP vQ.
Proof.
  unfold evalLin; cbn; lia.
Qed.

Definition tryNormPeriodOpt (len d : nat) (sg : SymSeg) : option SymSeg :=
  if Nat.leb (d + d)%nat len then
    let q_nat := Nat.div len d in
    if Nat.leb 2%nat q_nat && Nat.eqb (d * q_nat)%nat len then
      let mult := N.of_nat q_nat in
      let u := firstn d (word sg) in
      if nat_list_eqb (repWord u mult) (word sg) then
        Some (mkSeg u (mult * cM sg) (mult * cP sg) (mult * cQ sg) (mult * b sg))
      else None
    else None
  else None.

Lemma tryNormPeriodOpt_sound (d : nat) (sg sg' : SymSeg) (vM vP vQ : N) :
  tryNormPeriodOpt (List.length (word sg)) d sg = Some sg' ->
  evalSeg sg' vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  unfold tryNormPeriodOpt.
  destruct (Nat.leb (d + d)%nat _); [|discriminate].
  destruct (Nat.leb 2%nat _ && Nat.eqb _ _); [|discriminate].
  destruct (nat_list_eqb _ (word sg)) eqn:Hw; [|discriminate].
  intro H; inversion H; subst sg'; clear H.
  apply nat_list_eqb_eq in Hw.
  unfold evalSeg at 1; cbn [word].
  rewrite evalLin_scale, repWord_mul, Hw.
  reflexivity.
Qed.

Fixpoint tryNormPeriodsOpt (len : nat) (ds : list nat) (sg : SymSeg) : option SymSeg :=
  match ds with
  | [] => None
  | d :: ds' =>
    match tryNormPeriodOpt len d sg with
    | Some res => Some res
    | None => tryNormPeriodsOpt len ds' sg
    end
  end.

Lemma tryNormPeriodsOpt_sound (ds : list nat) :
  forall sg sg' vM vP vQ,
  tryNormPeriodsOpt (List.length (word sg)) ds sg = Some sg' ->
  evalSeg sg' vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  induction ds as [|d ds' IH]; intros sg sg' vM vP vQ H;
    cbn [tryNormPeriodsOpt] in H; [discriminate |].
  destruct (tryNormPeriodOpt (List.length (word sg)) d sg) as [res|] eqn:Hd.
  - inversion H; subst res. exact (tryNormPeriodOpt_sound d sg sg' vM vP vQ Hd).
  - exact (IH sg sg' vM vP vQ H).
Qed.

Definition normSegOpt (sg : SymSeg) : option SymSeg :=
  if isUnitSeg sg then None
  else if isLitSeg sg && N.leb (b sg) 3 then
    Some (mkSeg (repWord (word sg) (b sg)) 0 0 0 1)
  else
    let len := List.length (word sg) in
    if Nat.leb 2%nat len then
      tryNormPeriodsOpt len [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat] sg
    else None.

Lemma normSegOpt_sound (sg sg' : SymSeg) (vM vP vQ : N) :
  normSegOpt sg = Some sg' ->
  evalSeg sg' vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  unfold normSegOpt.
  destruct (isUnitSeg sg); [discriminate |].
  destruct (isLitSeg sg && N.leb (b sg) 3) eqn:HLb.
  - intro H; inversion H; subst sg'; clear H.
    apply Bool.andb_true_iff in HLb as [HL _].
    rewrite evalSeg_unit. unfold evalSeg.
    rewrite (isLitSeg_eq sg vM vP vQ HL). reflexivity.
  - destruct (Nat.leb 2%nat (List.length (word sg))); [|discriminate].
    apply tryNormPeriodsOpt_sound.
Qed.

Fixpoint normSegs (s : list SymSeg) : list SymSeg :=
  match s with
  | [] => []
  | sg :: rest =>
    match normSegOpt sg with
    | Some sg' => sg' :: normSegs rest
    | None => sg :: normSegs rest
    end
  end.

Lemma normSegs_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (normSegs s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  induction s as [|sg rest IH]; [reflexivity | cbn].
  destruct (normSegOpt sg) as [sg'|] eqn:Hn; cbn.
  - rewrite (normSegOpt_sound sg sg' vM vP vQ Hn), IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition rule1 (s1 s2 : SymSeg) : option (list SymSeg) :=
  if isUnitSeg s1 then
    if isUnitSeg s2 then Some [mkSeg (word s1 ++ word s2) 0 0 0 1]
    else None
  else None.

Lemma rule1_sound (s1 s2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  rule1 s1 s2 = Some res ->
  evalSym res vM vP vQ = evalSeg s1 vM vP vQ ++ evalSeg s2 vM vP vQ.
Proof.
  unfold rule1.
  destruct (isUnitSeg s1) eqn:H1; [|discriminate].
  destruct (isUnitSeg s2) eqn:H2; [|discriminate].
  intro H; inversion H; subst res; clear H.
  cbn [evalSym]. rewrite app_nil_r, evalSeg_unit.
  rewrite (isUnitSeg_eq s1 vM vP vQ H1), (isUnitSeg_eq s2 vM vP vQ H2).
  reflexivity.
Qed.

Definition rule2a (s1 s2 : SymSeg) : option (list SymSeg) :=
  if nat_list_eqb (word s1) (word s2) then
    Some [mkSeg (word s1) (cM s1 + cM s2) (cP s1 + cP s2) (cQ s1 + cQ s2) (b s1 + b s2)]
  else None.

Lemma rule2a_sound (s1 s2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  rule2a s1 s2 = Some res ->
  evalSym res vM vP vQ = evalSeg s1 vM vP vQ ++ evalSeg s2 vM vP vQ.
Proof.
  unfold rule2a.
  destruct (nat_list_eqb (word s1) (word s2)) eqn:Hw; [|discriminate].
  intro H; inversion H; subst res; clear H.
  apply nat_list_eqb_eq in Hw.
  cbn [evalSym]. rewrite app_nil_r.
  unfold evalSeg; cbn [word].
  replace (evalLin (mkSeg (word s1) (cM s1 + cM s2) (cP s1 + cP s2) (cQ s1 + cQ s2) (b s1 + b s2)) vM vP vQ)
    with (evalLin s1 vM vP vQ + evalLin s2 vM vP vQ)
    by (unfold evalLin; cbn; lia).
  rewrite repWord_add, Hw. reflexivity.
Qed.

Definition rule2b (s1 s2 : SymSeg) : option (list SymSeg) :=
  if isUnitSeg s1 && negb (isUnitSeg s2) then
    let len1 := List.length (word s1) in
    let len2 := List.length (word s2) in
    if Nat.ltb len2 len1 then
      let k := Nat.sub len1 len2 in
      if nat_list_eqb (skipn k (word s1)) (word s2) then
        Some [mkSeg (firstn k (word s1)) 0 0 0 1; mkSeg (word s2) (cM s2) (cP s2) (cQ s2) (b s2 + 1)]
      else None
    else None
  else None.

Lemma rule2b_sound (s1 s2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  rule2b s1 s2 = Some res ->
  evalSym res vM vP vQ = evalSeg s1 vM vP vQ ++ evalSeg s2 vM vP vQ.
Proof.
  unfold rule2b.
  destruct (isUnitSeg s1 && negb (isUnitSeg s2)) eqn:Hu; [|discriminate].
  set (len1 := List.length (word s1)).
  set (len2 := List.length (word s2)).
  destruct (Nat.ltb len2 len1); [|discriminate].
  set (k := Nat.sub len1 len2).
  destruct (nat_list_eqb (skipn k (word s1)) (word s2)) eqn:Hskip; [|discriminate].
  intro H; inversion H; subst res; clear H.
  apply Bool.andb_true_iff in Hu as [H1 _].
  apply nat_list_eqb_eq in Hskip.
  pose proof (firstn_skipn k (word s1)) as Hfs.
  rewrite Hskip in Hfs.
  cbn [evalSym]. rewrite app_nil_r, evalSeg_unit, (isUnitSeg_eq s1 vM vP vQ H1).
  unfold evalSeg; cbn [word].
  replace (evalLin (mkSeg (word s2) (cM s2) (cP s2) (cQ s2) (b s2 + 1)) vM vP vQ)
    with (N.succ (evalLin s2 vM vP vQ))
    by (unfold evalLin; cbn; lia).
  rewrite repWord_succ, app_assoc, Hfs.
  reflexivity.
Qed.

Definition rule3 (s1 s2 : SymSeg) : option (list SymSeg) :=
  if isUnitSeg s1 && negb (isUnitSeg s2) then
    if list_nonempty (word s1) && Nat.leb 2%nat (List.length (word s2)) then
      let ch := List.last (word s2) 0%nat in
      if Nat.eqb (List.last (word s1) 0%nat) ch then
        let lw_pref := removelast (word s1) in
        if nat_list_eqb (lw_pref ++ [ch]) (word s1) then
          let u := removelast (word s2) in
          if nat_list_eqb (u ++ [ch]) (word s2) then
            match lw_pref with
            | [] => Some [mkSeg (ch :: u) (cM s2) (cP s2) (cQ s2) (b s2); mkSeg [ch] 0 0 0 1]
            | _ :: _ => Some [mkSeg lw_pref 0 0 0 1; mkSeg (ch :: u) (cM s2) (cP s2) (cQ s2) (b s2); mkSeg [ch] 0 0 0 1]
            end
          else None
        else None
      else None
    else None
  else None.

Lemma rule3_sound (s1 s2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  rule3 s1 s2 = Some res ->
  evalSym res vM vP vQ = evalSeg s1 vM vP vQ ++ evalSeg s2 vM vP vQ.
Proof.
  unfold rule3.
  destruct (isUnitSeg s1 && negb (isUnitSeg s2)) eqn:Hg; [|discriminate].
  destruct (list_nonempty (word s1) && Nat.leb 2%nat (List.length (word s2))); [|discriminate].
  destruct (Nat.eqb _ _); [|discriminate].
  set (ch := List.last (word s2) 0%nat).
  set (lw_pref := removelast (word s1)).
  set (u := removelast (word s2)).
  destruct (nat_list_eqb (lw_pref ++ [ch]) (word s1)) eqn:Hw1; [|discriminate].
  destruct (nat_list_eqb (u ++ [ch]) (word s2)) eqn:Hw2; [|discriminate].
  apply Bool.andb_true_iff in Hg as [H1 _].
  apply nat_list_eqb_eq in Hw1.
  apply nat_list_eqb_eq in Hw2.
  pose proof (rotate_repWord u ch (evalLin s2 vM vP vQ)) as Hrot.
  rewrite Hw2 in Hrot.
  destruct lw_pref as [|p ps]; intro H; inversion H; subst res; clear H.
  - cbn [app] in Hw1.
    cbn [evalSym]. rewrite app_nil_r, evalSeg_unit, (isUnitSeg_eq s1 vM vP vQ H1).
    unfold evalSeg, evalLin in *; cbn [word cM cP cQ b] in *.
    rewrite <- Hrot, <- Hw1. reflexivity.
  - cbn [evalSym]. rewrite app_nil_r, !evalSeg_unit, (isUnitSeg_eq s1 vM vP vQ H1).
    unfold evalSeg, evalLin in *; cbn [word cM cP cQ b] in *.
    rewrite <- Hrot.
    change ((p :: ps) ++ ch :: repWord (word s2) (cM s2 * vM + cP s2 * vP + cQ s2 * vQ + b s2))
      with ((p :: ps) ++ [ch] ++ repWord (word s2) (cM s2 * vM + cP s2 * vP + cQ s2 * vQ + b s2)).
    rewrite app_assoc, Hw1. reflexivity.
Qed.

Definition rule4 (s1 s2 : SymSeg) : option (list SymSeg) :=
  if isUnitSeg s2 && negb (isUnitSeg s1) then
    let rw_suf := skipn (List.length (word s1)) (word s2) in
    if list_nonempty rw_suf && nat_list_eqb (word s1 ++ rw_suf) (word s2) then
      Some [mkSeg (word s1) (cM s1) (cP s1) (cQ s1) (b s1 + 1); mkSeg rw_suf 0 0 0 1]
    else None
  else None.

Lemma rule4_sound (s1 s2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  rule4 s1 s2 = Some res ->
  evalSym res vM vP vQ = evalSeg s1 vM vP vQ ++ evalSeg s2 vM vP vQ.
Proof.
  unfold rule4.
  destruct (isUnitSeg s2 && negb (isUnitSeg s1)) eqn:Hu; [|discriminate].
  set (rw_suf := skipn (List.length (word s1)) (word s2)).
  destruct (list_nonempty rw_suf && nat_list_eqb (word s1 ++ rw_suf) (word s2)) eqn:Hsuf; [|discriminate].
  intro H; inversion H; subst res; clear H.
  apply Bool.andb_true_iff in Hu as [H2 _].
  apply Bool.andb_true_iff in Hsuf as [_ Hw].
  apply nat_list_eqb_eq in Hw.
  cbn [evalSym]. rewrite app_nil_r, evalSeg_unit, (isUnitSeg_eq s2 vM vP vQ H2).
  unfold evalSeg; cbn [word].
  replace (evalLin (mkSeg (word s1) (cM s1) (cP s1) (cQ s1) (b s1 + 1)) vM vP vQ)
    with (evalLin s1 vM vP vQ + 1)
    by (unfold evalLin; cbn; lia).
  rewrite repWord_add, repWord_1, <- app_assoc, Hw.
  reflexivity.
Qed.

Definition tryRewritePair (n1 n2 : SymSeg) : option (list SymSeg) :=
  match rule1 n1 n2 with
  | Some res => Some res
  | None =>
    match rule2a n1 n2 with
    | Some res => Some res
    | None =>
      match rule2b n1 n2 with
      | Some res => Some res
      | None =>
        match rule3 n1 n2 with
        | Some res => Some res
        | None => rule4 n1 n2
        end
      end
    end
  end.

Lemma tryRewritePair_sound (n1 n2 : SymSeg) (res : list SymSeg) (vM vP vQ : N) :
  tryRewritePair n1 n2 = Some res ->
  evalSym res vM vP vQ = evalSeg n1 vM vP vQ ++ evalSeg n2 vM vP vQ.
Proof.
  unfold tryRewritePair.
  destruct (rule1 n1 n2) as [r|] eqn:H1; [intro H; inversion H; subst; exact (rule1_sound n1 n2 res vM vP vQ H1) |].
  destruct (rule2a n1 n2) as [r|] eqn:H2a; [intro H; inversion H; subst; exact (rule2a_sound n1 n2 res vM vP vQ H2a) |].
  destruct (rule2b n1 n2) as [r|] eqn:H2b; [intro H; inversion H; subst; exact (rule2b_sound n1 n2 res vM vP vQ H2b) |].
  destruct (rule3 n1 n2) as [r|] eqn:H3; [intro H; inversion H; subst; exact (rule3_sound n1 n2 res vM vP vQ H3) |].
  exact (rule4_sound n1 n2 res vM vP vQ).
Qed.

Fixpoint rewritePassAux (fuel : nat) (s : list SymSeg) : option (list SymSeg) :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | [] => None
    | [_] => None
    | s1 :: s2 :: rest =>
      match tryRewritePair s1 s2 with
      | Some rep =>
        match rewritePassAux fuel' rest with
        | Some out => Some (rep ++ out)
        | None => Some (rep ++ rest)
        end
      | None =>
        match rewritePassAux fuel' (s2 :: rest) with
        | Some out => Some (s1 :: out)
        | None => None
        end
      end
    end
  end.

Lemma rewritePassAux_sound (fuel : nat) :
  forall s s' vM vP vQ,
  rewritePassAux fuel s = Some s' ->
  evalSym s' vM vP vQ = evalSym s vM vP vQ.
Proof.
  induction fuel as [|fuel' IH]; intros s s' vM vP vQ H; [discriminate |].
  destruct s as [|s1 [|s2 rest]]; cbn [rewritePassAux] in H; try discriminate.
  destruct (tryRewritePair s1 s2) as [rep|] eqn:Hp.
  - destruct (rewritePassAux fuel' rest) as [out|] eqn:Hr; inversion H; subst s'; clear H.
    + rewrite evalSym_app, (tryRewritePair_sound s1 s2 rep vM vP vQ Hp),
        (IH rest out vM vP vQ Hr), <- app_assoc. reflexivity.
    + rewrite evalSym_app, (tryRewritePair_sound s1 s2 rep vM vP vQ Hp),
        <- app_assoc. reflexivity.
  - destruct (rewritePassAux fuel' (s2 :: rest)) as [out|] eqn:Hr; [|discriminate].
    inversion H; subst s'; clear H.
    cbn [evalSym]. rewrite (IH (s2 :: rest) out vM vP vQ Hr). reflexivity.
Qed.

Fixpoint canonLoop (fuel : nat) (s : list SymSeg) : list SymSeg :=
  match fuel with
  | O => s
  | S fuel' =>
    match rewritePassAux fuel256 s with
    | Some s' => canonLoop fuel' s'
    | None => s
    end
  end.

Lemma canonLoop_sound (fuel : nat) :
  forall s vM vP vQ,
  evalSym (canonLoop fuel s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  induction fuel as [|fuel' IH]; intros s vM vP vQ; [reflexivity | cbn [canonLoop]].
  destruct (rewritePassAux fuel256 s) as [s'|] eqn:Hr; [|reflexivity].
  rewrite IH, (rewritePassAux_sound fuel256 s s' vM vP vQ Hr). reflexivity.
Qed.

Definition canonRaw (s : list SymSeg) : list SymSeg :=
  canonLoop fuel64 (normSegs s).

Lemma canonRaw_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (canonRaw s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  unfold canonRaw. rewrite canonLoop_sound, normSegs_sound. reflexivity.
Qed.

Definition canonCollapse (s : list SymSeg) : list SymSeg :=
  canonRaw (unrollLitSegs s).

Lemma canonCollapse_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (canonCollapse s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  unfold canonCollapse. rewrite canonRaw_sound, unrollLitSegs_sound. reflexivity.
Qed.

Definition canonMode (collapse : bool) (s : list SymSeg) : list SymSeg :=
  if collapse then canonCollapse s else canonRaw s.

Lemma canonMode_sound (collapse : bool) (s : list SymSeg) (vM vP vQ : N) :
  evalSym (canonMode collapse s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  destruct collapse; [apply canonCollapse_sound | apply canonRaw_sound].
Qed.

Fixpoint findRepeatCount (u : list nat) (fuel : nat) (w : list nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
    if nat_list_eqb (firstn (List.length u) w) u && list_nonempty u then
      S (findRepeatCount u fuel' (skipn (List.length u) w))
    else O
  end.

Definition tryFactorHead (d : nat) (w : list nat) : option (SymSeg * list nat) :=
  let u := firstn d w in
  if nat_list_eqb u (firstn d (skipn d w)) then
    if nat_list_eqb (repWord u 5) (firstn (5 * d)%nat w) then
      let k := findRepeatCount u fuel512 w in
      if Nat.leb 5%nat k then
        let rest := skipn (k * d)%nat w in
        let kN := N.of_nat k in
        if nat_list_eqb (repWord u kN ++ rest) w then
          match normSegOpt (mkSeg u 0 0 0 kN) with
          | Some sg => Some (sg, rest)
          | None => Some (mkSeg u 0 0 0 kN, rest)
          end
        else None
      else None
    else None
  else None.

Lemma tryFactorHead_sound (d : nat) (w : list nat) (sg : SymSeg) (rest : list nat) (vM vP vQ : N) :
  tryFactorHead d w = Some (sg, rest) ->
  evalSeg sg vM vP vQ ++ rest = w.
Proof.
  unfold tryFactorHead.
  destruct (nat_list_eqb _ (firstn d (skipn d w))); [|discriminate].
  destruct (nat_list_eqb (repWord _ 5) _); [|discriminate].
  destruct (Nat.leb 5%nat _); [|discriminate].
  set (u := firstn d w).
  set (k := findRepeatCount u fuel512 w).
  set (kN := N.of_nat k).
  destruct (nat_list_eqb (repWord u kN ++ skipn (k * d)%nat w) w) eqn:Hw; [|discriminate].
  apply nat_list_eqb_eq in Hw.
  destruct (normSegOpt (mkSeg u 0 0 0 kN)) as [sg'|] eqn:Hn;
    intro H; inversion H; subst; clear H.
  - rewrite (normSegOpt_sound _ _ vM vP vQ Hn), evalSeg_lit. exact Hw.
  - rewrite evalSeg_lit. exact Hw.
Qed.

Fixpoint tryFactorHeads (ds : list nat) (w : list nat) : option (SymSeg * list nat) :=
  match ds with
  | [] => None
  | d :: ds' =>
    match tryFactorHead d w with
    | Some res => Some res
    | None => tryFactorHeads ds' w
    end
  end.

Lemma tryFactorHeads_sound (ds : list nat) :
  forall w sg rest vM vP vQ,
  tryFactorHeads ds w = Some (sg, rest) ->
  evalSeg sg vM vP vQ ++ rest = w.
Proof.
  induction ds as [|d ds' IH]; intros w sg rest vM vP vQ H; cbn in H; [discriminate |].
  destruct (tryFactorHead d w) as [res|] eqn:Hd.
  - inversion H; subst res. exact (tryFactorHead_sound d w sg rest vM vP vQ Hd).
  - exact (IH w sg rest vM vP vQ H).
Qed.

Definition emitPrefWord (pref : list nat) : list SymSeg :=
  match pref with
  | [] => []
  | _ :: _ => [mkSeg pref 0 0 0 1]
  end.

Lemma emitPrefWord_sound (pref : list nat) (vM vP vQ : N) :
  evalSym (emitPrefWord pref) vM vP vQ = pref.
Proof.
  destruct pref as [|p ps]; [reflexivity | cbn [emitPrefWord evalSym]; rewrite app_nil_r, evalSeg_unit; reflexivity].
Qed.

Fixpoint factorWordLoop (fuel : nat) (pref w : list nat) : list SymSeg :=
  match fuel with
  | O => emitPrefWord (pref ++ w)
  | S fuel' =>
    match tryFactorHeads [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat] w with
    | Some (sg, rest) => emitPrefWord pref ++ (sg :: factorWordLoop fuel' [] rest)
    | None =>
      match w with
      | [] => emitPrefWord pref
      | x :: xs => factorWordLoop fuel' (pref ++ [x]) xs
      end
    end
  end.

Lemma factorWordLoop_sound (fuel : nat) :
  forall pref w vM vP vQ,
  evalSym (factorWordLoop fuel pref w) vM vP vQ = pref ++ w.
Proof.
  induction fuel as [|fuel' IH]; intros pref w vM vP vQ; cbn [factorWordLoop].
  - apply emitPrefWord_sound.
  - destruct (tryFactorHeads [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat] w)
      as [[sg rest]|] eqn:Hf.
    + rewrite evalSym_app, emitPrefWord_sound; cbn [evalSym].
      rewrite IH; cbn [app].
      rewrite (tryFactorHeads_sound _ w sg rest vM vP vQ Hf). reflexivity.
    + destruct w as [|x xs].
      * rewrite app_nil_r. apply emitPrefWord_sound.
      * rewrite IH, <- app_assoc; reflexivity.
Qed.

Definition factorUnitSeg (sg : SymSeg) : list SymSeg :=
  if isUnitSeg sg then
    if Nat.leb 35%nat (List.length (word sg)) then
      factorWordLoop (S (List.length (word sg))) [] (word sg)
    else [sg]
  else [sg].

Lemma factorUnitSeg_sound (sg : SymSeg) (vM vP vQ : N) :
  evalSym (factorUnitSeg sg) vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  unfold factorUnitSeg.
  destruct (isUnitSeg sg) eqn:Hu; [|cbn; apply app_nil_r].
  destruct (Nat.leb 35%nat (List.length (word sg))); [|cbn; apply app_nil_r].
  rewrite factorWordLoop_sound; cbn [app].
  symmetry; exact (isUnitSeg_eq sg vM vP vQ Hu).
Qed.

Fixpoint factorUnitSegs (s : list SymSeg) : list SymSeg :=
  match s with
  | [] => []
  | sg :: rest => factorUnitSeg sg ++ factorUnitSegs rest
  end.

Lemma factorUnitSegs_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (factorUnitSegs s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  induction s as [|sg rest IH]; [reflexivity | cbn].
  rewrite evalSym_app, factorUnitSeg_sound, IH. reflexivity.
Qed.

Definition canonFunctional (s : list SymSeg) : list SymSeg :=
  canonRaw (factorUnitSegs (canonRaw s)).

Lemma canonFunctional_sound (s : list SymSeg) (vM vP vQ : N) :
  evalSym (canonFunctional s) vM vP vQ = evalSym s vM vP vQ.
Proof.
  unfold canonFunctional.
  rewrite canonRaw_sound, factorUnitSegs_sound, canonRaw_sound. reflexivity.
Qed.

Fixpoint stepFwdNoWall (c : nat) (L : list nat) (rop : list nat) : option (nat * list nat) :=
  match L with
  | [] => Some (c, rop)
  | a :: L' =>
    match c with
    | O =>
      match a with
      | O => stepFwdNoWall 1%nat L' (1%nat :: rop)
      | S O => stepFwdNoWall 0%nat L' (2%nat :: rop)
      | S (S _) => None
      end
    | S _ =>
      match a with
      | O => stepFwdNoWall 1%nat L' (0%nat :: rop)
      | S O => stepFwdNoWall 1%nat L' (1%nat :: rop)
      | S (S O) => stepFwdNoWall 0%nat L' (2%nat :: rop)
      | S (S (S _)) => None
      end
    end
  end.

Lemma stepFwdNoWall_append (w : list nat) :
  forall c acc c' rop rest prev_rop,
  stepFwdNoWall c w acc = Some (c', rop) ->
  stepFwdHitWall c (w ++ rest) (acc ++ prev_rop) =
    stepFwdHitWall c' rest (rop ++ prev_rop).
Proof.
  induction w as [|a w' IH]; intros c acc c' rop rest prev_rop H.
  - cbn in H. inversion H; subst. reflexivity.
  - destruct c as [|c0]; cbn in H |- *.
    + destruct a as [|[|k]]; try discriminate.
      * exact (IH 1%nat (1%nat :: acc) c' rop rest prev_rop H).
      * exact (IH 0%nat (2%nat :: acc) c' rop rest prev_rop H).
    + destruct a as [|[|[|k]]]; try discriminate.
      * exact (IH 1%nat (0%nat :: acc) c' rop rest prev_rop H).
      * exact (IH 1%nat (1%nat :: acc) c' rop rest prev_rop H).
      * exact (IH 0%nat (2%nat :: acc) c' rop rest prev_rop H).
Qed.

Lemma stepFwdNoWall_spec (w : list nat) (c c' : nat) (rop rest prev_rop : list nat) :
  stepFwdNoWall c w [] = Some (c', rop) ->
  stepFwdHitWall c (w ++ rest) prev_rop =
    stepFwdHitWall c' rest (rop ++ prev_rop).
Proof.
  exact (stepFwdNoWall_append w c [] c' rop rest prev_rop).
Qed.

Lemma stepFwdNoWall_rep (w : list nat) (c : nat) (rop : list nat) :
  stepFwdNoWall c w [] = Some (c, rop) ->
  forall (n : N) rest prev_rop,
  stepFwdHitWall c (repWord w n ++ rest) prev_rop =
    stepFwdHitWall c rest (repWord rop n ++ prev_rop).
Proof.
  intro H. induction n as [|n IH] using N.peano_ind; intros rest prev_rop.
  - rewrite !repWord_0. reflexivity.
  - rewrite repWord_succ, <- app_assoc, (stepFwdNoWall_spec w c c rop _ prev_rop H),
      (IH rest (rop ++ prev_rop)), repWord_succ, app_assoc, (repWord_comm rop n).
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma stepFwdHitWall_append (w : list nat) :
  forall c acc rest prev_rop,
  stepFwdNoWall c w acc = None ->
  stepFwdHitWall c (w ++ rest) (acc ++ prev_rop) =
    (fst (stepFwdHitWall c w acc) ++ rest, snd (stepFwdHitWall c w acc) ++ prev_rop).
Proof.
  induction w as [|a w' IH]; intros c acc rest prev_rop H; [discriminate |].
  destruct c as [|c0]; cbn in H |- *.
  - destruct a as [|[|k]].
    + exact (IH 1%nat (1%nat :: acc) rest prev_rop H).
    + exact (IH 0%nat (2%nat :: acc) rest prev_rop H).
    + reflexivity.
  - destruct a as [|[|[|k]]].
    + exact (IH 1%nat (0%nat :: acc) rest prev_rop H).
    + exact (IH 1%nat (1%nat :: acc) rest prev_rop H).
    + exact (IH 0%nat (2%nat :: acc) rest prev_rop H).
    + reflexivity.
Qed.

Lemma stepFwdHitWall_spec (w : list nat) (c : nat) (rest prev_rop : list nat) :
  stepFwdNoWall c w [] = None ->
  stepFwdHitWall c (w ++ rest) prev_rop =
    (fst (stepFwdHitWall c w []) ++ rest, snd (stepFwdHitWall c w []) ++ prev_rop).
Proof.
  exact (stepFwdHitWall_append w c [] rest prev_rop).
Qed.

Definition emitRemSeg (sg : SymSeg) : list SymSeg :=
  if isLitSeg sg then
    if N.eqb (b sg) 0 then [] else [sg]
  else [sg].

Lemma emitRemSeg_sound (sg : SymSeg) (vM vP vQ : N) :
  evalSym (emitRemSeg sg) vM vP vQ = evalSeg sg vM vP vQ.
Proof.
  unfold emitRemSeg.
  destruct (isLitSeg sg) eqn:HL; [|cbn; apply app_nil_r].
  destruct (N.eqb (b sg) 0) eqn:Hb; [|cbn; apply app_nil_r].
  apply N.eqb_eq in Hb.
  cbn [evalSym]. unfold evalSeg.
  rewrite (isLitSeg_eq sg vM vP vQ HL), Hb, repWord_0. reflexivity.
Qed.

Lemma evalSeg_peel (sg : SymSeg) (vM vP vQ : N) :
  N.eqb (b sg) 0 = false ->
  evalSeg sg vM vP vQ =
    word sg ++ evalSeg (mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1)) vM vP vQ.
Proof.
  intro Hb. apply N.eqb_neq in Hb.
  unfold evalSeg; cbn [word].
  replace (evalLin sg vM vP vQ)
    with (N.succ (evalLin (mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1)) vM vP vQ))
    by (unfold evalLin; cbn; lia).
  apply repWord_succ.
Qed.

Fixpoint fwdSymLoop (fuel : nat) (c : nat) (in_segs rev_fsegs : list SymSeg)
  : option (list SymSeg * list SymSeg * list SymSeg) :=
  match fuel with
  | O => None
  | S fuel' =>
    match in_segs with
    | [] => None
    | sg :: rest =>
      match stepFwdNoWall c (word sg) [] with
      | Some (c', rop) =>
        if Nat.eqb c' c then
          fwdSymLoop fuel' c rest (mkSeg rop (cM sg) (cP sg) (cQ sg) (b sg) :: rev_fsegs)
        else if N.eqb (b sg) 0 then None
        else
          let sg' := mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1) in
          fwdSymLoop fuel' c' (emitRemSeg sg' ++ rest) (mkSeg rop 0 0 0 1 :: rev_fsegs)
      | None =>
        if N.eqb (b sg) 0 then None
        else
          let '(rem_w, rop) := stepFwdHitWall c (word sg) [] in
          let sg' := mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1) in
          Some (emitPrefWord rem_w ++ emitRemSeg sg', mkSeg rop 0 0 0 1 :: rev_fsegs, rest)
      end
    end
  end.

Lemma fwdSymLoop_sound (fuel : nat) :
  forall c in_segs rev_fsegs rem_segs out_fsegs tail_segs vM vP vQ tail,
  fwdSymLoop fuel c in_segs rev_fsegs = Some (rem_segs, out_fsegs, tail_segs) ->
  stepFwdHitWall c (evalSym in_segs vM vP vQ ++ tail) (evalSym rev_fsegs vM vP vQ) =
    (evalSym (rem_segs ++ tail_segs) vM vP vQ ++ tail, evalSym out_fsegs vM vP vQ).
Proof.
  induction fuel as [|fuel' IH];
    intros c in_segs rev_fsegs rem_segs out_fsegs tail_segs vM vP vQ tail H; [discriminate |].
  destruct in_segs as [|sg rest]; cbn [fwdSymLoop] in H; [discriminate |].
  destruct (stepFwdNoWall c (word sg) []) as [[c' rop]|] eqn:Hnw.
  - destruct (Nat.eqb c' c) eqn:Hcc.
    + apply Nat.eqb_eq in Hcc; subst c'.
      cbn [evalSym]. rewrite <- app_assoc.
      unfold evalSeg at 1.
      rewrite (stepFwdNoWall_rep (word sg) c rop Hnw (evalLin sg vM vP vQ)).
      exact (IH c rest (mkSeg rop (cM sg) (cP sg) (cQ sg) (b sg) :: rev_fsegs)
        rem_segs out_fsegs tail_segs vM vP vQ tail H).
    + destruct (N.eqb (b sg) 0) eqn:Hb; [discriminate |].
      set (sg' := mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1)) in *.
      pose proof (IH c' (emitRemSeg sg' ++ rest) (mkSeg rop 0 0 0 1 :: rev_fsegs)
        rem_segs out_fsegs tail_segs vM vP vQ tail H) as Hrec.
      cbn [evalSym]. rewrite (evalSeg_peel sg vM vP vQ Hb), <- !app_assoc.
      rewrite (stepFwdNoWall_spec (word sg) c c' rop _ _ Hnw).
      cbn [evalSym] in Hrec.
      rewrite evalSym_app, emitRemSeg_sound, evalSeg_unit, <- app_assoc in Hrec.
      exact Hrec.
  - destruct (N.eqb (b sg) 0) eqn:Hb; [discriminate |].
    pose proof (stepFwdHitWall_spec (word sg) c
      (evalSeg (mkSeg (word sg) (cM sg) (cP sg) (cQ sg) (b sg - 1)) vM vP vQ ++
        evalSym rest vM vP vQ ++ tail)
      (evalSym rev_fsegs vM vP vQ) Hnw) as Hwall.
    destruct (stepFwdHitWall c (word sg) []) as [rem_w rop]; cbn [fst snd] in Hwall.
    inversion H; subst; clear H.
    cbn [evalSym]. rewrite (evalSeg_peel sg vM vP vQ Hb), <- !app_assoc.
    rewrite Hwall.
    rewrite !evalSym_app, emitPrefWord_sound, emitRemSeg_sound, evalSeg_unit, <- !app_assoc.
    reflexivity.
Qed.

Lemma bwdChunk_append (r1 r2 : list nat) (f f1 f2 : nat) (em1 em2 : list nat) :
  bwdChunk f r1 = Some (f1, em1) ->
  bwdChunk f1 r2 = Some (f2, em2) ->
  bwdChunk f (r1 ++ r2) = Some (f2, em2 ++ em1).
Proof.
  unfold bwdChunk. intros H1 H2.
  rewrite bwdChunkAux_app, H1.
  exact (bwdChunkAux_acc r2 f1 [] f2 em2 em1 H2).
Qed.

Lemma bwdChunk_rep (u : list nat) (f : nat) (em : list nat) :
  bwdChunk f u = Some (f, em) ->
  forall n : N, bwdChunk f (repWord u n) = Some (f, repWord em n).
Proof.
  intro H. induction n as [|n IH] using N.peano_ind.
  - rewrite !repWord_0. reflexivity.
  - rewrite repWord_succ, (bwdChunk_append u (repWord u n) f f f em (repWord em n) H IH),
      repWord_comm, <- repWord_succ.
    reflexivity.
Qed.

Definition BwdRel (f : nat) (w acc : list nat) (f' : nat) (acc' : list nat) : Prop :=
  exists em : list nat, bwdChunk f w = Some (f', em) /\ acc' = em ++ acc.

Lemma BwdRel_nil (f : nat) (acc : list nat) : BwdRel f [] acc f acc.
Proof. exists (@nil nat); split; reflexivity. Qed.

Lemma BwdRel_append {f f1 f2 : nat} {w1 w2 acc acc1 acc2 : list nat} :
  BwdRel f w1 acc f1 acc1 ->
  BwdRel f1 w2 acc1 f2 acc2 ->
  BwdRel f (w1 ++ w2) acc f2 acc2.
Proof.
  intros [em1 [Hb1 ->]] [em2 [Hb2 ->]].
  exists (em2 ++ em1).
  split; [exact (bwdChunk_append w1 w2 f f1 f2 em1 em2 Hb1 Hb2) | rewrite <- !app_assoc; reflexivity].
Qed.

Lemma BwdRel_chunk {f f' : nat} {w em : list nat} (acc : list SymSeg) (vM vP vQ : N) :
  bwdChunk f w = Some (f', em) ->
  BwdRel f w (evalSym acc vM vP vQ) f' (evalSym (emitPrefWord em ++ acc) vM vP vQ).
Proof.
  intro H. exists em; split; [exact H |].
  rewrite evalSym_app, emitPrefWord_sound. reflexivity.
Qed.

Lemma BwdRel_rep {f : nat} {u : list nat} (sg : SymSeg) (acc : list SymSeg) (vM vP vQ : N) :
  bwdChunk f u = Some (f, word sg) ->
  BwdRel f (repWord u (evalLin sg vM vP vQ)) (evalSym acc vM vP vQ)
    f (evalSym (sg :: acc) vM vP vQ).
Proof.
  intro H. exists (repWord (word sg) (evalLin sg vM vP vQ)).
  split; [exact (bwdChunk_rep u f (word sg) H (evalLin sg vM vP vQ)) | reflexivity].
Qed.

Lemma evalLin_div_rem (d cM' cP' cQ' q r : N) (fsg : SymSeg) (w : list nat) (vM vP vQ : N) :
  d * cM' = cM fsg ->
  d * cP' = cP fsg ->
  d * cQ' = cQ fsg ->
  d * q + r = b fsg ->
  evalSeg fsg vM vP vQ =
    repWord (repWord (word fsg) d) (evalLin (mkSeg w cM' cP' cQ' q) vM vP vQ) ++
      repWord (word fsg) r.
Proof.
  intros EM EP EQ Eb.
  unfold evalSeg.
  replace (evalLin fsg vM vP vQ)
    with (d * evalLin (mkSeg w cM' cP' cQ' q) vM vP vQ + r)
    by (unfold evalLin; cbn; lia).
  rewrite repWord_add, repWord_mul. reflexivity.
Qed.

Definition tryBwdSteady (d : N) (f : nat) (fsg : SymSeg) (acc : list SymSeg)
  : option (nat * list SymSeg) :=
  let cM' := N.div (cM fsg) d in
  let cP' := N.div (cP fsg) d in
  let cQ' := N.div (cQ fsg) d in
  let q := N.div (b fsg) d in
  let r := N.modulo (b fsg) d in
  if N.eqb (d * cM') (cM fsg) then
    if N.eqb (d * cP') (cP fsg) then
      if N.eqb (d * cQ') (cQ fsg) then
        if N.eqb (d * q + r) (b fsg) then
          match bwdChunk f (repWord (word fsg) d) with
          | None => None
          | Some (f_test, em_block) =>
            if Nat.eqb f_test f then
              match bwdChunk f (repWord (word fsg) r) with
              | None => None
              | Some (f_end, em_rem) =>
                Some (f_end, emitPrefWord em_rem ++ (mkSeg em_block cM' cP' cQ' q :: acc))
              end
            else None
          end
        else None
      else None
    else None
  else None.

Lemma tryBwdSteady_sound (d : N) (f f_end : nat) (fsg : SymSeg) (acc acc' : list SymSeg)
  (vM vP vQ : N) :
  tryBwdSteady d f fsg acc = Some (f_end, acc') ->
  BwdRel f (evalSeg fsg vM vP vQ) (evalSym acc vM vP vQ) f_end (evalSym acc' vM vP vQ).
Proof.
  unfold tryBwdSteady.
  set (cM' := N.div (cM fsg) d).
  set (cP' := N.div (cP fsg) d).
  set (cQ' := N.div (cQ fsg) d).
  set (q := N.div (b fsg) d).
  set (r := N.modulo (b fsg) d).
  destruct (N.eqb (d * cM') (cM fsg)) eqn:HM; [|discriminate].
  destruct (N.eqb (d * cP') (cP fsg)) eqn:HP; [|discriminate].
  destruct (N.eqb (d * cQ') (cQ fsg)) eqn:HQ; [|discriminate].
  destruct (N.eqb (d * q + r) (b fsg)) eqn:Hb; [|discriminate].
  destruct (bwdChunk f (repWord (word fsg) d)) as [[f_test em_block]|] eqn:Hblk; [|discriminate].
  destruct (Nat.eqb f_test f) eqn:Hft; [|discriminate].
  apply Nat.eqb_eq in Hft; subst f_test.
  destruct (bwdChunk f (repWord (word fsg) r)) as [[f_e em_rem]|] eqn:Hrem; [|discriminate].
  intro H; inversion H; subst; clear H.
  apply N.eqb_eq in HM; apply N.eqb_eq in HP; apply N.eqb_eq in HQ; apply N.eqb_eq in Hb.
  rewrite (evalLin_div_rem d cM' cP' cQ' q r fsg em_block vM vP vQ HM HP HQ Hb).
  eapply BwdRel_append.
  - exact (BwdRel_rep (mkSeg em_block cM' cP' cQ' q) acc vM vP vQ Hblk).
  - exact (BwdRel_chunk (mkSeg em_block cM' cP' cQ' q :: acc) vM vP vQ Hrem).
Qed.

Fixpoint tryBwdDiv (d : N) (peel_fuel : nat) (f : nat) (fsg : SymSeg) (acc : list SymSeg)
  : option (nat * list SymSeg) :=
  match peel_fuel with
  | O => None
  | S peel_fuel' =>
    match tryBwdSteady d f fsg acc with
    | Some res => Some res
    | None =>
      if N.eqb (b fsg) 0 then None
      else
        match bwdChunk f (word fsg) with
        | None => None
        | Some (nf, em_one) =>
          tryBwdDiv d peel_fuel' nf (mkSeg (word fsg) (cM fsg) (cP fsg) (cQ fsg) (b fsg - 1))
            (emitPrefWord em_one ++ acc)
        end
    end
  end.

Lemma tryBwdDiv_sound (d : N) (peel_fuel : nat) :
  forall f f_end fsg acc acc' vM vP vQ,
  tryBwdDiv d peel_fuel f fsg acc = Some (f_end, acc') ->
  BwdRel f (evalSeg fsg vM vP vQ) (evalSym acc vM vP vQ) f_end (evalSym acc' vM vP vQ).
Proof.
  induction peel_fuel as [|peel_fuel' IH];
    intros f f_end fsg acc acc' vM vP vQ H; [discriminate | cbn [tryBwdDiv] in H].
  destruct (tryBwdSteady d f fsg acc) as [res|] eqn:Hst.
  - inversion H; subst res. exact (tryBwdSteady_sound d f f_end fsg acc acc' vM vP vQ Hst).
  - destruct (N.eqb (b fsg) 0) eqn:Hb; [discriminate |].
    destruct (bwdChunk f (word fsg)) as [[nf em_one]|] eqn:Hc; [|discriminate].
    rewrite (evalSeg_peel fsg vM vP vQ Hb).
    eapply BwdRel_append.
    + exact (BwdRel_chunk acc vM vP vQ Hc).
    + exact (IH nf f_end _ (emitPrefWord em_one ++ acc) acc' vM vP vQ H).
Qed.

Fixpoint tryBwdDivs (ds : list N) (f : nat) (fsg : SymSeg) (acc : list SymSeg)
  : option (nat * list SymSeg) :=
  match ds with
  | [] => None
  | d :: ds' =>
    match tryBwdDiv d 7%nat f fsg acc with
    | Some res => Some res
    | None => tryBwdDivs ds' f fsg acc
    end
  end.

Lemma tryBwdDivs_sound (ds : list N) :
  forall f f_end fsg acc acc' vM vP vQ,
  tryBwdDivs ds f fsg acc = Some (f_end, acc') ->
  BwdRel f (evalSeg fsg vM vP vQ) (evalSym acc vM vP vQ) f_end (evalSym acc' vM vP vQ).
Proof.
  induction ds as [|d ds' IH]; intros f f_end fsg acc acc' vM vP vQ H;
    cbn [tryBwdDivs] in H; [discriminate |].
  destruct (tryBwdDiv d 7%nat f fsg acc) as [res|] eqn:Hd.
  - inversion H; subst res. exact (tryBwdDiv_sound d 7%nat f f_end fsg acc acc' vM vP vQ Hd).
  - exact (IH f f_end fsg acc acc' vM vP vQ H).
Qed.

Definition bwdSeg (f : nat) (fsg : SymSeg) (acc : list SymSeg) : option (nat * list SymSeg) :=
  if isUnitSeg fsg then
    match bwdChunk f (word fsg) with
    | Some (nf, em) => Some (nf, emitPrefWord em ++ acc)
    | None => None
    end
  else tryBwdDivs [1; 2; 3; 6] f fsg acc.

Lemma bwdSeg_sound (f f_end : nat) (fsg : SymSeg) (acc acc' : list SymSeg) (vM vP vQ : N) :
  bwdSeg f fsg acc = Some (f_end, acc') ->
  BwdRel f (evalSeg fsg vM vP vQ) (evalSym acc vM vP vQ) f_end (evalSym acc' vM vP vQ).
Proof.
  unfold bwdSeg.
  destruct (isUnitSeg fsg) eqn:Hu.
  - destruct (bwdChunk f (word fsg)) as [[nf em]|] eqn:Hc; [|discriminate].
    intro H; inversion H; subst; clear H.
    rewrite (isUnitSeg_eq fsg vM vP vQ Hu).
    exact (BwdRel_chunk acc vM vP vQ Hc).
  - apply tryBwdDivs_sound.
Qed.

Fixpoint bwdSymPass (f : nat) (rev_fsegs acc : list SymSeg) : option (nat * list SymSeg) :=
  match rev_fsegs with
  | [] => Some (f, acc)
  | fsg :: rest =>
    match bwdSeg f fsg acc with
    | Some (f1, acc1) => bwdSymPass f1 rest acc1
    | None => None
    end
  end.

Lemma bwdSymPass_sound (rev_fsegs : list SymSeg) :
  forall f f_end acc acc' vM vP vQ,
  bwdSymPass f rev_fsegs acc = Some (f_end, acc') ->
  BwdRel f (evalSym rev_fsegs vM vP vQ) (evalSym acc vM vP vQ) f_end (evalSym acc' vM vP vQ).
Proof.
  induction rev_fsegs as [|fsg rest IH]; intros f f_end acc acc' vM vP vQ H;
    cbn [bwdSymPass] in H.
  - inversion H; subst. apply BwdRel_nil.
  - destruct (bwdSeg f fsg acc) as [[f1 acc1]|] eqn:Hs; [|discriminate].
    cbn [evalSym].
    eapply BwdRel_append.
    + exact (bwdSeg_sound f f1 fsg acc acc1 vM vP vQ Hs).
    + exact (IH f1 f_end acc1 acc' vM vP vQ H).
Qed.

Definition splitHead (s : list SymSeg) : list SymSeg * list SymSeg :=
  match s with
  | s1 :: s2 :: s3 :: rest => ([s1; s2; s3], rest)
  | _ => (s, [])
  end.

Lemma splitHead_sound (s : list SymSeg) :
  fst (splitHead s) ++ snd (splitHead s) = s.
Proof.
  destruct s as [|s1 [|s2 [|s3 rest]]]; reflexivity.
Qed.

Definition symStepFunctional (in_segs : list SymSeg) : option (list SymSeg) :=
  match fwdSymLoop fuel512 0%nat in_segs [mkSeg [0%nat] 0 0 0 1] with
  | None => None
  | Some (rem_segs, rev_fsegs, tail_segs) =>
    match bwdSymPass 0%nat rev_fsegs rem_segs with
    | None => None
    | Some (f_end, acc_segs) =>
      match f_end with
      | O | S O | S (S O) =>
        let '(hd_s, tl_s) := splitHead tail_segs in
        Some (canonRaw (mkSeg [1%nat] 0 0 0 1 :: (acc_segs ++ hd_s)) ++ tl_s)
      | _ => None
      end
    end
  end.

Theorem symStepFunctional_sound (in_segs out_segs : list SymSeg) (vM vP vQ : N) (tail : list nat) :
  symStepFunctional in_segs = Some out_segs ->
  stepConcrete (evalSym in_segs vM vP vQ ++ tail) = Some (evalSym out_segs vM vP vQ ++ tail).
Proof.
  unfold symStepFunctional.
  destruct (fwdSymLoop fuel512 0%nat in_segs [mkSeg [0%nat] 0 0 0 1])
    as [[[rem_segs rev_fsegs] tail_segs]|] eqn:Hf; [|discriminate].
  pose proof (fwdSymLoop_sound fuel512 0%nat in_segs [mkSeg [0%nat] 0 0 0 1]
    rem_segs rev_fsegs tail_segs vM vP vQ tail Hf) as Hfwd.
  cbn [evalSym] in Hfwd; rewrite evalSeg_unit, app_nil_r in Hfwd.
  destruct (bwdSymPass 0%nat rev_fsegs rem_segs) as [[f_end acc_segs]|] eqn:Hb; [|discriminate].
  destruct (bwdSymPass_sound rev_fsegs 0%nat f_end rem_segs acc_segs vM vP vQ Hb)
    as [em [Hbwd Hacc]].
  pose proof (splitHead_sound tail_segs) as Hsh.
  destruct (splitHead tail_segs) as [hd_s tl_s]; cbn [fst snd] in Hsh.
  unfold stepConcrete. rewrite Hfwd, Hbwd.
  assert (Hout :
    evalSym (canonRaw (mkSeg [1%nat] 0 0 0 1 :: (acc_segs ++ hd_s)) ++ tl_s) vM vP vQ ++ tail =
    1%nat :: (em ++ (evalSym (rem_segs ++ tail_segs) vM vP vQ ++ tail))).
  { rewrite evalSym_app, canonRaw_sound; cbn [evalSym].
    rewrite evalSeg_unit, <- Hsh, !evalSym_app, Hacc.
    rewrite <- !app_assoc. reflexivity. }
  destruct f_end as [|[|[|f_more]]]; intro H; try discriminate;
    inversion H; subst out_segs; f_equal; symmetry; exact Hout.
Qed.

Fixpoint iterSymStep (n : nat) (s : list SymSeg) : option (list SymSeg) :=
  match n with
  | O => Some s
  | S n' =>
    match symStepFunctional s with
    | Some s1 => iterSymStep n' s1
    | None => None
    end
  end.

Lemma iterSymStep_S (n : nat) (s : list SymSeg) :
  iterSymStep (S n) s =
  match symStepFunctional s with
  | Some s1 => iterSymStep n s1
  | None => None
  end.
Proof. reflexivity. Qed.


Lemma iterSymStep_sound (n : nat) :
  forall s s' vM vP vQ tail,
  iterSymStep (S n) s = Some s' ->
  cfgSweep (evalSym s vM vP vQ ++ tail) -[ tm ]->+ cfgSweep (evalSym s' vM vP vQ ++ tail).
Proof.
  induction n as [|n' IH]; intros s s' vM vP vQ tail H; rewrite iterSymStep_S in H.
  - destruct (symStepFunctional s) as [s1|] eqn:Hs; [|discriminate H].
    cbn [iterSymStep] in H; inversion H; subst s1.
    exact (stepConcrete_sound _ _ (symStepFunctional_sound s s' vM vP vQ tail Hs)).
  - destruct (symStepFunctional s) as [s1|] eqn:Hs; [|discriminate H].
    eapply progress_trans.
    + exact (stepConcrete_sound _ _ (symStepFunctional_sound s s1 vM vP vQ tail Hs)).
    + exact (IH s1 s' vM vP vQ tail H).
Qed.

Inductive LoopSeg : Type :=
| LS_const (w : list nat) (cM0 b0 : N)
| LS_grow (w : list nat) (cM0 b0 r : N)
| LS_drain (w : list nat) (remM remB r : N).

Definition evalLoopSeg (ls : LoopSeg) (vM k q_cnt : N) : list nat :=
  match ls with
  | LS_const w cM0 b0 => repWord w (cM0 * vM + b0)
  | LS_grow w cM0 b0 r => repWord w (cM0 * vM + r * k + b0)
  | LS_drain w remM remB r => repWord w (remM * vM + r * q_cnt + remB)
  end.

Fixpoint evalLoop (lss : list LoopSeg) (vM k q_cnt : N) : list nat :=
  match lss with
  | [] => []
  | ls :: rest => evalLoopSeg ls vM k q_cnt ++ evalLoop rest vM k q_cnt
  end.

Definition loopSegStepLHS (ls : LoopSeg) : SymSeg :=
  match ls with
  | LS_const w cM0 b0 => mkSeg w cM0 0 0 b0
  | LS_grow w cM0 b0 r => mkSeg w cM0 r 0 b0
  | LS_drain w remM remB r => mkSeg w remM 0 r (remB + r)
  end.

Definition loopSegStepRHS (ls : LoopSeg) : SymSeg :=
  match ls with
  | LS_const w cM0 b0 => mkSeg w cM0 0 0 b0
  | LS_grow w cM0 b0 r => mkSeg w cM0 r 0 (b0 + r)
  | LS_drain w remM remB r => mkSeg w remM 0 r remB
  end.

Definition loopSegStart (alpha beta : N) (ls : LoopSeg) : SymSeg :=
  match ls with
  | LS_const w cM0 b0 => mkSeg w cM0 0 0 b0
  | LS_grow w cM0 b0 _ => mkSeg w cM0 0 0 b0
  | LS_drain w remM remB r => mkSeg w (remM + r * alpha) 0 0 (remB + r * beta)
  end.

Definition loopSegEnd (alpha beta : N) (ls : LoopSeg) : SymSeg :=
  match ls with
  | LS_const w cM0 b0 => mkSeg w cM0 0 0 b0
  | LS_grow w cM0 b0 r => mkSeg w (cM0 + r * alpha) 0 0 (b0 + r * beta)
  | LS_drain w remM remB _ => mkSeg w remM 0 0 remB
  end.

Fixpoint loopStepLHS (lss : list LoopSeg) : list SymSeg :=
  match lss with
  | [] => []
  | ls :: rest => loopSegStepLHS ls :: loopStepLHS rest
  end.

Fixpoint loopStepRHS (lss : list LoopSeg) : list SymSeg :=
  match lss with
  | [] => []
  | ls :: rest => loopSegStepRHS ls :: loopStepRHS rest
  end.

Fixpoint loopStart (alpha beta : N) (lss : list LoopSeg) : list SymSeg :=
  match lss with
  | [] => []
  | ls :: rest => loopSegStart alpha beta ls :: loopStart alpha beta rest
  end.

Fixpoint loopEnd (alpha beta : N) (lss : list LoopSeg) : list SymSeg :=
  match lss with
  | [] => []
  | ls :: rest => loopSegEnd alpha beta ls :: loopEnd alpha beta rest
  end.

Lemma loopSegStepLHS_sound (ls : LoopSeg) (vM k q_cnt : N) :
  evalSeg (loopSegStepLHS ls) vM k q_cnt = evalLoopSeg ls vM k (q_cnt + 1).
Proof.
  destruct ls; unfold loopSegStepLHS, evalSeg, evalLin, evalLoopSeg; cbn [word cM cP cQ b]; f_equal; lia.
Qed.

Lemma loopSegStepRHS_sound (ls : LoopSeg) (vM k q_cnt : N) :
  evalSeg (loopSegStepRHS ls) vM k q_cnt = evalLoopSeg ls vM (k + 1) q_cnt.
Proof.
  destruct ls; unfold loopSegStepRHS, evalSeg, evalLin, evalLoopSeg; cbn [word cM cP cQ b]; f_equal; lia.
Qed.

Lemma loopSegStart_sound (alpha beta : N) (ls : LoopSeg) (vM : N) :
  evalSeg (loopSegStart alpha beta ls) vM 0 0 = evalLoopSeg ls vM 0 (alpha * vM + beta).
Proof.
  destruct ls; unfold loopSegStart, evalSeg, evalLin, evalLoopSeg; cbn [word cM cP cQ b]; f_equal; lia.
Qed.

Lemma loopSegEnd_sound (alpha beta : N) (ls : LoopSeg) (vM : N) :
  evalSeg (loopSegEnd alpha beta ls) vM 0 0 = evalLoopSeg ls vM (alpha * vM + beta) 0.
Proof.
  destruct ls; unfold loopSegEnd, evalSeg, evalLin, evalLoopSeg; cbn [word cM cP cQ b]; f_equal; lia.
Qed.

Lemma loopStepLHS_sound (lss : list LoopSeg) (vM k q_cnt : N) :
  evalSym (loopStepLHS lss) vM k q_cnt = evalLoop lss vM k (q_cnt + 1).
Proof.
  induction lss as [|ls rest IH]; [reflexivity | cbn [loopStepLHS evalSym evalLoop]; rewrite loopSegStepLHS_sound, IH; reflexivity].
Qed.

Lemma loopStepRHS_sound (lss : list LoopSeg) (vM k q_cnt : N) :
  evalSym (loopStepRHS lss) vM k q_cnt = evalLoop lss vM (k + 1) q_cnt.
Proof.
  induction lss as [|ls rest IH]; [reflexivity | cbn [loopStepRHS evalSym evalLoop]; rewrite loopSegStepRHS_sound, IH; reflexivity].
Qed.

Lemma loopStart_sound (alpha beta : N) (lss : list LoopSeg) (vM : N) :
  evalSym (loopStart alpha beta lss) vM 0 0 = evalLoop lss vM 0 (alpha * vM + beta).
Proof.
  induction lss as [|ls rest IH]; [reflexivity | cbn [loopStart evalSym evalLoop]; rewrite loopSegStart_sound, IH; reflexivity].
Qed.

Lemma loopEnd_sound (alpha beta : N) (lss : list LoopSeg) (vM : N) :
  evalSym (loopEnd alpha beta lss) vM 0 0 = evalLoop lss vM (alpha * vM + beta) 0.
Proof.
  induction lss as [|ls rest IH]; [reflexivity | cbn [loopEnd evalSym evalLoop]; rewrite loopSegEnd_sound, IH; reflexivity].
Qed.

Definition checkLoopStep (collapse : bool) (stride : nat) (lss : list LoopSeg) : bool :=
  match iterSymStep (S stride) (canonMode collapse (loopStepLHS lss)) with
  | Some out => list_symseg_eqb (canonMode collapse out) (canonMode collapse (loopStepRHS lss))
  | None => false
  end.

Lemma checkLoopStep_sound (collapse : bool) (stride : nat) (lss : list LoopSeg) :
  checkLoopStep collapse stride lss = true ->
  forall vM k q_cnt tail,
  cfgSweep (evalLoop lss vM k (q_cnt + 1) ++ tail) -[ tm ]->+
    cfgSweep (evalLoop lss vM (k + 1) q_cnt ++ tail).
Proof.
  unfold checkLoopStep.
  destruct (iterSymStep (S stride) (canonMode collapse (loopStepLHS lss))) as [out|] eqn:Hi; [|discriminate].
  intro H; apply list_symseg_eqb_eq in H.
  intros vM k q_cnt tail.
  pose proof (iterSymStep_sound stride (canonMode collapse (loopStepLHS lss)) out vM k q_cnt tail Hi) as Hstep.
  rewrite canonMode_sound, loopStepLHS_sound in Hstep.
  assert (Hrhs : evalSym out vM k q_cnt = evalLoop lss vM (k + 1) q_cnt).
  { rewrite <- (canonMode_sound collapse out vM k q_cnt), H, canonMode_sound, loopStepRHS_sound.
    reflexivity. }
  rewrite Hrhs in Hstep. exact Hstep.
Qed.

Lemma evalLoop_iter_star (collapse : bool) (stride : nat) (lss : list LoopSeg) :
  checkLoopStep collapse stride lss = true ->
  forall (q_cnt vM k : N) tail,
  cfgSweep (evalLoop lss vM k q_cnt ++ tail) -[ tm ]->*
    cfgSweep (evalLoop lss vM (k + q_cnt) 0 ++ tail).
Proof.
  intro Hstep.
  induction q_cnt as [|q_cnt IH] using N.peano_ind; intros vM k tail.
  - rewrite N.add_0_r. apply evstep_refl.
  - replace (N.succ q_cnt) with (q_cnt + 1) by lia.
    eapply evstep_trans.
    + apply progress_evstep. exact (checkLoopStep_sound collapse stride lss Hstep vM k q_cnt tail).
    + replace (k + (q_cnt + 1)) with ((k + 1) + q_cnt) by lia.
      exact (IH vM (k + 1) tail).
Qed.

Definition accelSteps (k_len n : nat) (in_segs : list SymSeg) : option (list SymSeg) :=
  match iterSymStep (S n) (firstn k_len in_segs) with
  | Some out => Some (out ++ skipn k_len in_segs)
  | None => None
  end.

Lemma accelSteps_sound (k_len n : nat) (in_segs out_segs : list SymSeg) (vM : N) (tail : list nat) :
  accelSteps k_len n in_segs = Some out_segs ->
  cfgSweep (evalSym in_segs vM 0 0 ++ tail) -[ tm ]->*
    cfgSweep (evalSym out_segs vM 0 0 ++ tail).
Proof.
  unfold accelSteps.
  destruct (iterSymStep (S n) (firstn k_len in_segs)) as [out|] eqn:Hs; [|discriminate].
  intro H; inversion H; subst out_segs; clear H.
  replace (evalSym in_segs vM 0 0 ++ tail)
    with (evalSym (firstn k_len in_segs) vM 0 0 ++ (evalSym (skipn k_len in_segs) vM 0 0 ++ tail))
    by (rewrite app_assoc, <- evalSym_app, firstn_skipn; reflexivity).
  rewrite evalSym_app, <- app_assoc.
  apply progress_evstep.
  exact (iterSymStep_sound n (firstn k_len in_segs) out vM 0 0
    (evalSym (skipn k_len in_segs) vM 0 0 ++ tail) Hs).
Qed.

Definition accelFactor (k_len : nat) (in_segs : list SymSeg) : option (list SymSeg) :=
  Some (canonFunctional (firstn k_len in_segs) ++ skipn k_len in_segs).

Lemma accelFactor_sound (k_len : nat) (in_segs out_segs : list SymSeg) (vM : N) (tail : list nat) :
  accelFactor k_len in_segs = Some out_segs ->
  evalSym out_segs vM 0 0 ++ tail = evalSym in_segs vM 0 0 ++ tail.
Proof.
  unfold accelFactor. intro H; inversion H; subst out_segs; clear H.
  rewrite evalSym_app, canonFunctional_sound, <- evalSym_app, firstn_skipn.
  reflexivity.
Qed.

Definition accelLoop (collapse : bool) (k_len : nat) (in_segs : list SymSeg)
  (stride : nat) (alpha beta : N) (lss : list LoopSeg) : option (list SymSeg) :=
  let act := firstn k_len in_segs in
  let pas := skipn k_len in_segs in
  if list_symseg_eqb (canonMode collapse act) (canonMode collapse (loopStart alpha beta lss)) then
    if checkLoopStep collapse stride lss then
      Some (canonFunctional (loopEnd alpha beta lss) ++ pas)
    else None
  else None.

Lemma accelLoop_sound (collapse : bool) (k_len : nat) (in_segs out_segs : list SymSeg)
  (stride : nat) (alpha beta : N) (lss : list LoopSeg) (vM : N) (tail : list nat) :
  accelLoop collapse k_len in_segs stride alpha beta lss = Some out_segs ->
  cfgSweep (evalSym in_segs vM 0 0 ++ tail) -[ tm ]->*
    cfgSweep (evalSym out_segs vM 0 0 ++ tail).
Proof.
  unfold accelLoop.
  set (act := firstn k_len in_segs).
  set (pas := skipn k_len in_segs).
  destruct (list_symseg_eqb (canonMode collapse act) (canonMode collapse (loopStart alpha beta lss))) eqn:H1;
    [|discriminate].
  destruct (checkLoopStep collapse stride lss) eqn:H2; [|discriminate].
  intro H; inversion H; subst out_segs; clear H.
  apply list_symseg_eqb_eq in H1.
  replace (evalSym in_segs vM 0 0 ++ tail)
    with (evalSym act vM 0 0 ++ (evalSym pas vM 0 0 ++ tail))
    by (unfold act, pas; rewrite app_assoc, <- evalSym_app, firstn_skipn; reflexivity).
  assert (Ein : evalSym act vM 0 0 = evalLoop lss vM 0 (alpha * vM + beta)).
  { rewrite <- (canonMode_sound collapse act vM 0 0), H1, canonMode_sound, loopStart_sound.
    reflexivity. }
  assert (Eout : evalSym (canonFunctional (loopEnd alpha beta lss)) vM 0 0 =
    evalLoop lss vM (0 + (alpha * vM + beta)) 0).
  { rewrite canonFunctional_sound, loopEnd_sound, N.add_0_l. reflexivity. }
  rewrite evalSym_app, <- app_assoc, Ein, Eout.
  exact (evalLoop_iter_star collapse stride lss H2 (alpha * vM + beta) vM 0
    (evalSym pas vM 0 0 ++ tail)).
Qed.

Definition substM (a b0 : N) (sg : SymSeg) : SymSeg :=
  mkSeg (word sg) (cM sg * a) (cP sg) (cQ sg) (cM sg * b0 + b sg).

Lemma substM_sound (a b0 : N) (sg : SymSeg) (vM : N) :
  evalSeg (substM a b0 sg) vM 0 0 = evalSeg sg (a * vM + b0) 0 0.
Proof.
  unfold substM, evalSeg, evalLin; cbn [word cM cP cQ b]; f_equal; lia.
Qed.

Fixpoint substMSegs (a b0 : N) (s : list SymSeg) : list SymSeg :=
  match s with
  | [] => []
  | sg :: rest => substM a b0 sg :: substMSegs a b0 rest
  end.

Lemma substMSegs_sound (a b0 : N) (s : list SymSeg) (vM : N) :
  evalSym (substMSegs a b0 s) vM 0 0 = evalSym s (a * vM + b0) 0 0.
Proof.
  induction s as [|sg rest IH]; [reflexivity | cbn [substMSegs evalSym]; rewrite substM_sound, IH; reflexivity].
Qed.

Inductive TraceOp : Type :=
| TO_steps (k_len : nat) (n : nat)
| TO_factor (k_len : nat)
| TO_loop (collapse : bool) (k_len : nat) (stride : nat) (alpha beta : N) (lss : list LoopSeg).

Fixpoint runTrace (ops : list TraceOp) (s : list SymSeg) : option (list SymSeg) :=
  match ops with
  | [] => Some s
  | TO_steps k_len n :: rest =>
    match accelSteps k_len n s with
    | Some s1 => runTrace rest s1
    | None => None
    end
  | TO_factor k_len :: rest =>
    match accelFactor k_len s with
    | Some s1 => runTrace rest s1
    | None => None
    end
  | TO_loop collapse k_len stride alpha beta lss :: rest =>
    match accelLoop collapse k_len s stride alpha beta lss with
    | Some s1 => runTrace rest s1
    | None => None
    end
  end.

Lemma runTrace_sound (ops : list TraceOp) :
  forall s s' vM tail,
  runTrace ops s = Some s' ->
  cfgSweep (evalSym s vM 0 0 ++ tail) -[ tm ]->*
    cfgSweep (evalSym s' vM 0 0 ++ tail).
Proof.
  induction ops as [|op rest IH]; intros s s' vM tail H; cbn [runTrace] in H.
  - inversion H; subst s'. apply evstep_refl.
  - destruct op as [k_len n | k_len | collapse k_len stride alpha beta lss].
    + destruct (accelSteps k_len n s) as [s1|] eqn:Hs; [|discriminate].
      eapply evstep_trans.
      * exact (accelSteps_sound k_len n s s1 vM tail Hs).
      * exact (IH s1 s' vM tail H).
    + destruct (accelFactor k_len s) as [s1|] eqn:Hf; [|discriminate].
      rewrite <- (accelFactor_sound k_len s s1 vM tail Hf).
      exact (IH s1 s' vM tail H).
    + destruct (accelLoop collapse k_len s stride alpha beta lss) as [s1|] eqn:Hl; [|discriminate].
      eapply evstep_trans.
      * exact (accelLoop_sound collapse k_len s s1 stride alpha beta lss vM tail Hl).
      * exact (IH s1 s' vM tail H).
Qed.

(* ========================================================================== *)
(* Layer 3: Soundness of Prefix & Wave Checkers                               *)
(* ========================================================================== *)

Definition checkPrefixGen (cSteps : nat) (wTpl : list SymSeg) (p0 : list SymSeg) (ops : list TraceOp) : bool :=
  match iterConcrete (S cSteps) [0%nat] with
  | None => false
  | Some c25 =>
    nat_list_eqb c25 (evalSym p0 0 0 0 ++ []) &&
    match runTrace ops p0 with
    | None => false
    | Some out_p =>
      list_symseg_eqb (canonCollapse (firstn 27%nat out_p))
        (canonCollapse (substMSegs 0 0 wTpl ++ [mkSeg [2%nat] 0 0 0 7]))
    end
  end.

Lemma checkPrefixGen_sound (cSteps : nat) (wTpl p0 : list SymSeg) (ops : list TraceOp) :
  checkPrefixGen cSteps wTpl p0 ops = true ->
  exists tail0 : list nat,
    c0 -[ tm ]->+ cfgSweep (evalSym wTpl 0 0 0 ++ tail0).
Proof.
  unfold checkPrefixGen.
  destruct (iterConcrete (S cSteps) [0%nat]) as [c25|] eqn:Hc; [|intro Hbad; discriminate Hbad].
  rewrite Bool.andb_true_iff.
  intros [Heq Htr].
  apply nat_list_eqb_eq in Heq.
  destruct (runTrace ops p0) as [out_p|] eqn:Hr; [|discriminate Htr].
  apply list_symseg_eqb_eq in Htr.
  pose proof (progress_trans tm _ _ _ init_reaches_sweep0
    (iterConcrete_sound cSteps [0%nat] c25 Hc)) as Hinit.
  rewrite Heq in Hinit.
  pose proof (progress_evstep_trans tm _ _ _ Hinit
    (runTrace_sound ops p0 out_p 0 [] Hr)) as Hreach.
  rewrite app_nil_r in Hreach.
  assert (Hhead : evalSym (firstn 27%nat out_p) 0 0 0 =
    evalSym wTpl 0 0 0 ++ evalSym [mkSeg [2%nat] 0 0 0 7] 0 0 0).
  { rewrite <- (canonCollapse_sound (firstn 27%nat out_p) 0 0 0), Htr,
      canonCollapse_sound, evalSym_app, substMSegs_sound.
    reflexivity. }
  assert (Hsplit : evalSym out_p 0 0 0 =
    evalSym wTpl 0 0 0 ++
      (evalSym [mkSeg [2%nat] 0 0 0 7] 0 0 0 ++ evalSym (skipn 27%nat out_p) 0 0 0)).
  { rewrite <- (firstn_skipn 27%nat out_p) at 1.
    rewrite evalSym_app, Hhead, <- app_assoc. reflexivity. }
  rewrite Hsplit in Hreach.
  eexists; exact Hreach.
Qed.

Definition checkWaveGen (wTpl remSeg : list SymSeg) (ops : list TraceOp) : bool :=
  match symStepFunctional wTpl with
  | None => false
  | Some s1 =>
    match runTrace ops s1 with
    | None => false
    | Some out_w =>
      list_symseg_eqb (canonCollapse (firstn 30%nat out_w))
        (canonCollapse (substMSegs 2 16 wTpl ++ remSeg))
    end
  end.

Lemma checkWaveGen_sound (wTpl remSeg : list SymSeg) (ops : list TraceOp) :
  checkWaveGen wTpl remSeg ops = true ->
  forall (vM : N) (tail : list nat),
  exists tail' : list nat,
    cfgSweep (evalSym wTpl vM 0 0 ++ tail) -[ tm ]->+
      cfgSweep (evalSym wTpl (2 * vM + 16) 0 0 ++ tail').
Proof.
  unfold checkWaveGen.
  destruct (symStepFunctional wTpl) as [s1|] eqn:Hs1; [|discriminate].
  destruct (runTrace ops s1) as [out_w|] eqn:Hr; [|discriminate].
  intro Hcl; apply list_symseg_eqb_eq in Hcl.
  intros vM tail.
  pose proof (stepConcrete_sound _ _ (symStepFunctional_sound wTpl s1 vM 0 0 tail Hs1)) as H0.
  pose proof (progress_evstep_trans tm _ _ _ H0
    (runTrace_sound ops s1 out_w vM tail Hr)) as Hreach.
  assert (Hhead : evalSym (firstn 30%nat out_w) vM 0 0 =
    evalSym wTpl (2 * vM + 16) 0 0 ++ evalSym remSeg vM 0 0).
  { rewrite <- (canonCollapse_sound (firstn 30%nat out_w) vM 0 0), Hcl,
      canonCollapse_sound, evalSym_app, substMSegs_sound.
    reflexivity. }
  assert (Hsplit : evalSym out_w vM 0 0 ++ tail =
    evalSym wTpl (2 * vM + 16) 0 0 ++
      (evalSym remSeg vM 0 0 ++ evalSym (skipn 30%nat out_w) vM 0 0 ++ tail)).
  { rewrite <- (firstn_skipn 30%nat out_w) at 1.
    rewrite evalSym_app, Hhead, <- !app_assoc. reflexivity. }
  rewrite Hsplit in Hreach.
  eexists; exact Hreach.
Qed.


(* ========================================================================== *)
(* Layer 4: Certificate Data, VM Verification, and Non-Halting Theorem        *)
(* ========================================================================== *)

Definition seg0 (w : list nat) (b0 : N) : SymSeg := mkSeg w 0 0 0 b0.
Definition segM (w : list nat) (cM0 b0 : N) : SymSeg := mkSeg w cM0 0 0 b0.
Definition segMPQ (w : list nat) (cM0 cP0 cQ0 b0 : N) : SymSeg := mkSeg w cM0 cP0 cQ0 b0.

Arguments seg0 w%_list b0%_N.
Arguments segM w%_list cM0%_N b0%_N.
Arguments segMPQ w%_list cM0%_N cP0%_N cQ0%_N b0%_N.
Arguments LS_const w%_list cM0%_N b0%_N.
Arguments LS_grow w%_list cM0%_N b0%_N r%_N.
Arguments LS_drain w%_list remM%_N remB%_N r%_N.
Arguments TO_steps k_len%_nat n%_nat.
Arguments TO_factor k_len%_nat.
Arguments TO_loop collapse%_bool k_len%_nat stride%_nat alpha%_N beta%_N lss%_list.

Section TraceData.
Local Open Scope nat_scope.

Definition pChk_0 : list SymSeg := [
  seg0 [1] 1;
  seg0 [0; 0; 2] 14;
  seg0 [0; 0; 1; 2; 0; 0; 0; 2; 0; 2; 0; 0; 0; 2; 0; 2] 1;
  seg0 [0] 7;
  seg0 [2; 2; 0; 0; 0; 0; 1] 1;
  seg0 [0; 0; 0; 2; 2] 9;
  seg0 [0] 6;
  seg0 [2; 0; 2] 1;
  seg0 [0] 6;
  seg0 [2; 0; 1; 2; 2; 0; 0; 0; 0; 1; 2; 2; 0; 0; 0; 2; 2; 2; 0; 0; 1; 2; 0; 2; 0; 1; 2] 1;
  seg0 [0] 6
].

Definition waveTemplate : list SymSeg := [
  seg0 [1; 0; 0; 1; 0; 0; 0; 1; 2; 2] 1;
  segM [0; 0; 0; 2; 2; 0; 1] 72 1139;
  seg0 [2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 1] 1;
  segM [2; 0; 2; 0; 0; 0; 2; 0] 12 187;
  seg0 [2; 0; 2; 0; 0; 0; 1; 2; 0; 1; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 2; 0; 1] 1;
  seg0 [2] 5;
  seg0 [0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 1; 2] 1;
  seg0 [2; 0; 1] 10;
  seg0 [2; 0] 7;
  seg0 [1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 2; 0; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1] 1;
  seg0 [2; 0] 7;
  seg0 [1; 2; 0; 1; 2; 0; 2; 0] 1;
  seg0 [2; 0; 1] 5;
  seg0 [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 0; 1] 1;
  seg0 [2; 0] 7;
  seg0 [1; 2; 0; 1; 2; 0; 2; 0] 1;
  seg0 [2; 0; 1] 5;
  seg0 [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1] 1;
  seg0 [2; 0] 5;
  seg0 [0; 2; 0; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0] 1;
  seg0 [2; 0; 1] 5;
  seg0 [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1] 1;
  seg0 [2; 0] 9;
  seg0 [0; 1; 2; 0; 1; 2; 0; 2; 0] 1;
  seg0 [2; 0; 1] 5;
  seg0 [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1] 1;
  seg0 [2] 6
].

Definition closeRemSeg : list SymSeg := [
  segM [2; 2; 2; 2; 2; 2; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1] 2 23;
  seg0 [2; 2; 2; 2; 2; 2; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1] 1
].

Definition pOpsChunk_0 : list TraceOp := [
  TO_steps 6 1; TO_steps 3 0; TO_steps 3 0; TO_factor 3; TO_steps 5 1;
  TO_steps 5 1; TO_steps 6 1; TO_steps 5 1; TO_steps 3 0; TO_factor 3;
  TO_steps 7 1; TO_steps 8 1; TO_steps 3 1; TO_steps 1 0; TO_steps 7 0;
  TO_factor 3; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 1 0;
  TO_steps 3 0; TO_factor 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 4 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 3;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1;
  TO_steps 1 0; TO_steps 5 0; TO_factor 3; TO_steps 3 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 1 0;
  TO_steps 3 0; TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 7 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 8 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1;
  TO_steps 3 0; TO_factor 3; TO_steps 6 1; TO_steps 3 0; TO_factor 3;
  TO_steps 5 1; TO_steps 5 1; TO_steps 6 1; TO_steps 5 1; TO_steps 5 0;
  TO_factor 5; TO_steps 9 1; TO_steps 10 1; TO_steps 7 0; TO_factor 3;
  TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 3 1; TO_steps 1 0; TO_steps 3 0; TO_factor 1;
  TO_steps 1 0; TO_steps 7 0; TO_factor 4; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 4; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 1 0; TO_steps 5 0; TO_factor 3; TO_steps 3 1;
  TO_steps 8 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 7 1;
  TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 1 0; TO_steps 3 0;
  TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 13 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 13 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 6 0;
  TO_steps 6 0; TO_factor 4; TO_steps 4 1; TO_steps 4 1; TO_steps 4 0;
  TO_steps 4 0; TO_factor 4; TO_steps 5 0;
  TO_loop false 5 0 0 12 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 38 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 5 1; TO_steps 5 0;
  TO_factor 5; TO_steps 10 0; TO_factor 5; TO_steps 5 0; TO_factor 5;
  TO_steps 10 1; TO_steps 10 0; TO_factor 6; TO_steps 6 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 4 1; TO_steps 3 1; TO_steps 9 0; TO_factor 3;
  TO_steps 12 1; TO_steps 8 1; TO_steps 5 0; TO_factor 5; TO_steps 9 1;
  TO_steps 9 0; TO_factor 8; TO_steps 8 1; TO_steps 5 0; TO_steps 12 0;
  TO_factor 5; TO_steps 11 1; TO_steps 12 1; TO_steps 11 1; TO_steps 11 1;
  TO_steps 9 1; TO_steps 5 1; TO_steps 5 1; TO_steps 5 0; TO_steps 5 0;
  TO_factor 5; TO_steps 7 1; TO_steps 15 1; TO_steps 13 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 10 0; TO_factor 8; TO_steps 8 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 13 0; TO_factor 5; TO_steps 7 1; TO_steps 3 1;
  TO_steps 14 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 1 0; TO_steps 3 0; TO_factor 3; TO_steps 1 0;
  TO_steps 3 0; TO_factor 1; TO_steps 6 1; TO_steps 4 1; TO_steps 4 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1;
  TO_steps 4 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 4;
  TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 4; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 4; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 9 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 18 0; TO_factor 11; TO_steps 4 1; TO_steps 5 1; TO_steps 3 1;
  TO_steps 1 0; TO_steps 7 0; TO_factor 5; TO_steps 3 1; TO_steps 7 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 16 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 3 1; TO_steps 1 0; TO_steps 3 0; TO_factor 3;
  TO_steps 4 1;
  TO_loop false 4 1 0 47 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 47 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 6 0;
  TO_factor 6; TO_steps 8 1; TO_steps 18 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 4 1; TO_steps 4 1;
  TO_loop true 4 0 0 46 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 76 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 11 0;
  TO_factor 9; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 3 1; TO_steps 3 1; TO_steps 5 1; TO_steps 3 1;
  TO_steps 3 0; TO_steps 11 0; TO_factor 3; TO_steps 9 1; TO_steps 20 1;
  TO_steps 5 0; TO_factor 5; TO_steps 12 0; TO_factor 10; TO_steps 5 0;
  TO_steps 10 0; TO_factor 5
].

Definition pOpsChunk_1 : list TraceOp := [
  TO_steps 9 1; TO_steps 5 0; TO_steps 14 0; TO_factor 5; TO_steps 11 1;
  TO_steps 13 1; TO_steps 11 1; TO_steps 11 1; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 5 0; TO_steps 25 0; TO_factor 17; TO_steps 8 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 12 0; TO_factor 5; TO_steps 8 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 13 0; TO_factor 5; TO_steps 7 1; TO_steps 5 1;
  TO_steps 10 1; TO_steps 5 1; TO_steps 5 1; TO_steps 5 0; TO_steps 5 0;
  TO_factor 5; TO_steps 7 1; TO_steps 5 1; TO_steps 5 0; TO_steps 12 0;
  TO_factor 10; TO_steps 5 0; TO_steps 11 0; TO_factor 10; TO_steps 5 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 5; TO_steps 5 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 5; TO_steps 5 0; TO_steps 7 0;
  TO_factor 5; TO_steps 7 1; TO_steps 5 0; TO_steps 10 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 13 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 10 1; TO_steps 5 0; TO_steps 18 0; TO_factor 9; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 20 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 9 1; TO_steps 5 1; TO_steps 12 1; TO_steps 3 1;
  TO_steps 8 1; TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 7 1;
  TO_steps 1 0; TO_steps 3 0; TO_factor 1; TO_steps 1 0; TO_steps 10 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 18 0;
  TO_factor 10; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 15 1; TO_steps 4 1; TO_steps 5 1; TO_steps 3 1;
  TO_steps 1 0; TO_steps 7 0; TO_factor 5; TO_steps 3 1; TO_steps 7 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 1 0; TO_steps 21 0;
  TO_factor 10; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 1 0;
  TO_steps 3 0; TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 119 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 119 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 6 0;
  TO_factor 6; TO_steps 9 1; TO_steps 17 0; TO_factor 13; TO_steps 21 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 0;
  TO_loop true 4 0 0 118 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 148 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 3 0; TO_steps 15 0;
  TO_factor 13; TO_steps 9 1; TO_steps 16 1; TO_steps 5 0; TO_factor 5;
  TO_steps 12 0; TO_factor 10; TO_steps 5 0; TO_steps 10 0; TO_factor 5;
  TO_steps 9 1; TO_steps 5 0; TO_steps 14 0; TO_factor 5; TO_steps 11 1;
  TO_steps 13 1; TO_steps 11 1; TO_steps 11 1; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 5; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 11; TO_steps 7 1; TO_steps 5 1; TO_steps 11 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 13 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 7 0; TO_factor 5; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0
].

Definition pOpsChunk_2 : list TraceOp := [
  TO_steps 10 0; TO_factor 5; TO_steps 5 0; TO_steps 7 0; TO_factor 5;
  TO_steps 7 1; TO_steps 5 0; TO_steps 10 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 10 1;
  TO_steps 5 0; TO_steps 21 0; TO_factor 9; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 18 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 15 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 7 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 9 1; TO_steps 11 1; TO_steps 7 1; TO_steps 16 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 20 0; TO_factor 11; TO_steps 7 1; TO_steps 11 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 8 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 12 1; TO_steps 7 1; TO_steps 8 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 11 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0;
  TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 13 1; TO_steps 18 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 25 0; TO_factor 18; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 5 1; TO_steps 3 0;
  TO_steps 17 0; TO_factor 12; TO_steps 3 1; TO_steps 19 1; TO_steps 3 1;
  TO_steps 5 1; TO_steps 3 1; TO_steps 7 1; TO_steps 1 0; TO_steps 3 0;
  TO_factor 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 14 0; TO_factor 12; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 14 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 22 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 13 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 15 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 17 0; TO_factor 11;
  TO_steps 4 1; TO_steps 16 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 17 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 16 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1
].

Definition pOpsChunk_3 : list TraceOp := [
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0;
  TO_factor 8; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 1 0; TO_steps 7 0; TO_factor 5; TO_steps 3 1;
  TO_steps 7 1; TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 14 1;
  TO_steps 3 1; TO_steps 3 1; TO_steps 3 1; TO_steps 1 0; TO_steps 3 0;
  TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 263 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 263 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 6 0;
  TO_factor 6; TO_steps 9 1; TO_steps 31 0; TO_factor 17; TO_steps 22 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 0;
  TO_loop true 4 0 0 262 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 292 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 27 0;
  TO_factor 18; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 3 1; TO_steps 3 1; TO_steps 5 1; TO_steps 3 1;
  TO_steps 3 0; TO_steps 27 0; TO_factor 19; TO_steps 9 1; TO_steps 16 1;
  TO_steps 5 0; TO_factor 5; TO_steps 12 0; TO_factor 10; TO_steps 5 0;
  TO_steps 10 0; TO_factor 5; TO_steps 9 1; TO_steps 5 0; TO_steps 14 0;
  TO_factor 5; TO_steps 11 1; TO_steps 13 1; TO_steps 11 1; TO_steps 11 1;
  TO_steps 9 1; TO_steps 5 1; TO_steps 5 1; TO_steps 5 0; TO_steps 5 0;
  TO_factor 5; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 13 0; TO_factor 5; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 0; TO_steps 13 0; TO_factor 11; TO_steps 7 1; TO_steps 5 1;
  TO_steps 11 1; TO_steps 5 1; TO_steps 5 1; TO_steps 5 0; TO_steps 5 0;
  TO_factor 5; TO_steps 7 1; TO_steps 5 1; TO_steps 5 0; TO_steps 14 0;
  TO_factor 9; TO_steps 13 1; TO_steps 5 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 5; TO_steps 5 1; TO_steps 5 1; TO_steps 5 0; TO_steps 10 0;
  TO_factor 5; TO_steps 5 0; TO_steps 7 0; TO_factor 5; TO_steps 7 1;
  TO_steps 5 0; TO_steps 10 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 10 1; TO_steps 5 0;
  TO_steps 21 0; TO_factor 9; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 18 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 15 1; TO_steps 10 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 16 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 20 0;
  TO_factor 11; TO_steps 7 1; TO_steps 11 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 12 1; TO_steps 7 1; TO_steps 8 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9;
  TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 13 1; TO_steps 18 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 24 0;
  TO_factor 18; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 19 0;
  TO_factor 14; TO_steps 21 1; TO_steps 7 1; TO_steps 9 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 5 0
].

Definition pOpsChunk_4 : list TraceOp := [
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 15 0; TO_factor 13; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9;
  TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 15 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 14 1; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1;
  TO_steps 7 1; TO_steps 23 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 14 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 18 0; TO_factor 12; TO_steps 17 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 18 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 17 1; TO_steps 7 1;
  TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1;
  TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 5 1; TO_steps 3 0; TO_steps 32 0;
  TO_factor 27; TO_steps 3 1; TO_steps 21 1; TO_steps 3 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 7 1; TO_steps 1 0; TO_steps 3 0; TO_factor 1;
  TO_steps 1 0; TO_steps 26 0; TO_factor 17; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 26 0; TO_factor 18; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 15 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1
].

Definition pOpsChunk_5 : list TraceOp := [
  TO_steps 1 0; TO_steps 36 0; TO_factor 21; TO_steps 4 1; TO_steps 25 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 25 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 25 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0;
  TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0;
  TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 15 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 28 0; TO_factor 19; TO_steps 4 1;
  TO_steps 26 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 26 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 27 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 15 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 29 0; TO_factor 19;
  TO_steps 4 1; TO_steps 1 0; TO_steps 31 0; TO_factor 29; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 31 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1
].

Definition pOpsChunk_6 : list TraceOp := [
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 27 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 5 1; TO_steps 3 1; TO_steps 1 0; TO_steps 7 0;
  TO_factor 5; TO_steps 3 1; TO_steps 7 1; TO_steps 3 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 14 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1;
  TO_steps 1 0; TO_steps 3 0; TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 551 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 2 1; TO_steps 3 1; TO_steps 2 0; TO_steps 2 0;
  TO_factor 1; TO_steps 8 1; TO_steps 8 0;
  TO_loop true 8 0 0 551 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 6 0;
  TO_factor 6; TO_steps 9 1; TO_steps 29 0; TO_factor 19; TO_steps 30 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 0;
  TO_loop true 4 0 0 550 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 580 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 31 1;
  TO_steps 7 1; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 3 0; TO_steps 28 0;
  TO_factor 3; TO_steps 9 1; TO_steps 16 1; TO_steps 5 0; TO_factor 5;
  TO_steps 12 0; TO_factor 10; TO_steps 5 0; TO_steps 10 0; TO_factor 5;
  TO_steps 9 1; TO_steps 5 0; TO_steps 14 0; TO_factor 5; TO_steps 11 1;
  TO_steps 13 1; TO_steps 11 1; TO_steps 11 1; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 5; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 11; TO_steps 7 1; TO_steps 5 1; TO_steps 11 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 13 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 7 0; TO_factor 5; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 10 0; TO_factor 5; TO_steps 5 0;
  TO_steps 7 0; TO_factor 5; TO_steps 7 1; TO_steps 5 0; TO_steps 10 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 10 1; TO_steps 5 0; TO_steps 21 0; TO_factor 9;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 18 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 11 0;
  TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 5 0; TO_steps 20 0; TO_factor 11; TO_steps 7 1;
  TO_steps 11 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 12 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 11 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 9 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 9 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1
].

Definition pOpsChunk_7 : list TraceOp := [
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 18 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 24 0; TO_factor 18; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 19 0; TO_factor 14; TO_steps 21 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 13 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 15 0; TO_factor 13; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9;
  TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 15 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 14 1; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1;
  TO_steps 7 1; TO_steps 23 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 14 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 18 0; TO_factor 12; TO_steps 17 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 18 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 17 1; TO_steps 7 1;
  TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1;
  TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 34 0;
  TO_factor 29; TO_steps 23 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 27 0; TO_factor 18; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 27 0; TO_factor 19; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9;
  TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 8 1; TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9;
  TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 13 1; TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 37 0; TO_factor 22; TO_steps 26 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 26 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1;
  TO_steps 26 1; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1;
  TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0
].

Definition pOpsChunk_8 : list TraceOp := [
  TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1;
  TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 29 0; TO_factor 20; TO_steps 27 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 27 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 28 1;
  TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0;
  TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1;
  TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 30 0; TO_factor 20; TO_steps 5 0; TO_steps 32 0; TO_factor 30;
  TO_steps 7 1; TO_steps 9 1; TO_steps 32 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1;
  TO_steps 28 1; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1;
  TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1;
  TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 5 1;
  TO_steps 3 0; TO_steps 28 0; TO_factor 18; TO_steps 3 1; TO_steps 29 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 7 1; TO_steps 1 0;
  TO_steps 3 0; TO_factor 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 27 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1
].

Definition pOpsChunk_9 : list TraceOp := [
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0;
  TO_factor 8; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 15 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 29 0;
  TO_factor 19; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 27 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 15 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 29 0; TO_factor 19; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 30 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 27 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1
].

Definition pOpsChunk_10 : list TraceOp := [
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 15 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 29 0; TO_factor 19; TO_steps 4 1; TO_steps 30 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 30 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 27 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0;
  TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0;
  TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 15 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 29 0; TO_factor 19; TO_steps 4 1;
  TO_steps 30 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 27 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1
].

Definition pOpsChunk_11 : list TraceOp := [
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 15 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 29 0; TO_factor 19;
  TO_steps 4 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 27 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 10 0;
  TO_factor 8; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 15 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 29 0;
  TO_factor 19; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 27 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6;
  TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 15 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1
].

Definition pOpsChunk_12 : list TraceOp := [
  TO_steps 4 1; TO_steps 1 0; TO_steps 6 0; TO_factor 6; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 29 0; TO_factor 19; TO_steps 4 1; TO_steps 30 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 30 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 27 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 8 0; TO_factor 6; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 11 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0;
  TO_factor 8; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 9 1;
  TO_steps 4 1; TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 13 0; TO_factor 8;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1; TO_steps 4 1;
  TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 14 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0; TO_factor 13;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 6 0;
  TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1; TO_steps 12 1;
  TO_steps 4 1; TO_steps 5 1; TO_steps 3 1; TO_steps 1 0; TO_steps 7 0;
  TO_factor 5; TO_steps 3 1; TO_steps 7 1; TO_steps 3 1; TO_steps 5 1;
  TO_steps 3 1; TO_steps 14 1; TO_steps 3 1; TO_steps 3 1; TO_steps 3 1;
  TO_steps 1 0; TO_steps 3 0; TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 0 1127 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 1 0
].

Definition pOpsChunk_all : list TraceOp :=
  pOpsChunk_0 ++ pOpsChunk_1 ++ pOpsChunk_2 ++ pOpsChunk_3 ++ pOpsChunk_4 ++ pOpsChunk_5 ++ pOpsChunk_6 ++ pOpsChunk_7 ++ pOpsChunk_8 ++ pOpsChunk_9 ++ pOpsChunk_10 ++ pOpsChunk_11 ++ pOpsChunk_12.


Definition wOpsChunk_0 : list TraceOp := [
  TO_steps 3 1; TO_steps 2 0; TO_steps 2 0; TO_factor 1; TO_steps 8 1;
  TO_steps 8 0;
  TO_loop true 8 0 72 1127 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 0 8 1;
      LS_grow [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1] 0 1;
      LS_drain [0; 1; 0; 0; 0; 2; 2] 0 6 1
    ];
  TO_steps 5 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 6 0;
  TO_factor 6; TO_steps 9 1; TO_steps 29 0; TO_factor 11; TO_steps 30 1;
  TO_steps 8 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 0;
  TO_loop true 4 0 72 1126 [
      LS_const [1] 0 1;
      LS_grow [0; 0; 2] 72 1156 1;
      LS_drain [0; 0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [2; 0; 1] 0 6 1
    ];
  TO_steps 5 1; TO_steps 4 1; TO_steps 4 1; TO_steps 4 1; TO_steps 30 1;
  TO_steps 7 1; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 3 0; TO_steps 28 0;
  TO_factor 3; TO_steps 9 1; TO_steps 16 1; TO_steps 5 0; TO_factor 5;
  TO_steps 12 0; TO_factor 10; TO_steps 5 0; TO_steps 10 0; TO_factor 5;
  TO_steps 9 1; TO_steps 5 0; TO_steps 14 0; TO_factor 5; TO_steps 11 1;
  TO_steps 13 1; TO_steps 11 1; TO_steps 11 1; TO_steps 9 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 5; TO_steps 9 1; TO_steps 5 1; TO_steps 5 0; TO_steps 13 0;
  TO_factor 11; TO_steps 7 1; TO_steps 5 1; TO_steps 11 1; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 5 0; TO_factor 5; TO_steps 7 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 13 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 7 0; TO_factor 5; TO_steps 5 1;
  TO_steps 5 1; TO_steps 5 0; TO_steps 10 0; TO_factor 5; TO_steps 5 0;
  TO_steps 7 0; TO_factor 5; TO_steps 7 1; TO_steps 5 0; TO_steps 10 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 10 1; TO_steps 5 0; TO_steps 21 0; TO_factor 9;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 18 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 11 0;
  TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 5 0; TO_steps 20 0; TO_factor 11; TO_steps 7 1;
  TO_steps 11 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 12 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 11 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 9 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 9 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 18 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 24 0; TO_factor 18; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 19 0; TO_factor 14; TO_steps 21 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 13 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 15 0; TO_factor 13; TO_steps 7 1; TO_steps 14 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1;
  TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 15 0; TO_factor 9; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 14 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 14 1; TO_steps 7 1; TO_steps 23 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 14 0; TO_factor 14; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 18 0; TO_factor 12; TO_steps 17 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 18 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 17 1;
  TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 13 1
].

Definition wOpsChunk_1 : list TraceOp := [
  TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 8 1; TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9;
  TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 13 1; TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 34 0; TO_factor 29; TO_steps 23 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 27 0; TO_factor 18;
  TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 27 0; TO_factor 19;
  TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0;
  TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1;
  TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 37 0; TO_factor 22; TO_steps 26 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 26 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 26 1; TO_steps 7 1;
  TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1;
  TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 29 0;
  TO_factor 20; TO_steps 27 1; TO_steps 7 1; TO_steps 9 1; TO_steps 27 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 9 1; TO_steps 28 1; TO_steps 7 1; TO_steps 14 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1;
  TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14;
  TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0;
  TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 16 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 30 0; TO_factor 20
].

Definition wOpsChunk_2 : list TraceOp := [
  TO_steps 5 0; TO_steps 32 0; TO_factor 30; TO_steps 7 1; TO_steps 9 1;
  TO_steps 32 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 28 1; TO_steps 7 1;
  TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1;
  TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 30 0;
  TO_factor 20; TO_steps 31 1; TO_steps 7 1; TO_steps 9 1; TO_steps 31 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 9 1; TO_steps 28 1; TO_steps 7 1; TO_steps 14 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1;
  TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14;
  TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1; TO_steps 15 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0;
  TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 16 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 30 0; TO_factor 20;
  TO_steps 31 1; TO_steps 7 1; TO_steps 9 1; TO_steps 31 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 9 1; TO_steps 28 1; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9;
  TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 8 1; TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9;
  TO_steps 8 1; TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 13 1; TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 30 0; TO_factor 20; TO_steps 31 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 31 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1;
  TO_steps 28 1; TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1;
  TO_steps 10 1; TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 14 0; TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1;
  TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1
].

Definition wOpsChunk_3 : list TraceOp := [
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 30 0; TO_factor 20; TO_steps 31 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 31 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 28 1;
  TO_steps 7 1; TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 7 1; TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1;
  TO_steps 8 1; TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0;
  TO_factor 9; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1;
  TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1;
  TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1;
  TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 30 0; TO_factor 20; TO_steps 31 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 31 1; TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 7; TO_steps 7 1; TO_steps 9 1; TO_steps 28 1; TO_steps 7 1;
  TO_steps 14 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1;
  TO_steps 11 1; TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0;
  TO_steps 9 0; TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9;
  TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0; TO_steps 16 0;
  TO_factor 14; TO_steps 7 1; TO_steps 8 1; TO_steps 14 1; TO_steps 7 1;
  TO_steps 15 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1; TO_steps 5 0;
  TO_steps 16 0; TO_factor 14; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 11 0; TO_factor 9; TO_steps 8 1; TO_steps 7 1; TO_steps 11 1;
  TO_steps 7 1; TO_steps 7 1; TO_steps 8 1; TO_steps 7 1; TO_steps 5 0;
  TO_steps 7 0; TO_factor 7; TO_steps 13 1; TO_steps 13 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 9 1; TO_steps 7 1;
  TO_steps 16 1; TO_steps 9 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0;
  TO_factor 7; TO_steps 10 1; TO_steps 7 1; TO_steps 5 0; TO_steps 30 0;
  TO_factor 20; TO_steps 31 1; TO_steps 7 1; TO_steps 9 1; TO_steps 31 1;
  TO_loop true 51 143 1 2 [
      LS_const [1] 0 1;
      LS_drain [0; 0; 2] 0 135 144;
      LS_const [0; 0; 1] 0 1;
      LS_grow [2; 0; 0; 0; 2; 0] 0 934 72;
      LS_const [1; 2; 2; 0; 1; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 1] 0 1;
      LS_grow [2; 0; 2; 0; 0; 0; 2; 0] 0 153 12;
      LS_const [2; 0; 1; 2; 2; 0; 2; 0; 2; 0; 0; 2; 0; 2; 0; 2; 0; 0; 2; 0; 1; 2; 0; 0; 0; 2; 2; 2; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2] 0 1;
      LS_const [0] 0 11;
      LS_const [2; 0; 1] 0 8;
      LS_const [2; 0] 0 7;
      LS_const [1; 2; 0; 1; 2; 0; 2; 0; 2] 0 1;
      LS_const [0] 0 17;
      LS_const [1; 2; 0; 2; 0; 2] 0 1;
      LS_const [0] 0 11;
      LS_const [1; 2; 0; 1] 0 1;
      LS_const [2; 0] 0 7;
      LS_const [1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 2; 0] 0 1;
      LS_const [0; 2] 0 5;
      LS_const [0; 1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1] 0 1;
      LS_const [2; 0] 0 8;
      LS_const [0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1] 0 1;
      LS_const [2] 0 15;
      LS_grow [0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 2; 2; 2; 2; 2; 2] 0 6 1
    ];
  TO_steps 7 1; TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7;
  TO_steps 7 1; TO_steps 9 1; TO_steps 30 1; TO_steps 7 1; TO_steps 14 1;
  TO_steps 5 0; TO_steps 9 0; TO_factor 7; TO_steps 7 1; TO_steps 11 1;
  TO_steps 12 1; TO_steps 7 1; TO_steps 11 1; TO_steps 5 0; TO_steps 9 0;
  TO_factor 9; TO_steps 7 1; TO_steps 10 1; TO_steps 8 1; TO_steps 7 1;
  TO_steps 13 1; TO_steps 10 1; TO_steps 7 1; TO_steps 7 1; TO_steps 9 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 14 0; TO_factor 9; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 16 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 14 1; TO_steps 7 1; TO_steps 15 1; TO_steps 7 1; TO_steps 7 1;
  TO_steps 9 1; TO_steps 5 0; TO_steps 16 0; TO_factor 14; TO_steps 7 1;
  TO_steps 7 1; TO_steps 9 1; TO_steps 7 1; TO_steps 11 1; TO_steps 10 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 11 0; TO_factor 9; TO_steps 8 1;
  TO_steps 7 1; TO_steps 11 1; TO_steps 7 1; TO_steps 7 1; TO_steps 8 1;
  TO_steps 7 1; TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 13 1;
  TO_steps 13 1; TO_steps 7 1; TO_steps 5 0; TO_steps 9 0; TO_factor 7;
  TO_steps 9 1; TO_steps 7 1; TO_steps 16 1; TO_steps 9 1; TO_steps 7 1;
  TO_steps 5 0; TO_steps 7 0; TO_factor 7; TO_steps 10 1; TO_steps 5 1;
  TO_steps 3 0; TO_steps 28 0; TO_factor 18; TO_steps 3 1; TO_steps 29 1;
  TO_steps 3 1; TO_steps 5 1; TO_steps 3 1; TO_steps 7 1;
  TO_loop true 30 287 1 15 [
      LS_const [1; 2] 0 1;
      LS_grow [0; 0; 0; 2; 0] 0 6 144;
      LS_drain [0; 0; 0; 2; 0; 2] 0 62 72;
      LS_const [0; 0; 0; 2; 0; 1; 2; 2; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2; 0; 0; 2; 0; 1] 0 1;
      LS_grow [2; 0; 0; 0; 2; 0; 2; 0] 12 189 12;
      LS_const [2; 0; 0; 0; 1; 2; 0; 2; 0; 0; 2; 0; 2; 0; 2; 0; 0; 2; 0; 2; 0; 0; 2] 0 1;
      LS_const [0] 0 8;
      LS_const [1; 2; 0] 0 5;
      LS_const [2; 0; 1; 2; 0; 2; 0; 2; 0] 0 1;
      LS_const [0; 1; 2] 0 9;
      LS_const [0; 2] 0 6;
      LS_const [0; 1; 2; 0; 1; 2; 0; 2] 0 1;
      LS_const [0] 0 17;
      LS_const [2; 0; 1; 2; 0; 2] 0 1;
      LS_const [0] 0 11;
      LS_const [2; 0; 1; 2; 0; 1] 0 1;
      LS_const [2; 0] 0 7;
      LS_const [1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0] 0 1;
      LS_const [0; 2] 0 6;
      LS_const [0; 1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1] 0 1;
      LS_const [2; 0] 0 7;
      LS_const [0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2] 0 1;
      LS_const [0] 0 29;
      LS_const [1; 2; 0; 2; 0] 0 1;
      LS_const [2; 0; 1] 0 5;
      LS_const [2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 2] 0 1;
      LS_grow [2; 2; 2; 2; 2; 2; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 2; 0; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1; 2; 0; 1] 1 8 1;
      LS_const [2] 0 7
    ];
  TO_steps 4 1; TO_steps 33 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 29 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 13 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 6; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 10 1; TO_steps 4 1; TO_steps 11 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1
].

Definition wOpsChunk_4 : list TraceOp := [
  TO_steps 4 1; TO_steps 1 0; TO_steps 8 0; TO_factor 8; TO_steps 4 1;
  TO_steps 6 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 9 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 1 0; TO_steps 13 0; TO_factor 8; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 8 1; TO_steps 4 1;
  TO_steps 15 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 7 1;
  TO_steps 4 1; TO_steps 13 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 14 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 1 0; TO_steps 15 0;
  TO_factor 13; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 8 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 10 1; TO_steps 4 1; TO_steps 9 1; TO_steps 4 1; TO_steps 6 1;
  TO_steps 4 1; TO_steps 1 0; TO_steps 10 0; TO_factor 8; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 10 1;
  TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1;
  TO_steps 7 1; TO_steps 4 1; TO_steps 6 1; TO_steps 4 1; TO_steps 1 0;
  TO_steps 6 0; TO_factor 6; TO_steps 4 1; TO_steps 12 1; TO_steps 4 1;
  TO_steps 12 1; TO_steps 4 1; TO_steps 5 1; TO_steps 3 1; TO_steps 1 0;
  TO_steps 7 0; TO_factor 5; TO_steps 3 1; TO_steps 7 1; TO_steps 3 1;
  TO_steps 5 1; TO_steps 3 1; TO_steps 14 1; TO_steps 3 1; TO_steps 3 1;
  TO_steps 3 1; TO_steps 1 0; TO_steps 3 0; TO_factor 3; TO_steps 4 1;
  TO_loop false 4 1 144 2279 [
      LS_const [1; 2] 0 1;
      LS_drain [0; 0; 0; 2; 0] 0 6 1;
      LS_const [0; 0; 0; 1; 2; 2] 0 1;
      LS_grow [0; 0; 0; 2; 2; 0; 1] 0 6 1
    ];
  TO_steps 4 1; TO_steps 4 1; TO_steps 2 1; TO_steps 2 1; TO_steps 2 1;
  TO_steps 2 1; TO_steps 1 0
].

Definition wOpsChunk_all : list TraceOp :=
  wOpsChunk_0 ++ wOpsChunk_1 ++ wOpsChunk_2 ++ wOpsChunk_3 ++ wOpsChunk_4.


End TraceData.

Lemma prefix_ok : checkPrefixGen fuel124 waveTemplate pChk_0 pOpsChunk_all = true.
Proof. vm_compute; reflexivity. Qed.

Lemma wave_ok : checkWaveGen waveTemplate closeRemSeg wOpsChunk_all = true.
Proof. vm_compute; reflexivity. Qed.

#[local] Opaque pChk_0 waveTemplate closeRemSeg
  pOpsChunk_0 pOpsChunk_1 pOpsChunk_2 pOpsChunk_3 pOpsChunk_4
  pOpsChunk_5 pOpsChunk_6 pOpsChunk_7 pOpsChunk_8 pOpsChunk_9
  pOpsChunk_10 pOpsChunk_11 pOpsChunk_12 pOpsChunk_all
  wOpsChunk_0 wOpsChunk_1 wOpsChunk_2 wOpsChunk_3 wOpsChunk_4 wOpsChunk_all.

Definition WaveInv (c : Q * tape) : Prop :=
  exists (vM : N) (tail : list nat),
    c = cfgSweep (evalSym waveTemplate vM 0 0 ++ tail).

Lemma wave_inv_step : forall c, WaveInv c -> exists c', WaveInv c' /\ c -[ tm ]->+ c'.
Proof.
  intros c [vM [tail ->]].
  destruct (checkWaveGen_sound waveTemplate closeRemSeg wOpsChunk_all wave_ok vM tail)
    as [tail' Hstep].
  exists (cfgSweep (evalSym waveTemplate (2 * vM + 16) 0 0 ++ tail')).
  split.
  - exists (2 * vM + 16), tail'. reflexivity.
  - exact Hstep.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct (checkPrefixGen_sound fuel124 waveTemplate pChk_0 pOpsChunk_all prefix_ok)
    as [tail0 Hinit].
  eapply multistep_nonhalt.
  - exact (progress_evstep tm _ _ Hinit).
  - eapply progress_nonhalt with (P := WaveInv).
    + exact wave_inv_step.
    + exists 0, tail0. reflexivity.
Qed.
