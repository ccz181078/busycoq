(* PR #88: compute the layered return rules on demand instead of replaying
   an externally generated DAG. The initialization and left-wall invariant
   are those of the original proof. *)

From BusyCoq Require Import Individual62.
Require Import String List PeanoNat NArith PArith ZifyNat Lia.
Import ListNotations.
Open Scope list_scope.
Open Scope sym_scope.

From BusyCoq Require HashTable.
From Coq Require Uint63.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF").

Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

(* ========================================================================== *)
(* Section 1: Basic Reachability, Tape Encodings, and Raw TM Steps            *)
(* ========================================================================== *)

Lemma halted_halts c : halted tm c -> halts tm c.
Proof.
  intros H. exists 0%nat, c. split; [constructor | exact H].
Qed.

Lemma ev_trans c1 c2 c3 : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof.
  induction 1; eauto.
Qed.

Lemma evstep_halts c c' : c -->* c' -> halts tm c' -> halts tm c.
Proof.
  induction 1 as [c | c c1 c2 H1 _ IH]; [auto |].
  intros H2. apply IH in H2. destruct H2 as [n [ch [Hm Hh]]].
  exists (S n), ch. split; [econstructor; eauto | exact Hh].
Qed.

Definition qEqb (x y : Q) : bool :=
  match x, y with
  | A, A | B, B | C, C | D, D | E, E | F, F => true
  | _, _ => false
  end.

Lemma qEqb_eq x y : qEqb x y = true -> x = y.
Proof.
  destruct x, y; simpl; congruence.
Qed.

Fixpoint boolListEqb (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Bool.eqb x y && boolListEqb xs' ys'
  | _, _ => false
  end.

Lemma boolListEqb_eq xs ys : boolListEqb xs ys = true -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; try discriminate.
  - reflexivity.
  - intros H. apply andb_prop in H as [H1 H2].
    apply Bool.eqb_prop in H1. subst y. f_equal. exact (IH ys H2).
Qed.

Definition bitToSym (b : bool) : Sym := if b then 1 else 0.

Fixpoint bitsToSide (xs : list bool) (s : side) : side :=
  match xs with
  | [] => s
  | b :: bs => bitToSym b >> bitsToSide bs s
  end.

Lemma bitsToSide_app xs ys s :
  bitsToSide (xs ++ ys) s = bitsToSide xs (bitsToSide ys s).
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma bitsToSide_eq_str xs s :
  bitsToSide xs s = map bitToSym xs *> s.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Definition consTrim (b : bool) (xs : list bool) : list bool :=
  match b, xs with
  | false, [] => []
  | _, _ => b :: xs
  end.
Arguments consTrim : simpl never.

Lemma bitsToSide_consTrim b xs :
  bitsToSide (consTrim b xs) 0inf = bitToSym b >> bitsToSide xs 0inf.
Proof.
  unfold consTrim. destruct b, xs; simpl; try reflexivity.
  exact (const_unfold _ 0).
Qed.

Definition popBit (rb : list bool) : bool * list bool :=
  match rb with
  | [] => (false, [])
  | c :: r => (c, r)
  end.

Lemma popBit_spec rb :
  bitsToSide rb 0inf = bitToSym (fst (popBit rb)) >> bitsToSide (snd (popBit rb)) 0inf.
Proof.
  destruct rb as [|c r]; simpl; [exact (const_unfold _ 0) | reflexivity].
Qed.

Lemma headLeft_cons a (sL sR : side) (q : Q) :
  (a >> sL) <{{q}} sR = sL {{q}}> (a >> sR).
Proof. reflexivity. Qed.

Definition tmStepRaw (q : Q) (sym : bool) : option (Q * bool * bool) :=
  match q, sym with
  | A, false => Some (B, true, true)
  | A, true  => Some (D, false, true)
  | B, false => Some (C, true, true)
  | B, true  => Some (F, false, false)
  | C, false => Some (A, false, false)
  | C, true  => Some (B, false, true)
  | D, false => Some (E, true, true)
  | D, true  => None
  | E, false => Some (B, true, false)
  | E, true  => Some (A, true, true)
  | F, false => Some (E, false, false)
  | F, true  => Some (F, false, false)
  end.

Lemma step_raw_right q nq sym w (sL sR : side) :
  tmStepRaw q sym = Some (nq, w, true) ->
  sL {{q}}> (bitToSym sym >> sR) -->* (bitToSym w >> sL) {{nq}}> sR.
Proof.
  intros H. apply evstep_one.
  destruct q, sym; simpl in H; try discriminate;
    inversion H; subst; apply @step_right; vm_compute; reflexivity.
Qed.

Lemma step_raw_left q nq sym w (sL sR : side) :
  tmStepRaw q sym = Some (nq, w, false) ->
  sL {{q}}> (bitToSym sym >> sR) -->* sL <{{nq}} (bitToSym w >> sR).
Proof.
  intros H. apply evstep_one.
  destruct q, sym; simpl in H; try discriminate;
    inversion H; subst; apply @step_left; vm_compute; reflexivity.
Qed.

Lemma step_raw_none q sym (sL sR : side) :
  tmStepRaw q sym = None ->
  halts tm (sL {{q}}> (bitToSym sym >> sR)).
Proof.
  intros H. apply halted_halts.
  destruct q, sym; simpl in H; try discriminate; vm_compute; reflexivity.
Qed.

(* ========================================================================== *)
(* Section 2: Link 1 Soundness (t = 0 -> 6,818)                               *)
(* ========================================================================== *)

Definition simRawZip1 (q : Q) (lb rb : list bool) : option (Q * list bool * list bool) :=
  let '(sym, rb') := popBit rb in
  match tmStepRaw q sym with
  | None => None
  | Some (nq, w, true) => Some (nq, consTrim w lb, rb')
  | Some (nq, w, false) =>
    let rbW := consTrim w rb' in
    match lb with
    | [] => Some (nq, [], consTrim false rbW)
    | nl :: lb' => Some (nq, lb', nl :: rbW)
    end
  end.

Fixpoint simRawZip (n : nat) (st : option (Q * list bool * list bool))
    : option (Q * list bool * list bool) :=
  match n with
  | O => st
  | S n' =>
    match st with
    | None => None
    | Some (q, lb, rb) => simRawZip n' (simRawZip1 q lb rb)
    end
  end.

Fixpoint simRawZipChunks (chunks chunkSize : nat) (st : option (Q * list bool * list bool))
    : option (Q * list bool * list bool) :=
  match chunks with
  | O => st
  | S chunks' => simRawZipChunks chunks' chunkSize (simRawZip chunkSize st)
  end.

Lemma simRawZip_none n : simRawZip n None = None.
Proof. destruct n; reflexivity. Qed.

Lemma simRawZipChunks_none chunks chunkSize :
  simRawZipChunks chunks chunkSize None = None.
Proof.
  induction chunks as [|c IH]; simpl; [reflexivity |].
  rewrite simRawZip_none. exact IH.
Qed.

Lemma simRawZip1_sound q q' lb rb lb' rb' :
  simRawZip1 q lb rb = Some (q', lb', rb') ->
  bitsToSide lb 0inf {{q}}> bitsToSide rb 0inf -->*
  bitsToSide lb' 0inf {{q'}}> bitsToSide rb' 0inf.
Proof.
  intros H. unfold simRawZip1 in H.
  rewrite (popBit_spec rb).
  destruct (popBit rb) as [sym rbT]; simpl fst; simpl snd.
  destruct (tmStepRaw q sym) as [[[nq w] [|]] |] eqn:Hst; [| | discriminate].
  - inversion H; subst. rewrite bitsToSide_consTrim.
    exact (step_raw_right _ _ _ _ _ _ Hst).
  - pose proof (step_raw_left _ _ _ _ (bitsToSide lb 0inf) (bitsToSide rbT 0inf) Hst) as Hs.
    destruct lb as [|nl lbT]; inversion H; subst.
    + rewrite !bitsToSide_consTrim.
      simpl bitsToSide in Hs |- *.
      rewrite (const_unfold _ 0) in Hs at 2.
      exact Hs.
    + simpl bitsToSide in Hs |- *.
      rewrite bitsToSide_consTrim.
      exact Hs.
Qed.

Lemma simRawZip_sound n q q' lb rb lb' rb' :
  simRawZip n (Some (q, lb, rb)) = Some (q', lb', rb') ->
  bitsToSide lb 0inf {{q}}> bitsToSide rb 0inf -->*
  bitsToSide lb' 0inf {{q'}}> bitsToSide rb' 0inf.
Proof.
  revert q lb rb. induction n as [|n IH]; intros q lb rb H; simpl in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (simRawZip1 q lb rb) as [[[q1 lb1] rb1] |] eqn:H1.
    + exact (ev_trans _ _ _ (simRawZip1_sound _ _ _ _ _ _ H1) (IH _ _ _ H)).
    + rewrite simRawZip_none in H. discriminate.
Qed.

Lemma simRawZipChunks_sound chunks chunkSize q q' lb rb lb' rb' :
  simRawZipChunks chunks chunkSize (Some (q, lb, rb)) = Some (q', lb', rb') ->
  bitsToSide lb 0inf {{q}}> bitsToSide rb 0inf -->*
  bitsToSide lb' 0inf {{q'}}> bitsToSide rb' 0inf.
Proof.
  revert q lb rb. induction chunks as [|c IH]; intros q lb rb H; simpl in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (simRawZip chunkSize (Some (q, lb, rb))) as [[[q1 lb1] rb1] |] eqn:H1.
    + exact (ev_trans _ _ _ (simRawZip_sound _ _ _ _ _ _ _ H1) (IH _ _ _ H)).
    + rewrite simRawZipChunks_none in H. discriminate.
Qed.

Definition right6818 : list bool := [false; false; true; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; true; false; false; true].
Definition tail35 : list bool := [false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; true; false; false; false; false; true; false; false; true; true; false; false; true].
Definition crys0_13 : list bool := [true; true; true; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true; true; true; true; true; false; false; true].

Definition checkLink1 : bool :=
  match simRawZip 18%nat (simRawZipChunks 68%nat 100%nat (Some (A, [], []))) with
  | Some (q, lb, rb) => qEqb q A && boolListEqb lb crys0_13 && boolListEqb rb right6818
  | None => false
  end.

Lemma link1_valid : checkLink1 = true.
Proof. vm_check_eq. Qed.

Lemma link1_reaches :
  c0 -->* (bitsToSide crys0_13 0inf {{A}}> bitsToSide right6818 0inf).
Proof.
  pose proof link1_valid as Hv. unfold checkLink1 in Hv.
  destruct (simRawZipChunks 68%nat 100%nat (Some (A, [], []))) as [[[q1 lb1] rb1] |] eqn:H1;
    [| rewrite simRawZip_none in Hv; discriminate].
  destruct (simRawZip 18%nat (Some (q1, lb1, rb1))) as [[[q2 lb2] rb2] |] eqn:H2;
    [| discriminate].
  apply andb_prop in Hv as [Hv1 Hrb].
  apply andb_prop in Hv1 as [Hq Hlb].
  apply qEqb_eq in Hq. apply boolListEqb_eq in Hlb. apply boolListEqb_eq in Hrb.
  subst q2 lb2 rb2.
  exact (ev_trans _ _ _
    (simRawZipChunks_sound 68%nat 100%nat _ _ _ _ _ _ H1)
    (simRawZip_sound 18%nat _ _ _ _ _ _ H2)).
Qed.

(* ========================================================================== *)
(* Section 3: Link 2 Soundness (Parametric 8-Phase Crystal Wall)              *)
(* ========================================================================== *)

Inductive Phase : Type := P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7.

Definition nextPhase (ph : Phase) : Phase :=
  match ph with
  | P0 => P1 | P1 => P2 | P2 => P3 | P3 => P4
  | P4 => P5 | P5 => P6 | P6 => P7 | P7 => P0
  end.

Definition phaseEqb (x y : Phase) : bool :=
  match x, y with
  | P0, P0 | P1, P1 | P2, P2 | P3, P3
  | P4, P4 | P5, P5 | P6, P6 | P7, P7 => true
  | _, _ => false
  end.

Lemma phaseEqb_eq x y : phaseEqb x y = true -> x = y.
Proof.
  destruct x, y; simpl; congruence.
Qed.

Definition wallStepSpec (ph : Phase) : Q * Q :=
  match ph with
  | P0 => (F, E)
  | P1 => (B, E)
  | P2 => (F, E)
  | P3 => (B, E)
  | P4 => (F, E)
  | P5 => (B, B)
  | P6 => (F, B)
  | P7 => (E, A)
  end.

Definition tm_fast : TM := Eval compute in tm.

Lemma tm_fast_eq q s : tm (q, s) = tm_fast (q, s).
Proof.
  destruct q, s; vm_compute; reflexivity.
Qed.

Lemma ev_fast c1 c2 : c1 -[ tm_fast ]->* c2 -> c1 -->* c2.
Proof.
  induction 1 as [c | c c' c'' H1 _ IH]; [apply evstep_refl |].
  eapply evstep_step; [| exact IH].
  inversion H1; subst.
  - apply @step_left. rewrite tm_fast_eq. assumption.
  - apply @step_right. rewrite tm_fast_eq. assumption.
Qed.

Definition blk7 : list Sym := [0; 0; 1; 1; 1; 1; 1].
Definition blk7a : list Sym := [1; 1; 1; 0; 0; 1; 1].
Definition tail0 : list Sym := [0; 0; 1].
Definition tail1 : list Sym := [1; 1; 1; 0; 0; 1].

Definition crysHead (ph : Phase) : list Sym :=
  match ph with
  | P0 => [1; 1; 1; 1; 1; 1; 1; 1]
  | P1 => [1; 0; 0; 1; 1; 1; 1]
  | P2 => [1; 0; 0; 1; 0; 1; 1; 1; 1; 1]
  | P3 => [1; 0; 0; 1; 1; 1; 1; 1; 1; 1]
  | P4 => [1; 0; 0; 1; 0; 1; 1; 1; 1]
  | P5 => [1; 0; 0; 1; 1; 1; 1; 1; 1]
  | P6 => [0; 1; 1; 1; 1; 1; 1; 1]
  | P7 => [1; 1; 1; 1; 1; 1; 1; 1]
  end.

Definition crysTape (ph : Phase) (c : nat) : side :=
  crysHead ph *> blk7 ^^ c *> tail0 *> 0inf.

Lemma sweep1L_1 (sL sR : side) :
  blk7 *> sL <{{F}} sR -->* sL <{{F}} [0; 0; 0; 0; 0; 1; 0] *> sR.
Proof. apply ev_fast. unfold blk7. execute. Qed.

Lemma sweep1L (c : nat) (sL sR : side) :
  blk7 ^^ c *> sL <{{F}} sR -->* sL <{{F}} [0; 0; 0; 0; 0; 1; 0] ^^ c *> sR.
Proof.
  revert sR. induction c as [|c IH]; intros sR; [finish |].
  change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c).
  rewrite Str_app_assoc.
  eapply ev_trans; [apply sweep1L_1 |].
  eapply ev_trans; [apply IH |].
  rewrite lpow_shift'.
  change ([0; 0; 0; 0; 0; 1; 0] ^^ S c) with ([0; 0; 0; 0; 0; 1; 0] ++ [0; 0; 0; 0; 0; 1; 0] ^^ c).
  rewrite Str_app_assoc. finish.
Qed.

Lemma sweep1_tail (sR : side) :
  tail0 *> 0inf <{{F}} sR -->* tail1 *> 0inf {{B}}> sR.
Proof. apply ev_fast. unfold tail0, tail1. execute. Qed.

Lemma sweep1R_1 (sL sR : side) :
  (1 >> sL) {{B}}> ([0; 0; 0; 0; 0; 1; 0] *> sR) -->* (blk7a *> (1 >> sL)) {{B}}> sR.
Proof. apply ev_fast. unfold blk7a. execute. Qed.

Lemma sweep1R (c : nat) (sL sR : side) :
  (1 >> sL) {{B}}> ([0; 0; 0; 0; 0; 1; 0] ^^ c *> sR) -->* (blk7a ^^ c *> (1 >> sL)) {{B}}> sR.
Proof.
  revert sL. induction c as [|c IH]; intros sL; [finish |].
  change ([0; 0; 0; 0; 0; 1; 0] ^^ S c) with ([0; 0; 0; 0; 0; 1; 0] ++ [0; 0; 0; 0; 0; 1; 0] ^^ c).
  rewrite Str_app_assoc.
  eapply ev_trans; [apply sweep1R_1 |].
  eapply ev_trans; [apply (IH ([1; 1; 0; 0; 1; 1] *> (1 >> sL))) |].
  change (1 >> [1; 1; 0; 0; 1; 1] *> (1 >> sL)) with (blk7a *> (1 >> sL)).
  rewrite lpow_shift'.
  change (blk7a ^^ S c) with (blk7a ++ blk7a ^^ c).
  rewrite Str_app_assoc. finish.
Qed.

Lemma shift_blk7a (c : nat) :
  blk7a ^^ c *> tail1 *> 0inf = [1; 1; 1] *> blk7 ^^ c *> tail0 *> 0inf.
Proof.
  induction c as [|c IH]; [reflexivity |].
  change (blk7a ^^ S c) with (blk7a ++ blk7a ^^ c).
  change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c).
  rewrite !Str_app_assoc, IH. reflexivity.
Qed.

Lemma sweep_blk7 (c : nat) (sR : side) :
  blk7 ^^ c *> tail0 *> 0inf <{{F}} sR -->* ([1; 1; 1] *> blk7 ^^ c *> tail0 *> 0inf) {{B}}> sR.
Proof.
  eapply ev_trans; [apply sweep1L |].
  eapply ev_trans; [apply sweep1_tail |].
  change (tail1 *> 0inf) with (1 >> ([1; 1; 0; 0; 1] *> 0inf)).
  eapply ev_trans; [apply sweep1R |].
  change (1 >> [1; 1; 0; 0; 1] *> 0inf) with (tail1 *> 0inf).
  rewrite shift_blk7a. finish.
Qed.

Lemma crys_ph0_a (sX sR : side) :
  [1; 1; 1; 1; 1; 1; 1; 1] *> sX <{{F}} sR -->* sX <{{F}} [0; 0; 0; 0; 0; 0; 0; 0] *> sR.
Proof. apply ev_fast. execute. Qed.

Lemma crys_ph0_b (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 0; 0; 0] *> sR) -->*
  sX <{{F}} [0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0] *> sR.
Proof. apply ev_fast. execute. Qed.

Lemma crys_ph0_c (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0] *> sR) -->*
  (crysHead P1 *> blk7 *> sX) {{E}}> sR.
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crys_ph1_a (sX sR : side) :
  [1; 0; 0; 1; 1; 1; 1] *> sX <{{B}} sR -->* sX <{{F}} [0; 0; 0; 0; 1; 0; 0] *> sR.
Proof. apply ev_fast. execute. Qed.

Lemma crys_ph1_b (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 1; 0; 0] *> sR) -->* (crysHead P2 *> sX) {{E}}> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph2 (sX sR : side) :
  crysHead P2 *> sX <{{F}} sR -->* (crysHead P3 *> sX) {{E}}> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph3_a (sX sR : side) :
  crysHead P3 *> sX <{{B}} sR -->* sX <{{F}} [0; 0; 0; 0; 0; 0; 0; 1; 0; 0] *> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph3_b (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 0; 0; 1; 0; 0] *> sR) -->*
  sX <{{F}} [0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 1; 0; 0] *> sR.
Proof. apply ev_fast. execute. Qed.

Lemma crys_ph3_c (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 1; 0; 0] *> sR) -->*
  (crysHead P4 *> blk7 *> sX) {{E}}> sR.
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crys_ph4 (sX sR : side) :
  crysHead P4 *> sX <{{F}} sR -->* (crysHead P5 *> sX) {{E}}> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph5_a (sX sR : side) :
  crysHead P5 *> sX <{{B}} sR -->* sX <{{F}} [0; 0; 0; 0; 0; 0; 1; 0; 0] *> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph5_b (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 0; 1; 0; 0] *> sR) -->*
  sX <{{F}} [0; 0; 0; 0; 0; 1; 0; 0; 1; 1; 0; 0] *> sR.
Proof. apply ev_fast. execute. Qed.

Lemma crys_ph5_c (sX sR : side) :
  [1; 1; 1] *> sX {{B}}> ([0; 0; 0; 0; 0; 1; 0; 0; 1; 1; 0; 0] *> sR) -->*
  (crysHead P6 *> blk7 *> sX) {{B}}> sR.
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crys_ph6 (sX sR : side) :
  crysHead P6 *> sX <{{F}} sR -->* (crysHead P7 *> sX) {{B}}> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph7 (sX sR : side) :
  crysHead P7 *> sX <{{E}} sR -->* (crysHead P0 *> sX) {{A}}> sR.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crystal_bounce (ph : Phase) (c : nat) (sR : side) :
  exists c',
    crysTape ph c <{{fst (wallStepSpec ph)}} sR -->*
    crysTape (nextPhase ph) c' {{snd (wallStepSpec ph)}}> sR.
Proof.
  destruct ph; simpl wallStepSpec; simpl nextPhase; simpl fst; simpl snd.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph0_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    eapply ev_trans; [apply crys_ph0_b |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph0_c.
  - exists c. unfold crysTape.
    eapply ev_trans; [apply crys_ph1_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph1_b.
  - exists c. unfold crysTape. apply crys_ph2.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph3_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    eapply ev_trans; [apply crys_ph3_b |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph3_c.
  - exists c. unfold crysTape. apply crys_ph4.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph5_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    eapply ev_trans; [apply crys_ph5_b |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph5_c.
  - exists c. unfold crysTape. apply crys_ph6.
  - exists c. unfold crysTape. apply crys_ph7.
Qed.

(* ========================================================================== *)
(* Section 4: Link 3 (6,818 -> Y1 Entry) & 13-State Autonomous Wall           *)
(* ========================================================================== *)

Definition simCrysZip1 (ph : Phase) (q : Q) (lb rb : list bool)
    : option (Phase * Q * list bool * list bool) :=
  let '(sym, rb') := popBit rb in
  match tmStepRaw q sym with
  | None => None
  | Some (nq, w, true) => Some (ph, nq, w :: lb, rb')
  | Some (nq, w, false) =>
    let rbW := consTrim w rb' in
    match lb with
    | nl :: lb' => Some (ph, nq, lb', nl :: rbW)
    | [] =>
      let '(expIn, qOut) := wallStepSpec ph in
      if qEqb nq expIn then Some (nextPhase ph, qOut, [], rbW) else None
    end
  end.

Fixpoint simCrysZip (n : nat) (st : option (Phase * Q * list bool * list bool))
    : option (Phase * Q * list bool * list bool) :=
  match n with
  | O => st
  | S n' =>
    match st with
    | None => None
    | Some (ph, q, lb, rb) => simCrysZip n' (simCrysZip1 ph q lb rb)
    end
  end.

Fixpoint simCrysZipChunks (chunks chunkSize : nat)
    (st : option (Phase * Q * list bool * list bool))
    : option (Phase * Q * list bool * list bool) :=
  match chunks with
  | O => st
  | S chunks' => simCrysZipChunks chunks' chunkSize (simCrysZip chunkSize st)
  end.

Lemma simCrysZip_none n : simCrysZip n None = None.
Proof. destruct n; reflexivity. Qed.

Lemma simCrysZipChunks_none chunks chunkSize :
  simCrysZipChunks chunks chunkSize None = None.
Proof.
  induction chunks as [|k IH]; simpl; [reflexivity |].
  rewrite simCrysZip_none. exact IH.
Qed.

Lemma simCrysZip1_sound ph q ph' q' lb rb lb' rb' :
  simCrysZip1 ph q lb rb = Some (ph', q', lb', rb') ->
  forall c, exists c',
    bitsToSide lb (crysTape ph c) {{q}}> bitsToSide rb 0inf -->*
    bitsToSide lb' (crysTape ph' c') {{q'}}> bitsToSide rb' 0inf.
Proof.
  intros H c. unfold simCrysZip1 in H.
  rewrite (popBit_spec rb).
  destruct (popBit rb) as [sym rbT]; simpl fst; simpl snd.
  destruct (tmStepRaw q sym) as [[[nq w] [|]] |] eqn:Hst; [| | discriminate].
  - inversion H; subst. exists c. simpl bitsToSide.
    exact (step_raw_right _ _ _ _ _ _ Hst).
  - destruct lb as [|nl lbT].
    + destruct (wallStepSpec ph) as [expIn qOut] eqn:Hws.
      destruct (qEqb nq expIn) eqn:Heq; [| discriminate].
      apply qEqb_eq in Heq. inversion H; subst.
      pose proof (crystal_bounce ph c (bitsToSide (consTrim w rbT) 0inf)) as [c' Hcb].
      rewrite Hws in Hcb; simpl fst in Hcb; simpl snd in Hcb.
      exists c'. simpl bitsToSide.
      pose proof (step_raw_left _ _ _ _ (crysTape ph c) (bitsToSide rbT 0inf) Hst) as Hs.
      rewrite <- (bitsToSide_consTrim w rbT) in Hs.
      exact (ev_trans _ _ _ Hs Hcb).
    + inversion H; subst. exists c. simpl bitsToSide.
      rewrite bitsToSide_consTrim.
      exact (step_raw_left _ _ _ _ _ _ Hst).
Qed.

Lemma simCrysZip_sound n ph q ph' q' lb rb lb' rb' :
  simCrysZip n (Some (ph, q, lb, rb)) = Some (ph', q', lb', rb') ->
  forall c, exists c',
    bitsToSide lb (crysTape ph c) {{q}}> bitsToSide rb 0inf -->*
    bitsToSide lb' (crysTape ph' c') {{q'}}> bitsToSide rb' 0inf.
Proof.
  revert ph q lb rb. induction n as [|n IH]; intros ph q lb rb H c; simpl in H.
  - inversion H; subst. exists c. apply evstep_refl.
  - destruct (simCrysZip1 ph q lb rb) as [[[[ph1 q1] lb1] rb1] |] eqn:H1.
    + destruct (simCrysZip1_sound _ _ _ _ _ _ _ _ H1 c) as [c1 Hr1].
      destruct (IH _ _ _ _ H c1) as [c2 Hr2].
      exists c2. exact (ev_trans _ _ _ Hr1 Hr2).
    + rewrite simCrysZip_none in H. discriminate.
Qed.

Lemma simCrysZipChunks_sound chunks chunkSize ph q ph' q' lb rb lb' rb' :
  simCrysZipChunks chunks chunkSize (Some (ph, q, lb, rb)) = Some (ph', q', lb', rb') ->
  forall c, exists c',
    bitsToSide lb (crysTape ph c) {{q}}> bitsToSide rb 0inf -->*
    bitsToSide lb' (crysTape ph' c') {{q'}}> bitsToSide rb' 0inf.
Proof.
  revert ph q lb rb. induction chunks as [|k IH]; intros ph q lb rb H c; simpl in H.
  - inversion H; subst. exists c. apply evstep_refl.
  - destruct (simCrysZip chunkSize (Some (ph, q, lb, rb))) as [[[[ph1 q1] lb1] rb1] |] eqn:H1.
    + destruct (simCrysZip_sound _ _ _ _ _ _ _ _ _ H1 c) as [c1 Hr1].
      destruct (IH _ _ _ _ H c1) as [c2 Hr2].
      exists c2. exact (ev_trans _ _ _ Hr1 Hr2).
    + rewrite simCrysZipChunks_none in H. discriminate.
Qed.

Lemma crys0_13_eq : bitsToSide crys0_13 0inf = crysTape P0 13%nat.
Proof.
  rewrite bitsToSide_eq_str. unfold crysTape.
  rewrite <- !Str_app_assoc.
  reflexivity.
Qed.

Inductive WallIdx : Type :=
  | W0 | W1 | W2 | W3 | W4 | W5 | W6 | W7 | W8 | W9 | W10 | W11 | W12.

Definition nextWallIdx (w : WallIdx) : WallIdx :=
  match w with
  | W0 => W1 | W1 => W2 | W2 => W3 | W3 => W4 | W4 => W5
  | W5 => W6 | W6 => W7 | W7 => W8 | W8 => W9 | W9 => W10
  | W10 => W11 | W11 => W12 | W12 => W0
  end.

Definition pref35At (w : WallIdx) : list bool :=
  match w with
  | W0 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; true; false; true; true; true; true; true]
  | W1 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; false; false; true; true; true; true; false; false; true; false; true; true; true; true; true; true; true; true]
  | W2 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; true; false; false; true; true; true; true; false; false; true; true; true; true; true; true; true]
  | W3 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; true; false; false; true; true; true; true; true; true; true; false; true; true; true; true; true]
  | W4 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; false; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true]
  | W5 => [true; true; false; false; true; false; true; true; true; true; false; true; true; true; false; false; true; false; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true]
  | W6 => [true; true; false; false; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; true; false; false; true; false; true; true; true; true; true; false; true; true; true; true; true]
  | W7 => [true; true; false; false; true; true; true; true; true; true; true; false; false; true; true; true; true; false; false; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true]
  | W8 => [true; true; false; false; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; false; false; true; true; true; true; true; true; true]
  | W9 => [true; true; false; false; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; true; false; true; true; true; true; true]
  | W10 => [true; true; false; false; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; false; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true]
  | W11 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; false; true; true; true; true; true; false; false; true; false; true; true; true; true; true; true; true; true]
  | W12 => [true; true; false; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; true; true; true; true; true; false; false; true; false; true; true; true; true; true; true; true; true]
  end.

Definition checkLink3 : bool :=
  match simCrysZip 41%nat (simCrysZipChunks 184%nat 100%nat (Some (P0, A, [], right6818))) with
  | Some (ph, q, lb, rb) =>
    phaseEqb ph P4 && qEqb q A && boolListEqb lb (pref35At W0) && boolListEqb rb tail35
  | None => false
  end.

Lemma link3_valid : checkLink3 = true.
Proof. vm_check_eq. Qed.

Lemma link3_reaches :
  exists c,
    bitsToSide crys0_13 0inf {{A}}> bitsToSide right6818 0inf -->*
    bitsToSide (pref35At W0) (crysTape P4 c) {{A}}> bitsToSide tail35 0inf.
Proof.
  pose proof link3_valid as Hv. unfold checkLink3 in Hv.
  destruct (simCrysZipChunks 184%nat 100%nat (Some (P0, A, [], right6818)))
    as [[[[ph1 q1] lb1] rb1] |] eqn:H1;
    [| rewrite simCrysZip_none in Hv; discriminate].
  destruct (simCrysZip 41%nat (Some (ph1, q1, lb1, rb1)))
    as [[[[ph2 q2] lb2] rb2] |] eqn:H2;
    [| discriminate].
  apply andb_prop in Hv as [Hv1 Hrb].
  apply andb_prop in Hv1 as [Hv2 Hlb].
  apply andb_prop in Hv2 as [Hph Hq].
  apply phaseEqb_eq in Hph. apply qEqb_eq in Hq.
  apply boolListEqb_eq in Hlb. apply boolListEqb_eq in Hrb.
  subst ph2 q2 lb2 rb2.
  destruct (simCrysZipChunks_sound 184%nat 100%nat _ _ _ _ _ _ _ _ H1 13%nat) as [c1 Hr1].
  destruct (simCrysZip_sound 41%nat _ _ _ _ _ _ _ _ H2 c1) as [c2 Hr2].
  exists c2. rewrite crys0_13_eq.
  exact (ev_trans _ _ _ Hr1 Hr2).
Qed.

Fixpoint simCrysWall (fuel : nat) (ph : Phase) (q : Q) (lb rb : list bool)
    : option (Phase * Q * list bool) :=
  match fuel with
  | O => None
  | S fuel' =>
    match rb with
    | [] => Some (ph, q, lb)
    | sym :: r' =>
      match tmStepRaw q sym with
      | None => None
      | Some (nq, w, true) => simCrysWall fuel' ph nq (w :: lb) r'
      | Some (nq, w, false) =>
        let rw := w :: r' in
        match lb with
        | nl :: l' => simCrysWall fuel' ph nq l' (nl :: rw)
        | [] =>
          let '(expIn, qOut) := wallStepSpec ph in
          if qEqb nq expIn then simCrysWall fuel' (nextPhase ph) qOut [] rw
          else None
        end
      end
    end
  end.

Lemma simCrysWall_sound fuel ph q ph' q' lb rb lb' :
  simCrysWall fuel ph q lb rb = Some (ph', q', lb') ->
  forall c (sR : side), exists c',
    bitsToSide lb (crysTape ph c) {{q}}> bitsToSide rb sR -->*
    bitsToSide lb' (crysTape ph' c') {{q'}}> sR.
Proof.
  revert ph q lb rb. induction fuel as [|fuel IH]; intros ph q lb rb H c sR; simpl in H.
  - discriminate.
  - destruct rb as [|sym r'].
    + inversion H; subst. exists c. apply evstep_refl.
    + destruct (tmStepRaw q sym) as [[[nq w] [|]] |] eqn:Hst; [| | discriminate].
      * destruct (IH _ _ _ _ H c sR) as [c' Hrc].
        exists c'.
        pose proof (step_raw_right _ _ _ _
          (bitsToSide lb (crysTape ph c)) (bitsToSide r' sR) Hst) as Hs.
        simpl bitsToSide in Hs, Hrc |- *.
        exact (ev_trans _ _ _ Hs Hrc).
      * destruct lb as [|nl l'].
        -- destruct (wallStepSpec ph) as [expIn qOut] eqn:Hws.
           destruct (qEqb nq expIn) eqn:Heq; [| discriminate].
           apply qEqb_eq in Heq; subst nq.
           destruct (crystal_bounce ph c (bitsToSide (w :: r') sR)) as [c1 Hcb].
           rewrite Hws in Hcb; simpl fst in Hcb; simpl snd in Hcb.
           destruct (IH _ _ _ _ H c1 sR) as [c2 Hrc].
           exists c2.
           pose proof (step_raw_left _ _ _ _
             (crysTape ph c) (bitsToSide r' sR) Hst) as Hs.
           simpl bitsToSide in Hs, Hcb, Hrc |- *.
           exact (ev_trans _ _ _ Hs (ev_trans _ _ _ Hcb Hrc)).
        -- destruct (IH _ _ _ _ H c sR) as [c' Hrc].
           exists c'.
           pose proof (step_raw_left _ _ _ _
             (bitsToSide (nl :: l') (crysTape ph c)) (bitsToSide r' sR) Hst) as Hs.
           simpl bitsToSide in Hs, Hrc |- *.
           exact (ev_trans _ _ _ Hs Hrc).
Qed.

Definition LeftWallInv (sL : side) : Prop :=
  exists (w : WallIdx) (c : nat), sL = bitsToSide (pref35At w) (crysTape P4 c).

Definition checkPref35One (wallFuel : nat) (w : WallIdx) : bool :=
  match pref35At w with
  | [] => false
  | b0 :: l0 =>
    match simCrysWall wallFuel P4 F l0 [b0] with
    | Some (ph', q', lb') =>
      phaseEqb ph' P4 && qEqb q' A && boolListEqb lb' (pref35At (nextWallIdx w))
    | None => false
    end
  end.

Definition checkPref35Wall : bool :=
  let wf := Nat.mul 19 50 in
  checkPref35One wf W0 && checkPref35One wf W1 && checkPref35One wf W2 && checkPref35One wf W3 &&
  checkPref35One wf W4 && checkPref35One wf W5 && checkPref35One wf W6 && checkPref35One wf W7 &&
  checkPref35One wf W8 && checkPref35One wf W9 && checkPref35One wf W10 && checkPref35One wf W11 &&
  checkPref35One wf W12.

Lemma pref35_wall_valid : checkPref35Wall = true.
Proof. vm_check_eq. Qed.

Lemma checkPref35One_sound wallFuel w :
  checkPref35One wallFuel w = true ->
  forall c (sR : side), exists c',
    bitsToSide (pref35At w) (crysTape P4 c) <{{F}} sR -->*
    bitsToSide (pref35At (nextWallIdx w)) (crysTape P4 c') {{A}}> sR.
Proof.
  intros H c sR. unfold checkPref35One in H.
  destruct (pref35At w) as [|b0 l0] eqn:Hp; [discriminate |].
  destruct (simCrysWall wallFuel P4 F l0 [b0]) as [[[ph' q'] lb'] |] eqn:Hw;
    [| discriminate].
  apply andb_prop in H as [H1 Hlb].
  apply andb_prop in H1 as [Hph Hq].
  apply phaseEqb_eq in Hph. apply qEqb_eq in Hq. apply boolListEqb_eq in Hlb.
  subst ph' q' lb'.
  destruct (simCrysWall_sound _ _ _ _ _ _ _ _ Hw c sR) as [c' Hrc].
  exists c'. simpl bitsToSide in *. exact Hrc.
Qed.

Lemma leftWall_step sL sR :
  LeftWallInv sL ->
  exists sL', LeftWallInv sL' /\ (sL <{{F}} sR -->* sL' {{A}}> sR).
Proof.
  intros [w [c ->]].
  pose proof pref35_wall_valid as Hv. unfold checkPref35Wall in Hv.
  repeat (apply andb_prop in Hv as [Hv ?]).
  assert (Hone : checkPref35One (Nat.mul 19 50) w = true) by (destruct w; assumption).
  destruct (checkPref35One_sound (Nat.mul 19 50) w Hone c sR) as [c' Hrc].
  exists (bitsToSide (pref35At (nextWallIdx w)) (crysTape P4 c')).
  split; [exists (nextWallIdx w), c'; reflexivity | exact Hrc].
Qed.

(* ========================================================================== *)
(* Section 5: Nib/Byte Types, B8 Table, and Slice Byte-Zipper Evaluator       *)
(* ========================================================================== *)

Inductive Nib : Type :=
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | XA | XB | XC | XD | XE | XF.

Inductive Byte : Type := MkB (hi lo : Nib).

Definition nibEqb (x y : Nib) : bool :=
  match x, y with
  | X0, X0 | X1, X1 | X2, X2 | X3, X3 | X4, X4 | X5, X5 | X6, X6 | X7, X7
  | X8, X8 | X9, X9 | XA, XA | XB, XB | XC, XC | XD, XD | XE, XE | XF, XF => true
  | _, _ => false
  end.

Lemma nibEqb_eq x y : nibEqb x y = true -> x = y.
Proof.
  destruct x, y; simpl; congruence.
Qed.

Definition byteEqb (b1 b2 : Byte) : bool :=
  let 'MkB h1 l1 := b1 in
  let 'MkB h2 l2 := b2 in
  nibEqb h1 h2 && nibEqb l1 l2.

Lemma byteEqb_eq b1 b2 : byteEqb b1 b2 = true -> b1 = b2.
Proof.
  destruct b1 as [h1 l1], b2 as [h2 l2]; simpl.
  intros H. apply andb_prop in H as [Hh Hl].
  f_equal; [exact (nibEqb_eq _ _ Hh) | exact (nibEqb_eq _ _ Hl)].
Qed.

Local Notation h00 := (MkB X0 X0).
Local Notation h02 := (MkB X0 X2).
Local Notation h04 := (MkB X0 X4).
Local Notation h24 := (MkB X2 X4).
Local Notation h64 := (MkB X6 X4).

Definition nibBits (n : Nib) : list bool :=
  match n with
  | X0 => [false; false; false; false]
  | X1 => [true;  false; false; false]
  | X2 => [false; true;  false; false]
  | X3 => [true;  true;  false; false]
  | X4 => [false; false; true;  false]
  | X5 => [true;  false; true;  false]
  | X6 => [false; true;  true;  false]
  | X7 => [true;  true;  true;  false]
  | X8 => [false; false; false; true]
  | X9 => [true;  false; false; true]
  | XA => [false; true;  false; true]
  | XB => [true;  true;  false; true]
  | XC => [false; false; true;  true]
  | XD => [true;  false; true;  true]
  | XE => [false; true;  true;  true]
  | XF => [true;  true;  true;  true]
  end.

Definition packNib (b0 b1 b2 b3 : bool) : Nib :=
  match b0, b1, b2, b3 with
  | false, false, false, false => X0
  | true,  false, false, false => X1
  | false, true,  false, false => X2
  | true,  true,  false, false => X3
  | false, false, true,  false => X4
  | true,  false, true,  false => X5
  | false, true,  true,  false => X6
  | true,  true,  true,  false => X7
  | false, false, false, true  => X8
  | true,  false, false, true  => X9
  | false, true,  false, true  => XA
  | true,  true,  false, true  => XB
  | false, false, true,  true  => XC
  | true,  false, true,  true  => XD
  | false, true,  true,  true  => XE
  | true,  true,  true,  true  => XF
  end.

Lemma nibBits_packNib b0 b1 b2 b3 :
  nibBits (packNib b0 b1 b2 b3) = [b0; b1; b2; b3].
Proof.
  destruct b0, b1, b2, b3; reflexivity.
Qed.

Lemma nibBits_len n : length (nibBits n) = 4%nat.
Proof.
  destruct n; reflexivity.
Qed.

Definition byteBits (b : Byte) : list bool :=
  let 'MkB hi lo := b in nibBits lo ++ nibBits hi.

Lemma byteBits_len b : length (byteBits b) = 8%nat.
Proof.
  destruct b as [hi lo]. unfold byteBits.
  rewrite length_app, !nibBits_len. reflexivity.
Qed.

Definition packBits8 (b0 b1 b2 b3 b4 b5 b6 b7 : bool) : Byte :=
  MkB (packNib b4 b5 b6 b7) (packNib b0 b1 b2 b3).

Lemma byteBits_packBits8 b0 b1 b2 b3 b4 b5 b6 b7 :
  byteBits (packBits8 b0 b1 b2 b3 b4 b5 b6 b7) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
  unfold byteBits, packBits8. rewrite !nibBits_packNib. reflexivity.
Qed.

Definition packBitsList (xs : list bool) : Byte :=
  match xs with
  | [b0; b1; b2; b3; b4; b5; b6; b7] => packBits8 b0 b1 b2 b3 b4 b5 b6 b7
  | _ => h00
  end.
Arguments packBitsList : simpl never.

Lemma byteBits_packBitsList xs :
  length xs = 8%nat -> byteBits (packBitsList xs) = xs.
Proof.
  unfold packBitsList.
  destruct xs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 xs]]]]]]]]];
    simpl; intros H; try discriminate.
  exact (byteBits_packBits8 b0 b1 b2 b3 b4 b5 b6 b7).
Qed.

Inductive B8Out : Type :=
  | B8Left (qOut : Q) (outB : Byte)
  | B8Right (qOut : Q) (outB : Byte)
  | B8Halt
  | B8Fail.

Inductive Nib16 (Tp : Type) : Type :=
  | N16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf : Tp).
Arguments N16 {Tp} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition nib16_get {Tp : Type} (t : Nib16 Tp) (n : Nib) : Tp :=
  let 'N16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf := t in
  match n with
  | X0 => v0 | X1 => v1 | X2 => v2 | X3 => v3
  | X4 => v4 | X5 => v5 | X6 => v6 | X7 => v7
  | X8 => v8 | X9 => v9 | XA => va | XB => vb
  | XC => vc | XD => vd | XE => ve | XF => vf
  end.

Inductive B8Table : Type :=
  | MkB8T (t00 t01 t02 t03 t04 t05 t10 t11 t12 t13 t14 t15 : Nib16 (Nib16 B8Out)).

Definition b8TabGet (tbl : B8Table) (side_b : bool) (q : Q) : Nib16 (Nib16 B8Out) :=
  let 'MkB8T t00 t01 t02 t03 t04 t05 t10 t11 t12 t13 t14 t15 := tbl in
  match side_b, q with
  | false, A => t00 | false, B => t01 | false, C => t02
  | false, D => t03 | false, E => t04 | false, F => t05
  | true,  A => t10 | true,  B => t11 | true,  C => t12
  | true,  D => t13 | true,  E => t14 | true,  F => t15
  end.

Definition b8EntryT (tbl : B8Table) (side_b : bool) (q : Q) (b : Byte) : B8Out :=
  let 'MkB hi lo := b in nib16_get (nib16_get (b8TabGet tbl side_b q) hi) lo.
Arguments b8EntryT : simpl never.

Definition byteBitsToSide (b : Byte) (s : side) : side :=
  bitsToSide (byteBits b) s.

Definition byteBitsRevToSide (b : Byte) (s : side) : side :=
  bitsToSide (rev (byteBits b)) s.

Definition byteEntryCfg (side_b : bool) (q : Q) (b : Byte) (sL sR : side) : Q * tape :=
  if side_b then (byteBitsRevToSide b sL <{{q}} sR)
  else (sL {{q}}> byteBitsToSide b sR).

Fixpoint simB8Raw (fuel : nat) (q : Q) (lb : list bool) (cur : bool) (rb : list bool) : B8Out :=
  match fuel with
  | O => B8Fail
  | S fuel' =>
    match tmStepRaw q cur with
    | None => B8Halt
    | Some (nq, w, true) =>
      match rb with
      | [] => B8Right nq (packBitsList (rev lb ++ [w]))
      | nr :: r' => simB8Raw fuel' nq (w :: lb) nr r'
      end
    | Some (nq, w, false) =>
      match lb with
      | [] => B8Left nq (packBitsList (w :: rb))
      | nl :: l' => simB8Raw fuel' nq l' nl (w :: rb)
      end
    end
  end.

Lemma simB8Raw_sound fuel q lb cur rb (sL sR : side) :
  (length lb + 1 + length rb = 8)%nat ->
  match simB8Raw fuel q lb cur rb with
  | B8Left qOut outB =>
    bitsToSide lb sL {{q}}> bitsToSide (cur :: rb) sR -->*
    sL <{{qOut}} byteBitsToSide outB sR
  | B8Right qOut outB =>
    bitsToSide lb sL {{q}}> bitsToSide (cur :: rb) sR -->*
    byteBitsRevToSide outB sL {{qOut}}> sR
  | B8Halt =>
    halts tm (bitsToSide lb sL {{q}}> bitsToSide (cur :: rb) sR)
  | B8Fail => True
  end.
Proof.
  revert q lb cur rb. induction fuel as [|fuel IH]; intros q lb cur rb Hlen; simpl.
  - exact I.
  - destruct (tmStepRaw q cur) as [[[nq w] [|]] |] eqn:Hst.
    + destruct rb as [|nr r'].
      * assert (Hlen8 : length (rev lb ++ [w]) = 8%nat).
        { rewrite length_app, length_rev. simpl in Hlen |- *. lia. }
        unfold byteBitsRevToSide.
        rewrite (byteBits_packBitsList _ Hlen8).
        rewrite rev_app_distr, rev_involutive; simpl.
        exact (step_raw_right _ _ _ _ (bitsToSide lb sL) sR Hst).
      * assert (Hlen' : (length (w :: lb) + 1 + length r' = 8)%nat)
          by (simpl in Hlen |- *; lia).
        pose proof (IH nq (w :: lb) nr r' Hlen') as Hih.
        pose proof (step_raw_right _ _ _ _ (bitsToSide lb sL) (bitsToSide (nr :: r') sR) Hst) as Hs.
        simpl bitsToSide in Hih |- *.
        destruct (simB8Raw fuel nq (w :: lb) nr r').
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (evstep_halts _ _ Hs Hih).
        -- exact I.
    + destruct lb as [|nl l'].
      * assert (Hlen8 : length (w :: rb) = 8%nat) by (simpl in Hlen |- *; lia).
        unfold byteBitsToSide.
        rewrite (byteBits_packBitsList _ Hlen8). simpl bitsToSide.
        exact (step_raw_left _ _ _ _ sL (bitsToSide rb sR) Hst).
      * assert (Hlen' : (length l' + 1 + length (w :: rb) = 8)%nat)
          by (simpl in Hlen |- *; lia).
        pose proof (IH nq l' nl (w :: rb) Hlen') as Hih.
        pose proof (step_raw_left _ _ _ _ (bitsToSide (nl :: l') sL) (bitsToSide rb sR) Hst) as Hs.
        simpl bitsToSide in Hs, Hih |- *.
        destruct (simB8Raw fuel nq l' nl (w :: rb)).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (evstep_halts _ _ Hs Hih).
        -- exact I.
    + simpl bitsToSide. exact (step_raw_none _ _ _ _ Hst).
Qed.

(* Build the small lookup table from the byte simulator. *)
Definition tabulateNib {T} (f : Nib -> T) : Nib16 T :=
  N16 (f X0) (f X1) (f X2) (f X3) (f X4) (f X5) (f X6) (f X7)
      (f X8) (f X9) (f XA) (f XB) (f XC) (f XD) (f XE) (f XF).

Definition generateByte (side_b : bool) (q : Q) (b : Byte) :=
  if side_b then
    match rev (byteBits b) with [] => B8Fail | c :: l => simB8Raw 45 q l c [] end
  else
    match byteBits b with [] => B8Fail | c :: r => simB8Raw 45 q [] c r end.

Definition generateRow (side_b : bool) (q : Q) :=
  tabulateNib (fun hi => tabulateNib (fun lo => generateByte side_b q (MkB hi lo))).

Definition makeB8Table :=
  MkB8T (generateRow false A) (generateRow false B) (generateRow false C)
         (generateRow false D) (generateRow false E) (generateRow false F)
         (generateRow true A) (generateRow true B) (generateRow true C)
         (generateRow true D) (generateRow true E) (generateRow true F).

Definition theB8Table := Eval vm_compute in makeB8Table.
Arguments theB8Table : simpl never.

Lemma get_tabulate {T} (f : Nib -> T) n : nib16_get (tabulateNib f) n = f n.
Proof. destruct n; reflexivity. Qed.

Lemma byte_lookup side_b q b :
  b8EntryT theB8Table side_b q b = generateByte side_b q b.
Proof.
  assert (H : theB8Table = makeB8Table) by vm_check_eq.
  rewrite H. destruct b as [hi lo].
  assert (Hrow : b8TabGet makeB8Table side_b q = generateRow side_b q)
    by (destruct side_b, q; reflexivity).
  unfold b8EntryT. rewrite Hrow. unfold generateRow. now rewrite !get_tabulate.
Qed.

Lemma b8Entry_sound side_b q b (sL sR : side) :
  match b8EntryT theB8Table side_b q b with
  | B8Left qOut outB =>
    byteEntryCfg side_b q b sL sR -->* sL <{{qOut}} byteBitsToSide outB sR
  | B8Right qOut outB =>
    byteEntryCfg side_b q b sL sR -->* byteBitsRevToSide outB sL {{qOut}}> sR
  | B8Halt => halts tm (byteEntryCfg side_b q b sL sR)
  | B8Fail => True
  end.
Proof.
  rewrite byte_lookup. unfold generateByte, byteEntryCfg.
  pose proof (byteBits_len b) as Hlen.
  destruct side_b.
  - rewrite <- length_rev in Hlen. unfold byteBitsRevToSide.
    destruct (rev (byteBits b)) as [|c l]; [exact I|].
    exact (simB8Raw_sound 45 q l c [] sL sR ltac:(simpl in *; lia)).
  - unfold byteBitsToSide.
    destruct (byteBits b) as [|c r]; [exact I|].
    exact (simB8Raw_sound 45 q [] c r sL sR ltac:(simpl in *; lia)).
Qed.

Fixpoint bytesToRight (bs : list Byte) (sR : side) : side :=
  match bs with
  | [] => sR
  | b :: bs' => byteBitsToSide b (bytesToRight bs' sR)
  end.

Fixpoint bytesToLeft (bs : list Byte) (sL : side) : side :=
  match bs with
  | [] => sL
  | b :: bs' => byteBitsRevToSide b (bytesToLeft bs' sL)
  end.

Inductive SliceOut : Type :=
  | SliceLeft (qOut : Q) (outB : Byte) (rBytes : list Byte)
  | SliceRight (qOut : Q) (outRev : list Byte)
  | SliceHalt
  | SliceFail.

Fixpoint simSliceBytes (tbl : B8Table) (fuel : nat) (side_b : bool) (q : Q)
    (lb : list Byte) (cb : Byte) (rb : list Byte) : SliceOut :=
  match fuel with
  | O => SliceFail
  | S fuel' =>
    match b8EntryT tbl side_b q cb with
    | B8Left qOut outB =>
      match lb with
      | [] => SliceLeft qOut outB rb
      | pb :: lb' => simSliceBytes tbl fuel' true qOut lb' pb (outB :: rb)
      end
    | B8Right qOut outB =>
      match rb with
      | [] => SliceRight qOut (outB :: lb)
      | nb :: rb' => simSliceBytes tbl fuel' false qOut (outB :: lb) nb rb'
      end
    | B8Halt => SliceHalt
    | B8Fail => SliceFail
    end
  end.

Lemma simSliceBytes_sound fuel side_b q lb cb rb (sL sR : side) :
  match simSliceBytes theB8Table fuel side_b q lb cb rb with
  | SliceLeft qOut outB r' =>
    byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR) -->*
    sL <{{qOut}} bytesToRight (outB :: r') sR
  | SliceRight qOut outRev =>
    byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR) -->*
    bytesToLeft outRev sL {{qOut}}> sR
  | SliceHalt =>
    halts tm (byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR))
  | SliceFail => True
  end.
Proof.
  revert side_b q lb cb rb.
  induction fuel as [|fuel IH]; intros side_b q lb cb rb; simpl.
  - exact I.
  - pose proof (b8Entry_sound side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR)) as Hb8.
    destruct (b8EntryT theB8Table side_b q cb) as [qOut outB | qOut outB | |].
    + destruct lb as [|pb lb']; simpl in Hb8 |- *.
      * exact Hb8.
      * pose proof (IH true qOut lb' pb (outB :: rb)) as Hih.
        simpl in Hih.
        destruct (simSliceBytes theB8Table fuel true qOut lb' pb (outB :: rb)).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (evstep_halts _ _ Hb8 Hih).
        -- exact I.
    + destruct rb as [|nb rb']; simpl in Hb8 |- *.
      * exact Hb8.
      * pose proof (IH false qOut (outB :: lb) nb rb') as Hih.
        simpl in Hih.
        destruct (simSliceBytes theB8Table fuel false qOut (outB :: lb) nb rb').
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (evstep_halts _ _ Hb8 Hih).
        -- exact I.
    + exact Hb8.
    + exact I.
Qed.
Arguments simSliceBytes : simpl never.

(** A wall is a stack of byte slices. Its hidden bottom is represented
    by [LeftWallInv], so cache entries are valid for any bottom phase
    and counter, not for a single concrete history. *)
Definition Wall := list (list Byte).

Fixpoint wallTape (w : Wall) (sL : side) : Prop :=
  match w with
  | [] => LeftWallInv sL
  | b :: rest => exists s, wallTape rest s /\ sL = bytesToLeft b s
  end.

Module ByteKey <: HashTable.HashableType.
  Definition K := Byte.
  Definition K_hash (b : K) :=
    HashTable.HashConcat.list_hash HashTable.HashConcat.bool_hash (byteBits b).
  Definition K_eq := byteEqb.
  Lemma K_eq_spec a b : Bool.reflect (a=b) (K_eq a b).
  Proof.
    destruct (K_eq a b) eqn:E.
    - constructor; exact (byteEqb_eq _ _ E).
    - constructor. intros ->. assert (H : forall n, nibEqb n n = true)
        by (intros []; reflexivity).
      destruct b; unfold K_eq, byteEqb in E. rewrite !H in E; discriminate.
  Qed.
End ByteKey.

Module QKey <: HashTable.HashableType.
  Definition K := Q.
  Definition K_hash := BB62.q_hash.
  Definition K_eq := BB62.q_eqb.
  Definition K_eq_spec := BB62.q_eqb_spec.
End QKey.

Module SliceKey := HashTable.ListHash ByteKey.
Module WallKey := HashTable.ListHash SliceKey.
Module CacheKey := HashTable.ProdHash WallKey QKey.
Module CacheVal <: HashTable.ValueType.
  Definition V := (Wall * Q)%type.
End CacheVal.
Module Cache := HashTable.HashMap CacheKey CacheVal.

Definition Memo := Cache.hmap_t.
Definition WallResult := (option (Wall * Q) * Memo)%type.
Definition WallCall := Wall -> Q -> Memo -> WallResult.

Definition returnSpec (src : Wall * Q) (out : Wall * Q) : Prop :=
  forall sL sR, wallTape (fst src) sL ->
  exists sL', wallTape (fst out) sL' /\ (sL <{{snd src}} sR -->* sL' {{snd out}}> sR).

Definition memoValid (t : Memo) :=
  Cache.hmap_WF t /\
  forall key value, Cache.hmap_get key t = Some value -> returnSpec key value.

Definition returnSound key (p : WallResult) :=
  memoValid (snd p) /\
  match fst p with Some out => returnSpec key out | None => True end.

Lemma memo_empty len : memoValid (Cache.hmap_make len).
Proof.
  split; [apply Cache.hmap_make_WF|].
  intros k v; rewrite Cache.hmap_get_make; discriminate.
Qed.

Lemma memo_insert t k v : memoValid t -> returnSpec k v -> memoValid (Cache.hmap_set k v t).
Proof.
  intros [Hwf Hmemo] Hv; split; [now apply Cache.hmap_set_WF|].
  intros key value.
  destruct (CacheKey.K_eq_spec key k) as [->|Hne].
  - rewrite Cache.hmap_get_set_same by exact Hwf. now intros [= <-].
  - rewrite Cache.hmap_get_set_other by assumption. apply Hmemo.
Qed.

Fixpoint returnSlice (call : WallCall) (fuel : nat)
    (parent : Wall) (side_b : bool) (q : Q) (lb : list Byte)
    (cb : Byte) (rb : list Byte) (t : Memo) : WallResult :=
  match fuel with
  | O => (None,t)
  | S fuel' =>
    match simSliceBytes theB8Table 50 side_b q lb cb rb with
    | SliceRight q' out => (Some (out :: parent,q'),t)
    | SliceLeft q' b r' =>
      let '(ret,t') := call parent q' t in
      match ret with
      | Some (par',q'') => returnSlice call fuel' par' false q'' [] b r' t'
      | None => (None,t')
      end
    | _ => (None,t)
    end
  end.

(* Arguments [depth] and [fuel] only bound the search; exhausting a
   bound yields no rule. A memo entry contains a computed return. *)
Fixpoint returnWall (depth : nat) (w : Wall) (q : Q) (t : Memo) : WallResult :=
  match Cache.hmap_get (w,q) t with
  | Some out => (Some out,t)
  | None =>
    let '(ret,t') :=
      match w with
      | [] => match q with F => (Some ([],A),t) | _ => (None,t) end
      | (b :: lb) :: parent =>
        match depth with
        | O => (None,t)
        | S d => returnSlice (fun w' q' t'' => returnWall d w' q' t'') 170 parent true q lb b [] t
        end
      | [] :: _ => (None,t)
      end in
    match ret with
    | Some out => (Some out, Cache.hmap_set (w,q) out t')
    | None => (None,t')
    end
  end.

Fixpoint slicesSide (blocks : list (list Byte)) : side :=
  match blocks with
  | [] => 0inf
  | b :: blocks' => bytesToRight b (slicesSide blocks')
  end.

(* The cut positions are chosen independently of the contents. The
   first three slices are the finite right prefix, padded with zeros. *)
Definition blankWidths : list nat := [2;2;2;2;2;4;4;2;2;4;2;4;5;3;6;4;4;6].
Definition blankSlices := map (fun n => repeat h00 n) blankWidths.

Fixpoint runTop (fuel : nat) (w : Wall) (side_b : bool) (q : Q)
    (cb : Byte) (rb : list Byte) (blocks : list (list Byte)) (t : Memo) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match simSliceBytes theB8Table 50 side_b q [] cb rb with
    | SliceHalt => true
    | SliceLeft q' b r' =>
      match returnWall (length w) w q' t with
      | (Some (w',q''),t') => runTop fuel' w' false q'' b r' blocks t'
      | _ => false
      end
    | SliceRight q' out =>
      match blocks with
      | (b :: r) :: blocks' => runTop fuel' (out :: w) false q' b r blocks' t
      | _ => false
      end
    | SliceFail => false
    end
  end.

Definition checkRun : bool :=
  runTop 450 [] false A h04 [h00] ([h00;h24] :: [h64;h02] :: blankSlices)
    (Cache.hmap_make (Uint63.of_Z (BinNums.Zpos 65536%positive))).

Definition sliceSpec parent side_b q lb cb rb (out : Wall * Q) : Prop :=
  forall sL sR, wallTape parent sL ->
    exists sL', wallTape (fst out) sL' /\
      (byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR)
       -->* sL' {{snd out}}> sR).

Lemma returnSlice_sound (call : WallCall)
    (Hcall : forall w q t, memoValid t -> returnSound (w,q) (call w q t)) fuel :
  forall w side_b q lb cb rb t, memoValid t ->
    let '(ret,t') := returnSlice call fuel w side_b q lb cb rb t in
    memoValid t' /\
      match ret with Some out => sliceSpec w side_b q lb cb rb out | None => True end.
Proof.
  induction fuel as [|fuel IH]; intros w dir q lb cb rb t Ht.
  - exact (conj Ht I).
  - cbn [returnSlice].
    destruct (simSliceBytes theB8Table 50 dir q lb cb rb) as [p b r|p out| |] eqn:Es;
      try exact (conj Ht I).
    + specialize (Hcall w p t Ht).
      destruct (call w p t) as [[[w' p']|] t']; cbn [returnSound fst snd] in Hcall;
        [| exact Hcall].
      destruct Hcall as [Ht' Hret].
      specialize (IH w' false p' [] b r t' Ht').
      destruct (returnSlice call fuel w' false p' [] b r t') as [[v|] t''];
        [| exact IH].
      destruct IH as [Ht'' Hnext]. split; [exact Ht''|].
      intros sL sR Hw.
      pose proof (simSliceBytes_sound 50 dir q lb cb rb sL sR) as Hs.
      rewrite Es in Hs.
      destruct (Hret sL (bytesToRight (b::r) sR) Hw) as [sL' [Hw' Hr]].
      destruct (Hnext sL' sR Hw') as [sL'' [Hw'' Hn]].
      exists sL''. split; [exact Hw''|].
      exact (ev_trans _ _ _ Hs (ev_trans _ _ _ Hr Hn)).
    + split; [exact Ht|]. intros sL sR Hw.
      exists (bytesToLeft out sL). split; [now exists sL|].
      pose proof (simSliceBytes_sound 50 dir q lb cb rb sL sR) as Hs.
      now rewrite Es in Hs.
Qed.

Lemma returnWall_unfold depth w q t :
  returnWall depth w q t =
    match Cache.hmap_get (w,q) t with
    | Some out => (Some out,t)
    | None =>
      let '(ret,t') :=
        match w with
        | [] => match q with F => (Some ([],A),t) | _ => (None,t) end
        | (b :: lb) :: parent =>
          match depth with
          | O => (None,t)
          | S d => returnSlice (fun w' q' t'' => returnWall d w' q' t'') 170 parent true q lb b [] t
          end
        | [] :: _ => (None,t)
        end in
      match ret with
      | Some out => (Some out, Cache.hmap_set (w,q) out t')
      | None => (None,t')
      end
    end.
Proof. destruct depth; reflexivity. Qed.

Lemma returnWall_sound depth :
  forall w q t, memoValid t -> returnSound (w,q) (returnWall depth w q t).
Proof.
  induction depth as [|depth IH]; intros w q t Ht; rewrite returnWall_unfold;
    destruct (Cache.hmap_get (w,q) t) as [v|] eqn:E.
  1,3: exact (conj Ht (proj2 Ht _ _ E)).
  all: destruct w as [|[|b lb] w]; try exact (conj Ht I).
  1,2: destruct q; try exact (conj Ht I);
    split; [apply memo_insert; [exact Ht|]|]; exact leftWall_step.
  pose proof (returnSlice_sound _ IH 170 w true q lb b [] t Ht) as H.
  destruct (returnSlice (fun w' q' t' => returnWall depth w' q' t') 170 w true q lb b [] t)
    as [[v|] t'];
    [| exact H].
  destruct H as [Ht' Hslice].
  assert (Hr : returnSpec ((b::lb)::w,q) v).
  { intros sL sR [s [Hw ->]]. exact (Hslice s sR Hw). }
  exact (conj (memo_insert _ _ _ Ht' Hr) Hr).
Qed.

Local Opaque simSliceBytes returnWall.

Lemma runTop_sound fuel :
  forall w dir q cb rb blocks t sL, memoValid t -> wallTape w sL ->
    runTop fuel w dir q cb rb blocks t = true ->
    halts tm (byteEntryCfg dir q cb sL (bytesToRight rb (slicesSide blocks))).
Proof.
  induction fuel as [|fuel IH]; intros w dir q cb rb blocks t sL Ht Hw Hrun;
    cbn [runTop] in Hrun; try discriminate.
  pose proof (simSliceBytes_sound 50 dir q [] cb rb sL (slicesSide blocks)) as Hs.
  destruct (simSliceBytes theB8Table 50 dir q [] cb rb) as [p b r|p out| |];
    try discriminate; [| | exact Hs].
  - pose proof (returnWall_sound (length w) w p t Ht) as H.
    destruct (returnWall (length w) w p t) as [[[w' p']|] t']; try discriminate.
    destruct H as [Ht' Hr].
    destruct (Hr sL (bytesToRight (b::r) (slicesSide blocks)) Hw) as [sL' [Hw' Hstep]].
    exact (evstep_halts _ _ Hs (evstep_halts _ _ Hstep
      (IH w' false p' b r blocks t' sL' Ht' Hw' Hrun))).
  - destruct blocks as [|[|b r] blocks]; try discriminate.
    assert (Hw' : wallTape (out::w) (bytesToLeft out sL)) by now exists sL.
    exact (evstep_halts _ _ Hs
      (IH (out::w) false p b r blocks t (bytesToLeft out sL) Ht Hw' Hrun)).
Qed.

Local Transparent simSliceBytes returnWall.

Lemma zero_cons_0inf : 0 >> 0inf = 0inf.
Proof. symmetry. exact (const_unfold _ 0). Qed.

Lemma bitsToSide_zeros n : bitsToSide (repeat false n) 0inf = 0inf.
Proof. induction n; simpl; [reflexivity | rewrite IHn; exact zero_cons_0inf]. Qed.

Lemma blankSlices_side widths : slicesSide (map (fun n => repeat h00 n) widths) = 0inf.
Proof.
  induction widths as [|n ns IH]; [reflexivity|].
  cbn [map slicesSide]. rewrite IH. clear IH ns. induction n; [reflexivity|].
  change (byteBitsToSide h00 (bytesToRight (repeat h00 n) 0inf) = 0inf).
  rewrite IHn. exact (bitsToSide_zeros 8).
Qed.

Lemma tail_start_eq :
  bitsToSide tail35 0inf =
    bytesToRight [h04;h00] (slicesSide ([h00;h24] :: [h64;h02] :: blankSlices)).
Proof.
  change (bitsToSide tail35 0inf =
    bytesToRight [h04;h00;h00;h24;h64;h02] (slicesSide blankSlices)).
  unfold blankSlices. rewrite blankSlices_side.
  rewrite <- (bitsToSide_zeros 6) at 1. rewrite <- bitsToSide_app. reflexivity.
Qed.

Local Opaque runTop.

Lemma checkRun_sound : checkRun = true -> halts tm c0.
Proof.
  intros Hrun. unfold checkRun in Hrun. destruct link3_reaches as [c Hlink3].
  pose proof (ev_trans _ _ _ link1_reaches Hlink3) as Hreach.
  rewrite tail_start_eq in Hreach.
  assert (Hw : wallTape [] (bitsToSide (pref35At W0) (crysTape P4 c)))
    by (exists W0, c; reflexivity).
  exact (evstep_halts _ _ Hreach
    (runTop_sound 450 [] false A h04 [h00] _ _ _ (memo_empty _) Hw Hrun)).
Qed.

Local Transparent runTop.

Theorem halt : halts tm c0.
Proof. apply checkRun_sound. vm_check_eq. Qed.

End TM1.
