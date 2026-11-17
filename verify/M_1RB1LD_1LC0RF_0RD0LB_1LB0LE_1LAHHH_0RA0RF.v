From BusyCoq Require Import Individual62.
Require Import String List PeanoNat NArith PArith ZifyNat ZifyN Lia.
Import ListNotations.
Open Scope bool_scope.
Open Scope list_scope.
Open Scope sym_scope.

Definition tm : TM := TM_from_str "1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF".

Module M5.

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

Lemma zero_cons_0inf : 0 >> 0inf = 0inf.
Proof. symmetry. exact (const_unfold _ 0). Qed.

Lemma bitsToSide_zeros n : bitsToSide (repeat false n) 0inf = 0inf.
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; exact zero_cons_0inf].
Qed.

Definition tmStepRaw (q : Q) (sym : bool) : option (Q * bool * bool) :=
  match q, sym with
  | A, false => Some (B, true, true)
  | A, true  => Some (D, true, false)
  | B, false => Some (C, true, false)
  | B, true  => Some (F, false, true)
  | C, false => Some (D, false, true)
  | C, true  => Some (B, false, false)
  | D, false => Some (B, true, false)
  | D, true  => Some (E, false, false)
  | E, false => Some (A, true, false)
  | E, true  => None
  | F, false => Some (A, false, true)
  | F, true  => Some (F, false, true)
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

Lemma step_raw_hl_right q nq sym w (sL sR : side) :
  tmStepRaw q sym = Some (nq, w, true) ->
  (bitToSym sym >> sL) <{{q}} sR -->* (bitToSym w >> sL) {{nq}}> sR.
Proof.
  exact (step_raw_right q nq sym w sL sR).
Qed.

Lemma step_raw_hl_left q nq sym w (sL sR : side) :
  tmStepRaw q sym = Some (nq, w, false) ->
  (bitToSym sym >> sL) <{{q}} sR -->* sL <{{nq}} (bitToSym w >> sR).
Proof.
  exact (step_raw_left q nq sym w sL sR).
Qed.

Lemma step_raw_hl_none q sym (sL sR : side) :
  tmStepRaw q sym = None ->
  halts tm ((bitToSym sym >> sL) <{{q}} sR).
Proof.
  exact (step_raw_none q sym sL sR).
Qed.

(* ========================================================================== *)
(* Section 2: Link 1 Soundness (t = 0 -> 303)                                 *)
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

Definition lb303 : list bool := [false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; true; false; false; true].
Definition rb303 : list bool := [true; false; false; true; true; true; true; true; false; false; true].

Definition checkLink1 : bool :=
  match simRawZip 3%nat (simRawZipChunks 3%nat 100%nat (Some (A, [], []))) with
  | Some (q, lb, rb) => qEqb q F && boolListEqb lb lb303 && boolListEqb rb rb303
  | None => false
  end.

Lemma link1_valid : checkLink1 = true.
Proof. vm_check_eq. Qed.

Lemma link1_reaches :
  c0 -->* (bitsToSide lb303 0inf {{F}}> bitsToSide rb303 0inf).
Proof.
  pose proof link1_valid as Hv. unfold checkLink1 in Hv.
  destruct (simRawZipChunks 3%nat 100%nat (Some (A, [], []))) as [[[q1 lb1] rb1] |] eqn:H1;
    [| rewrite simRawZip_none in Hv; discriminate].
  destruct (simRawZip 3%nat (Some (q1, lb1, rb1))) as [[[q2 lb2] rb2] |] eqn:H2;
    [| discriminate].
  apply andb_prop in Hv as [Hv1 Hrb].
  apply andb_prop in Hv1 as [Hq Hlb].
  apply qEqb_eq in Hq. apply boolListEqb_eq in Hlb. apply boolListEqb_eq in Hrb.
  subst q2 lb2 rb2.
  exact (ev_trans _ _ _
    (simRawZipChunks_sound 3%nat 100%nat _ _ _ _ _ _ H1)
    (simRawZip_sound 3%nat _ _ _ _ _ _ H2)).
Qed.

(* ========================================================================== *)
(* Section 3: Link 2 Soundness (Parametric 12-Phase Right Crystal Wall)       *)
(* ========================================================================== *)

Inductive Phase : Type :=
  | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11.

Definition nextPhase (ph : Phase) : Phase :=
  match ph with
  | P0 => P1  | P1 => P2  | P2 => P3  | P3 => P4
  | P4 => P5  | P5 => P6  | P6 => P7  | P7 => P8
  | P8 => P9  | P9 => P10 | P10 => P11 | P11 => P0
  end.

Definition phaseEqb (x y : Phase) : bool :=
  match x, y with
  | P0, P0 | P1, P1 | P2, P2 | P3, P3
  | P4, P4 | P5, P5 | P6, P6 | P7, P7
  | P8, P8 | P9, P9 | P10, P10 | P11, P11 => true
  | _, _ => false
  end.

Lemma phaseEqb_eq x y : phaseEqb x y = true -> x = y.
Proof.
  destruct x, y; simpl; congruence.
Qed.

Definition wallStepSpec (ph : Phase) : Q * Q :=
  match ph with
  | P0  => (F, C)
  | P1  => (D, E)
  | P2  => (F, B)
  | P3  => (F, C)
  | P4  => (D, E)
  | P5  => (F, B)
  | P6  => (A, D)
  | P7  => (F, B)
  | P8  => (A, D)
  | P9  => (F, A)
  | P10 => (B, C)
  | P11 => (B, A)
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

Lemma lpow_comm_app {X : Type} (xs : list X) (c : nat) :
  (xs ^^ c ++ xs)%list = xs ^^ S c.
Proof.
  induction c as [|c IH]; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite <- app_assoc, IH. reflexivity.
Qed.

Definition blk7 : list Sym := [1; 1; 1; 1; 1; 0; 0].
Definition blk7m : list Sym := [1; 0; 0; 0; 0; 0; 0].
Definition blk7b : list Sym := [1; 0; 0; 1; 1; 1; 1].
Definition ctail0 : list Sym := [1].
Definition ctail1 : list Sym := [1; 0; 0; 1].

Definition crysHead (ph : Phase) : list Sym :=
  match ph with
  | P0  => [1; 0; 0]
  | P1  => [1; 1; 1; 1; 0; 0]
  | P2  => [0; 1; 1; 1; 0; 0]
  | P3  => [1; 1; 1; 1; 0; 0]
  | P4  => [1; 0]
  | P5  => [0; 0]
  | P6  => [1; 1; 1; 0; 0]
  | P7  => [1; 1; 1; 0; 0]
  | P8  => [0]
  | P9  => [1; 1; 0; 0]
  | P10 => [1; 0; 1; 1; 1; 0; 0]
  | P11 => [1; 1; 1; 1; 1; 0; 0]
  end.

Definition crysTape (ph : Phase) (c : nat) : side :=
  crysHead ph *> blk7 ^^ c *> ctail0 *> 0inf.

Lemma sweep1R_1 (sL sR : side) :
  sL {{B}}> (blk7 *> sR) -->* (blk7m *> sL) {{B}}> sR.
Proof. apply ev_fast. unfold blk7, blk7m. execute. Qed.

Lemma sweep1R (c : nat) (sL sR : side) :
  sL {{B}}> (blk7 ^^ c *> sR) -->* (blk7m ^^ c *> sL) {{B}}> sR.
Proof.
  revert sL. induction c as [|c IH]; intros sL; [finish |].
  change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c).
  rewrite Str_app_assoc.
  eapply ev_trans; [apply sweep1R_1 |].
  eapply ev_trans; [apply (IH (blk7m *> sL)) |].
  rewrite <- Str_app_assoc, lpow_comm_app. finish.
Qed.

Lemma sweep1_tail (sL : side) :
  sL {{B}}> (ctail0 *> 0inf) -->* sL <{{A}} (ctail1 *> 0inf).
Proof. apply ev_fast. unfold ctail0, ctail1. execute. Qed.

Lemma sweep1L_1 (sL sR : side) :
  (blk7m *> sL) <{{A}} sR -->* sL <{{A}} (blk7b *> sR).
Proof. apply ev_fast. unfold blk7m, blk7b. execute. Qed.

Lemma sweep1L (c : nat) (sL sR : side) :
  (blk7m ^^ c *> sL) <{{A}} sR -->* sL <{{A}} (blk7b ^^ c *> sR).
Proof.
  revert sR. induction c as [|c IH]; intros sR; [finish |].
  change (blk7m ^^ S c) with (blk7m ++ blk7m ^^ c).
  rewrite Str_app_assoc.
  eapply ev_trans; [apply sweep1L_1 |].
  eapply ev_trans; [apply (IH (blk7b *> sR)) |].
  rewrite <- Str_app_assoc, lpow_comm_app. finish.
Qed.

Lemma shift_blk7b (c : nat) :
  blk7b ^^ c *> ctail1 *> 0inf = [1; 0; 0] *> blk7 ^^ c *> ctail0 *> 0inf.
Proof.
  induction c as [|c IH]; [reflexivity |].
  change (blk7b ^^ S c) with (blk7b ++ blk7b ^^ c).
  change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c).
  rewrite !Str_app_assoc, IH. reflexivity.
Qed.

Lemma sweep_blk7 (c : nat) (sL : side) :
  sL {{B}}> (blk7 ^^ c *> ctail0 *> 0inf) -->*
  sL <{{A}} ([1; 0; 0] *> blk7 ^^ c *> ctail0 *> 0inf).
Proof.
  eapply ev_trans; [apply sweep1R |].
  eapply ev_trans; [apply sweep1_tail |].
  eapply ev_trans; [apply sweep1L |].
  rewrite shift_blk7b. finish.
Qed.

Lemma crys_ph0_a (sL sX : side) :
  sL {{F}}> (crysHead P0 *> sX) -->* ([1; 0; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph0_b (sL sX : side) :
  ([1; 0; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->* sL <{{C}} (crysHead P1 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph1 (sL sX : side) :
  sL {{D}}> (crysHead P1 *> sX) -->* sL <{{E}} (crysHead P2 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph2 (sL sX : side) :
  sL {{F}}> (crysHead P2 *> sX) -->* sL <{{B}} (crysHead P3 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph3_a (sL sX : side) :
  sL {{F}}> (crysHead P3 *> sX) -->* ([1; 0; 0; 0; 0; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph3_b (sL sX : side) :
  ([1; 0; 0; 0; 0; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->*
  sL <{{C}} (crysHead P4 *> blk7 *> sX).
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crys_ph4 (sL sX : side) :
  sL {{D}}> (crysHead P4 *> sX) -->* sL <{{E}} (crysHead P5 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph5_a (sL sX : side) :
  sL {{F}}> (crysHead P5 *> sX) -->* ([1; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph5_b (sL sX : side) :
  ([1; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->* sL <{{B}} (crysHead P6 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph6 (sL sX : side) :
  sL {{A}}> (crysHead P6 *> sX) -->* sL <{{D}} (crysHead P7 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph7_a (sL sX : side) :
  sL {{F}}> (crysHead P7 *> sX) -->* ([1; 0; 0; 0; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph7_b (sL sX : side) :
  ([1; 0; 0; 0; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->*
  sL <{{B}} (crysHead P8 *> blk7 *> sX).
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crys_ph8_a (sL sX : side) :
  sL {{A}}> (crysHead P8 *> sX) -->* ([1] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph8_b (sL sX : side) :
  ([1] *> sL) <{{A}} ([1; 0; 0] *> sX) -->* sL <{{D}} (crysHead P9 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph9_a (sL sX : side) :
  sL {{F}}> (crysHead P9 *> sX) -->* ([1; 0; 0; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph9_b (sL sX : side) :
  ([1; 0; 0; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->* sL <{{A}} (crysHead P10 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph10 (sL sX : side) :
  sL {{B}}> (crysHead P10 *> sX) -->* sL <{{C}} (crysHead P11 *> sX).
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph11_a (sL sX : side) :
  sL {{B}}> (crysHead P11 *> sX) -->* ([1; 0; 0; 0; 0; 0; 0] *> sL) {{B}}> sX.
Proof. apply ev_fast. unfold crysHead. execute. Qed.

Lemma crys_ph11_b (sL sX : side) :
  ([1; 0; 0; 0; 0; 0; 0] *> sL) <{{A}} ([1; 0; 0] *> sX) -->*
  sL <{{A}} (crysHead P0 *> blk7 *> sX).
Proof. apply ev_fast. unfold crysHead, blk7. execute. Qed.

Lemma crystal_bounce (ph : Phase) (c : nat) (sL : side) :
  exists c',
    sL {{fst (wallStepSpec ph)}}> crysTape ph c -->*
    sL <{{snd (wallStepSpec ph)}} crysTape (nextPhase ph) c'.
Proof.
  destruct ph; simpl wallStepSpec; simpl nextPhase; simpl fst; simpl snd.
  - exists c. unfold crysTape.
    eapply ev_trans; [apply crys_ph0_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph0_b.
  - exists c. unfold crysTape. apply crys_ph1.
  - exists c. unfold crysTape. apply crys_ph2.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph3_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph3_b.
  - exists c. unfold crysTape. apply crys_ph4.
  - exists c. unfold crysTape.
    eapply ev_trans; [apply crys_ph5_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph5_b.
  - exists c. unfold crysTape. apply crys_ph6.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph7_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph7_b.
  - exists c. unfold crysTape.
    eapply ev_trans; [apply crys_ph8_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph8_b.
  - exists c. unfold crysTape.
    eapply ev_trans; [apply crys_ph9_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph9_b.
  - exists c. unfold crysTape. apply crys_ph10.
  - exists (S c). unfold crysTape.
    change (blk7 ^^ S c) with (blk7 ++ blk7 ^^ c). rewrite Str_app_assoc.
    eapply ev_trans; [apply crys_ph11_a |].
    eapply ev_trans; [apply sweep_blk7 |].
    apply crys_ph11_b.
Qed.

(* ========================================================================== *)
(* Section 4: Stage 0 Crystal Base Simulator (simCrysWall)                    *)
(* ========================================================================== *)

Fixpoint simCrysWall (fuel : nat) (ph : Phase) (q : Q) (lb rb : list bool)
    : option (Phase * Q * list bool) :=
  match fuel with
  | O => None
  | S fuel' =>
    match lb with
    | [] => Some (ph, q, rb)
    | sym :: l' =>
      match tmStepRaw q sym with
      | None => None
      | Some (nq, w, false) => simCrysWall fuel' ph nq l' (w :: rb)
      | Some (nq, w, true) =>
        let lw := w :: l' in
        match rb with
        | nr :: r' => simCrysWall fuel' ph nq (nr :: lw) r'
        | [] =>
          let '(expIn, qOut) := wallStepSpec ph in
          if qEqb nq expIn then simCrysWall fuel' (nextPhase ph) qOut lw []
          else None
        end
      end
    end
  end.

Lemma simCrysWall_sound fuel ph q ph' q' lb rb rb' :
  simCrysWall fuel ph q lb rb = Some (ph', q', rb') ->
  forall c (sL : side), exists c',
    bitsToSide lb sL <{{q}} bitsToSide rb (crysTape ph c) -->*
    sL <{{q'}} bitsToSide rb' (crysTape ph' c').
Proof.
  revert ph q lb rb. induction fuel as [|fuel IH]; intros ph q lb rb H c sL; simpl in H.
  - discriminate.
  - destruct lb as [|sym l'].
    + inversion H; subst. exists c. apply evstep_refl.
    + destruct (tmStepRaw q sym) as [[[nq w] [|]] |] eqn:Hst; [| | discriminate].
      * destruct rb as [|nr r'].
        -- destruct (wallStepSpec ph) as [expIn qOut] eqn:Hws.
           destruct (qEqb nq expIn) eqn:Heq; [| discriminate].
           apply qEqb_eq in Heq; subst nq.
           destruct (crystal_bounce ph c (bitsToSide (w :: l') sL)) as [c1 Hcb].
           rewrite Hws in Hcb; simpl fst in Hcb; simpl snd in Hcb.
           destruct (IH _ _ _ _ H c1 sL) as [c2 Hrc].
           exists c2.
           pose proof (step_raw_hl_right _ _ _ _ (bitsToSide l' sL) (crysTape ph c) Hst) as Hs.
           simpl bitsToSide in Hs, Hcb, Hrc |- *.
           exact (ev_trans _ _ _ Hs (ev_trans _ _ _ Hcb Hrc)).
        -- destruct (IH _ _ _ _ H c sL) as [c' Hrc].
           exists c'.
           pose proof (step_raw_hl_right _ _ _ _
             (bitsToSide l' sL) (bitsToSide (nr :: r') (crysTape ph c)) Hst) as Hs.
           simpl bitsToSide in Hs, Hrc |- *.
           exact (ev_trans _ _ _ Hs Hrc).
      * destruct (IH _ _ _ _ H c sL) as [c' Hrc].
        exists c'.
        pose proof (step_raw_hl_left _ _ _ _
          (bitsToSide l' sL) (bitsToSide rb (crysTape ph c)) Hst) as Hs.
        simpl bitsToSide in Hs, Hrc |- *.
        exact (ev_trans _ _ _ Hs Hrc).
Qed.

(* ========================================================================== *)
(* Section 5: Nib/Byte Types, B8 Table, and Slice Byte-Zipper Evaluator       *)
(* ========================================================================== *)

Inductive Nib : Type :=
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | XA | XB | XC | XD | XE | XF.

Inductive Byte : Type := MkB (hi lo : Nib).

Local Notation h00 := (MkB X0 X0). Local Notation h01 := (MkB X0 X1). Local Notation h02 := (MkB X0 X2). Local Notation h03 := (MkB X0 X3).
Local Notation h04 := (MkB X0 X4). Local Notation h05 := (MkB X0 X5). Local Notation h06 := (MkB X0 X6). Local Notation h07 := (MkB X0 X7).
Local Notation h08 := (MkB X0 X8). Local Notation h09 := (MkB X0 X9). Local Notation h0a := (MkB X0 XA). Local Notation h0b := (MkB X0 XB).
Local Notation h0c := (MkB X0 XC). Local Notation h0d := (MkB X0 XD). Local Notation h0e := (MkB X0 XE). Local Notation h0f := (MkB X0 XF).
Local Notation h10 := (MkB X1 X0). Local Notation h11 := (MkB X1 X1). Local Notation h12 := (MkB X1 X2). Local Notation h13 := (MkB X1 X3).
Local Notation h14 := (MkB X1 X4). Local Notation h15 := (MkB X1 X5). Local Notation h16 := (MkB X1 X6). Local Notation h17 := (MkB X1 X7).
Local Notation h18 := (MkB X1 X8). Local Notation h19 := (MkB X1 X9). Local Notation h1a := (MkB X1 XA). Local Notation h1b := (MkB X1 XB).
Local Notation h1c := (MkB X1 XC). Local Notation h1d := (MkB X1 XD). Local Notation h1e := (MkB X1 XE). Local Notation h1f := (MkB X1 XF).
Local Notation h20 := (MkB X2 X0). Local Notation h21 := (MkB X2 X1). Local Notation h22 := (MkB X2 X2). Local Notation h23 := (MkB X2 X3).
Local Notation h24 := (MkB X2 X4). Local Notation h25 := (MkB X2 X5). Local Notation h26 := (MkB X2 X6). Local Notation h27 := (MkB X2 X7).
Local Notation h28 := (MkB X2 X8). Local Notation h29 := (MkB X2 X9). Local Notation h2a := (MkB X2 XA). Local Notation h2b := (MkB X2 XB).
Local Notation h2c := (MkB X2 XC). Local Notation h2d := (MkB X2 XD). Local Notation h2e := (MkB X2 XE). Local Notation h2f := (MkB X2 XF).
Local Notation h30 := (MkB X3 X0). Local Notation h31 := (MkB X3 X1). Local Notation h32 := (MkB X3 X2). Local Notation h33 := (MkB X3 X3).
Local Notation h34 := (MkB X3 X4). Local Notation h35 := (MkB X3 X5). Local Notation h36 := (MkB X3 X6). Local Notation h37 := (MkB X3 X7).
Local Notation h38 := (MkB X3 X8). Local Notation h39 := (MkB X3 X9). Local Notation h3a := (MkB X3 XA). Local Notation h3b := (MkB X3 XB).
Local Notation h3c := (MkB X3 XC). Local Notation h3d := (MkB X3 XD). Local Notation h3e := (MkB X3 XE). Local Notation h3f := (MkB X3 XF).
Local Notation h40 := (MkB X4 X0). Local Notation h41 := (MkB X4 X1). Local Notation h42 := (MkB X4 X2). Local Notation h43 := (MkB X4 X3).
Local Notation h44 := (MkB X4 X4). Local Notation h45 := (MkB X4 X5). Local Notation h46 := (MkB X4 X6). Local Notation h47 := (MkB X4 X7).
Local Notation h48 := (MkB X4 X8). Local Notation h49 := (MkB X4 X9). Local Notation h4a := (MkB X4 XA). Local Notation h4b := (MkB X4 XB).
Local Notation h4c := (MkB X4 XC). Local Notation h4d := (MkB X4 XD). Local Notation h4e := (MkB X4 XE). Local Notation h4f := (MkB X4 XF).
Local Notation h50 := (MkB X5 X0). Local Notation h51 := (MkB X5 X1). Local Notation h52 := (MkB X5 X2). Local Notation h53 := (MkB X5 X3).
Local Notation h54 := (MkB X5 X4). Local Notation h55 := (MkB X5 X5). Local Notation h56 := (MkB X5 X6). Local Notation h57 := (MkB X5 X7).
Local Notation h58 := (MkB X5 X8). Local Notation h59 := (MkB X5 X9). Local Notation h5a := (MkB X5 XA). Local Notation h5b := (MkB X5 XB).
Local Notation h5c := (MkB X5 XC). Local Notation h5d := (MkB X5 XD). Local Notation h5e := (MkB X5 XE). Local Notation h5f := (MkB X5 XF).
Local Notation h60 := (MkB X6 X0). Local Notation h61 := (MkB X6 X1). Local Notation h62 := (MkB X6 X2). Local Notation h63 := (MkB X6 X3).
Local Notation h64 := (MkB X6 X4). Local Notation h65 := (MkB X6 X5). Local Notation h66 := (MkB X6 X6). Local Notation h67 := (MkB X6 X7).
Local Notation h68 := (MkB X6 X8). Local Notation h69 := (MkB X6 X9). Local Notation h6a := (MkB X6 XA). Local Notation h6b := (MkB X6 XB).
Local Notation h6c := (MkB X6 XC). Local Notation h6d := (MkB X6 XD). Local Notation h6e := (MkB X6 XE). Local Notation h6f := (MkB X6 XF).
Local Notation h70 := (MkB X7 X0). Local Notation h71 := (MkB X7 X1). Local Notation h72 := (MkB X7 X2). Local Notation h73 := (MkB X7 X3).
Local Notation h74 := (MkB X7 X4). Local Notation h75 := (MkB X7 X5). Local Notation h76 := (MkB X7 X6). Local Notation h77 := (MkB X7 X7).
Local Notation h78 := (MkB X7 X8). Local Notation h79 := (MkB X7 X9). Local Notation h7a := (MkB X7 XA). Local Notation h7b := (MkB X7 XB).
Local Notation h7c := (MkB X7 XC). Local Notation h7d := (MkB X7 XD). Local Notation h7e := (MkB X7 XE). Local Notation h7f := (MkB X7 XF).
Local Notation h80 := (MkB X8 X0). Local Notation h81 := (MkB X8 X1). Local Notation h82 := (MkB X8 X2). Local Notation h83 := (MkB X8 X3).
Local Notation h84 := (MkB X8 X4). Local Notation h85 := (MkB X8 X5). Local Notation h86 := (MkB X8 X6). Local Notation h87 := (MkB X8 X7).
Local Notation h88 := (MkB X8 X8). Local Notation h89 := (MkB X8 X9). Local Notation h8a := (MkB X8 XA). Local Notation h8b := (MkB X8 XB).
Local Notation h8c := (MkB X8 XC). Local Notation h8d := (MkB X8 XD). Local Notation h8e := (MkB X8 XE). Local Notation h8f := (MkB X8 XF).
Local Notation h90 := (MkB X9 X0). Local Notation h91 := (MkB X9 X1). Local Notation h92 := (MkB X9 X2). Local Notation h93 := (MkB X9 X3).
Local Notation h94 := (MkB X9 X4). Local Notation h95 := (MkB X9 X5). Local Notation h96 := (MkB X9 X6). Local Notation h97 := (MkB X9 X7).
Local Notation h98 := (MkB X9 X8). Local Notation h99 := (MkB X9 X9). Local Notation h9a := (MkB X9 XA). Local Notation h9b := (MkB X9 XB).
Local Notation h9c := (MkB X9 XC). Local Notation h9d := (MkB X9 XD). Local Notation h9e := (MkB X9 XE). Local Notation h9f := (MkB X9 XF).
Local Notation ha0 := (MkB XA X0). Local Notation ha1 := (MkB XA X1). Local Notation ha2 := (MkB XA X2). Local Notation ha3 := (MkB XA X3).
Local Notation ha4 := (MkB XA X4). Local Notation ha5 := (MkB XA X5). Local Notation ha6 := (MkB XA X6). Local Notation ha7 := (MkB XA X7).
Local Notation ha8 := (MkB XA X8). Local Notation ha9 := (MkB XA X9). Local Notation haa := (MkB XA XA). Local Notation hab := (MkB XA XB).
Local Notation hac := (MkB XA XC). Local Notation had := (MkB XA XD). Local Notation hae := (MkB XA XE). Local Notation haf := (MkB XA XF).
Local Notation hb0 := (MkB XB X0). Local Notation hb1 := (MkB XB X1). Local Notation hb2 := (MkB XB X2). Local Notation hb3 := (MkB XB X3).
Local Notation hb4 := (MkB XB X4). Local Notation hb5 := (MkB XB X5). Local Notation hb6 := (MkB XB X6). Local Notation hb7 := (MkB XB X7).
Local Notation hb8 := (MkB XB X8). Local Notation hb9 := (MkB XB X9). Local Notation hba := (MkB XB XA). Local Notation hbb := (MkB XB XB).
Local Notation hbc := (MkB XB XC). Local Notation hbd := (MkB XB XD). Local Notation hbe := (MkB XB XE). Local Notation hbf := (MkB XB XF).
Local Notation hc0 := (MkB XC X0). Local Notation hc1 := (MkB XC X1). Local Notation hc2 := (MkB XC X2). Local Notation hc3 := (MkB XC X3).
Local Notation hc4 := (MkB XC X4). Local Notation hc5 := (MkB XC X5). Local Notation hc6 := (MkB XC X6). Local Notation hc7 := (MkB XC X7).
Local Notation hc8 := (MkB XC X8). Local Notation hc9 := (MkB XC X9). Local Notation hca := (MkB XC XA). Local Notation hcb := (MkB XC XB).
Local Notation hcc := (MkB XC XC). Local Notation hcd := (MkB XC XD). Local Notation hce := (MkB XC XE). Local Notation hcf := (MkB XC XF).
Local Notation hd0 := (MkB XD X0). Local Notation hd1 := (MkB XD X1). Local Notation hd2 := (MkB XD X2). Local Notation hd3 := (MkB XD X3).
Local Notation hd4 := (MkB XD X4). Local Notation hd5 := (MkB XD X5). Local Notation hd6 := (MkB XD X6). Local Notation hd7 := (MkB XD X7).
Local Notation hd8 := (MkB XD X8). Local Notation hd9 := (MkB XD X9). Local Notation hda := (MkB XD XA). Local Notation hdb := (MkB XD XB).
Local Notation hdc := (MkB XD XC). Local Notation hdd := (MkB XD XD). Local Notation hde := (MkB XD XE). Local Notation hdf := (MkB XD XF).
Local Notation he0 := (MkB XE X0). Local Notation he1 := (MkB XE X1). Local Notation he2 := (MkB XE X2). Local Notation he3 := (MkB XE X3).
Local Notation he4 := (MkB XE X4). Local Notation he5 := (MkB XE X5). Local Notation he6 := (MkB XE X6). Local Notation he7 := (MkB XE X7).
Local Notation he8 := (MkB XE X8). Local Notation he9 := (MkB XE X9). Local Notation hea := (MkB XE XA). Local Notation heb := (MkB XE XB).
Local Notation hec := (MkB XE XC). Local Notation hed := (MkB XE XD). Local Notation hee := (MkB XE XE). Local Notation hef := (MkB XE XF).
Local Notation hf0 := (MkB XF X0). Local Notation hf1 := (MkB XF X1). Local Notation hf2 := (MkB XF X2). Local Notation hf3 := (MkB XF X3).
Local Notation hf4 := (MkB XF X4). Local Notation hf5 := (MkB XF X5). Local Notation hf6 := (MkB XF X6). Local Notation hf7 := (MkB XF X7).
Local Notation hf8 := (MkB XF X8). Local Notation hf9 := (MkB XF X9). Local Notation hfa := (MkB XF XA). Local Notation hfb := (MkB XF XB).
Local Notation hfc := (MkB XF XC). Local Notation hfd := (MkB XF XD). Local Notation hfe := (MkB XF XE). Local Notation hff := (MkB XF XF).

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

Fixpoint sliceEqb (xs ys : list Byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => byteEqb x y && sliceEqb xs' ys'
  | _, _ => false
  end.

Lemma sliceEqb_eq xs ys : sliceEqb xs ys = true -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; try discriminate.
  - reflexivity.
  - intros H. apply andb_prop in H as [H1 H2].
    f_equal; [exact (byteEqb_eq _ _ H1) | exact (IH ys H2)].
Qed.

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
  | B8Wall (qOut : Q) (outB : Byte)
  | B8Tail (qOut : Q) (outB : Byte)
  | B8Halt
  | B8Fail.

Definition b8OutEqb (x y : B8Out) : bool :=
  match x, y with
  | B8Wall q1 b1, B8Wall q2 b2 => qEqb q1 q2 && byteEqb b1 b2
  | B8Tail q1 b1, B8Tail q2 b2 => qEqb q1 q2 && byteEqb b1 b2
  | B8Halt, B8Halt => true
  | B8Fail, B8Fail => true
  | _, _ => false
  end.

Lemma b8OutEqb_eq x y : b8OutEqb x y = true -> x = y.
Proof.
  destruct x, y; simpl; try discriminate; try reflexivity;
    intros H; apply andb_prop in H as [Hq Hb];
    f_equal; try exact (qEqb_eq _ _ Hq); exact (byteEqb_eq _ _ Hb).
Qed.

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

Definition b8Tab_0_0 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall B h01) (B8Wall F h90) (B8Wall B h03) (B8Wall F h48) (B8Wall B h05) (B8Wall F h00) (B8Wall B h07) B8Halt (B8Wall B h09) (B8Wall F h48) (B8Wall B h0b) (B8Tail B h7d) (B8Wall B h0d) (B8Wall F h08) (B8Wall B h0f) B8Halt)
    (N16 (B8Wall B h11) (B8Tail A hbb) (B8Wall B h13) (B8Tail C hbf) (B8Wall B h15) (B8Wall F h10) (B8Wall B h17) B8Halt (B8Wall B h19) (B8Tail C hbf) (B8Wall B h1b) (B8Tail C hbd) (B8Wall B h1d) (B8Wall F h18) (B8Wall B h1f) B8Halt)
    (N16 (B8Wall B h21) (B8Tail B h7f) (B8Wall B h23) (B8Tail A h97) (B8Wall B h25) (B8Wall F h20) (B8Wall B h27) B8Halt (B8Wall B h29) (B8Tail A h97) (B8Wall B h2b) (B8Wall F h90) (B8Wall B h2d) (B8Wall F h28) (B8Wall B h2f) B8Halt)
    (N16 (B8Wall B h31) (B8Tail B h7b) (B8Wall B h33) (B8Tail A h9f) (B8Wall B h35) (B8Wall F h30) (B8Wall B h37) B8Halt (B8Wall B h39) (B8Tail A h9f) (B8Wall B h3b) B8Halt (B8Wall B h3d) (B8Wall F h38) (B8Wall B h3f) B8Halt)
    (N16 (B8Wall B h41) (B8Tail C haf) (B8Wall B h43) (B8Tail B he7) (B8Wall B h45) (B8Wall F h40) (B8Wall B h47) B8Halt (B8Wall B h49) (B8Tail B he7) (B8Wall B h4b) (B8Tail C hbd) (B8Wall B h4d) (B8Wall F h48) (B8Wall B h4f) B8Halt)
    (N16 (B8Wall B h51) (B8Tail A h9f) (B8Wall B h53) (B8Tail B hef) (B8Wall B h55) (B8Wall F h50) (B8Wall B h57) B8Halt (B8Wall B h59) (B8Tail B hef) (B8Wall B h5b) (B8Tail B hed) (B8Wall B h5d) (B8Wall F h58) (B8Wall B h5f) B8Halt)
    (N16 (B8Wall B h61) (B8Tail C hbf) (B8Wall B h63) (B8Tail A hb7) (B8Wall B h65) (B8Wall F h60) (B8Wall B h67) B8Halt (B8Wall B h69) (B8Tail A hb7) (B8Wall B h6b) (B8Tail C haf) (B8Wall B h6d) (B8Wall F h68) (B8Wall B h6f) B8Halt)
    (N16 (B8Wall B h71) B8Halt (B8Wall B h73) (B8Tail A hbf) (B8Wall B h75) (B8Wall F h70) (B8Wall B h77) B8Halt (B8Wall B h79) (B8Tail A hbf) (B8Wall B h7b) B8Halt (B8Wall B h7d) (B8Wall F h78) (B8Wall B h7f) B8Halt)
    (N16 (B8Wall B h81) (B8Tail D hcf) (B8Wall B h83) (B8Wall F hc8) (B8Wall B h85) (B8Wall F h80) (B8Wall B h87) B8Halt (B8Wall B h89) (B8Wall F hc8) (B8Wall B h8b) (B8Tail D hdd) (B8Wall B h8d) (B8Wall F h88) (B8Wall B h8f) B8Halt)
    (N16 (B8Wall B h91) (B8Tail B h7b) (B8Wall B h93) (B8Tail C hff) (B8Wall B h95) (B8Wall F h90) (B8Wall B h97) B8Halt (B8Wall B h99) (B8Tail C hff) (B8Wall B h9b) (B8Tail C hfd) (B8Wall B h9d) (B8Wall F h98) (B8Wall B h9f) B8Halt)
    (N16 (B8Wall B ha1) (B8Tail D hdf) (B8Wall B ha3) (B8Tail B h57) (B8Wall B ha5) (B8Wall F ha0) (B8Wall B ha7) B8Halt (B8Wall B ha9) (B8Tail B h57) (B8Wall B hab) (B8Tail D hcf) (B8Wall B had) (B8Wall F ha8) (B8Wall B haf) B8Halt)
    (N16 (B8Wall B hb1) (B8Tail D hdb) (B8Wall B hb3) (B8Tail B h5f) (B8Wall B hb5) (B8Wall F hb0) (B8Wall B hb7) B8Halt (B8Wall B hb9) (B8Tail B h5f) (B8Wall B hbb) B8Halt (B8Wall B hbd) (B8Wall F hb8) (B8Wall B hbf) B8Halt)
    (N16 (B8Wall B hc1) (B8Tail C hef) (B8Wall B hc3) (B8Tail E h67) (B8Wall B hc5) (B8Wall F hc0) (B8Wall B hc7) B8Halt (B8Wall B hc9) (B8Tail E h67) (B8Wall B hcb) (B8Tail C hfd) (B8Wall B hcd) (B8Wall F hc8) (B8Wall B hcf) B8Halt)
    (N16 (B8Wall B hd1) (B8Tail B h5f) (B8Wall B hd3) (B8Tail E h6f) (B8Wall B hd5) (B8Wall F hd0) (B8Wall B hd7) B8Halt (B8Wall B hd9) (B8Tail E h6f) (B8Wall B hdb) (B8Tail E h6d) (B8Wall B hdd) (B8Wall F hd8) (B8Wall B hdf) B8Halt)
    (N16 (B8Wall B he1) (B8Tail C hff) (B8Wall B he3) (B8Tail B h77) (B8Wall B he5) (B8Wall F he0) (B8Wall B he7) B8Halt (B8Wall B he9) (B8Tail B h77) (B8Wall B heb) (B8Tail C hef) (B8Wall B hed) (B8Wall F he8) (B8Wall B hef) B8Halt)
    (N16 (B8Wall B hf1) B8Halt (B8Wall B hf3) (B8Tail B h7f) (B8Wall B hf5) (B8Wall F hf0) (B8Wall B hf7) B8Halt (B8Wall B hf9) (B8Tail B h7f) (B8Wall B hfb) B8Halt (B8Wall B hfd) (B8Wall F hf8) (B8Wall B hff) B8Halt).
Definition b8Tab_0_1 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall A h04) (B8Wall F h00) (B8Wall F h12) (B8Wall F h02) (B8Tail C hbe) (B8Wall F h04) (B8Wall F h90) (B8Wall F h06) (B8Wall A h0c) (B8Wall F h08) (B8Tail B he7) (B8Wall F h0a) (B8Tail A h9e) (B8Wall F h0c) (B8Wall F h48) (B8Wall F h0e))
    (N16 (B8Wall A h14) (B8Wall F h10) (B8Tail A hb9) (B8Wall F h12) (B8Wall A h00) (B8Wall F h14) (B8Tail A hbb) (B8Wall F h16) (B8Wall A h1c) (B8Wall F h18) (B8Tail C hbd) (B8Wall F h1a) B8Halt (B8Wall F h1c) (B8Tail C hbf) (B8Wall F h1e))
    (N16 (B8Wall A h24) (B8Wall F h20) (B8Wall F h32) (B8Wall F h22) (B8Tail A h9e) (B8Wall F h24) (B8Tail B h7f) (B8Wall F h26) (B8Wall A h2c) (B8Wall F h28) (B8Tail A h95) (B8Wall F h2a) (B8Tail C hf6) (B8Wall F h2c) (B8Tail A h97) (B8Wall F h2e))
    (N16 (B8Wall A h34) (B8Wall F h30) (B8Tail B h79) (B8Wall F h32) (B8Wall A h20) (B8Wall F h34) (B8Tail B h7b) (B8Wall F h36) (B8Wall A h3c) (B8Wall F h38) (B8Tail A h9d) (B8Wall F h3a) B8Halt (B8Wall F h3c) (B8Tail A h9f) (B8Wall F h3e))
    (N16 (B8Wall A h44) (B8Wall F h40) (B8Wall F h52) (B8Wall F h42) (B8Tail B hee) (B8Wall F h44) (B8Tail C haf) (B8Wall F h46) (B8Wall A h4c) (B8Wall F h48) (B8Tail B he5) (B8Wall F h4a) (B8Tail A hbe) (B8Wall F h4c) (B8Tail B he7) (B8Wall F h4e))
    (N16 (B8Wall A h54) (B8Wall F h50) (B8Wall F h02) (B8Wall F h52) (B8Wall A h40) (B8Wall F h54) (B8Tail A h9f) (B8Wall F h56) (B8Wall A h5c) (B8Wall F h58) (B8Tail B hed) (B8Wall F h5a) B8Halt (B8Wall F h5c) (B8Tail B hef) (B8Wall F h5e))
    (N16 (B8Wall A h64) (B8Wall F h60) (B8Wall F h72) (B8Wall F h62) (B8Tail A hbe) (B8Wall F h64) (B8Tail C hbf) (B8Wall F h66) (B8Wall A h6c) (B8Wall F h68) (B8Tail A hb5) (B8Wall F h6a) (B8Tail A hb6) (B8Wall F h6c) (B8Tail A hb7) (B8Wall F h6e))
    (N16 (B8Wall A h74) (B8Wall F h70) B8Halt (B8Wall F h72) (B8Wall A h60) (B8Wall F h74) B8Halt (B8Wall F h76) (B8Wall A h7c) (B8Wall F h78) (B8Tail A hbd) (B8Wall F h7a) B8Halt (B8Wall F h7c) (B8Tail A hbf) (B8Wall F h7e))
    (N16 (B8Wall A h84) (B8Wall F h80) (B8Wall F h92) (B8Wall F h82) (B8Tail C hfe) (B8Wall F h84) (B8Tail D hcf) (B8Wall F h86) (B8Wall A h8c) (B8Wall F h88) (B8Tail E h67) (B8Wall F h8a) (B8Tail B h5e) (B8Wall F h8c) (B8Wall F hc8) (B8Wall F h8e))
    (N16 (B8Wall A h94) (B8Wall F h90) (B8Tail B h79) (B8Wall F h92) (B8Wall A h80) (B8Wall F h94) (B8Tail B h7b) (B8Wall F h96) (B8Wall A h9c) (B8Wall F h98) (B8Tail C hfd) (B8Wall F h9a) B8Halt (B8Wall F h9c) (B8Tail C hff) (B8Wall F h9e))
    (N16 (B8Wall A ha4) (B8Wall F ha0) (B8Wall F hb2) (B8Wall F ha2) (B8Tail B h5e) (B8Wall F ha4) (B8Tail D hdf) (B8Wall F ha6) (B8Wall A hac) (B8Wall F ha8) (B8Tail B h55) (B8Wall F haa) (B8Tail C hbe) (B8Wall F hac) (B8Tail B h57) (B8Wall F hae))
    (N16 (B8Wall A hb4) (B8Wall F hb0) (B8Tail D hd9) (B8Wall F hb2) (B8Wall A ha0) (B8Wall F hb4) (B8Tail D hdb) (B8Wall F hb6) (B8Wall A hbc) (B8Wall F hb8) (B8Tail B h5d) (B8Wall F hba) B8Halt (B8Wall F hbc) (B8Tail B h5f) (B8Wall F hbe))
    (N16 (B8Wall A hc4) (B8Wall F hc0) (B8Wall F hd2) (B8Wall F hc2) (B8Tail E h6e) (B8Wall F hc4) (B8Tail C hef) (B8Wall F hc6) (B8Wall A hcc) (B8Wall F hc8) (B8Tail E h65) (B8Wall F hca) (B8Tail B h7e) (B8Wall F hcc) (B8Tail E h67) (B8Wall F hce))
    (N16 (B8Wall A hd4) (B8Wall F hd0) (B8Wall F h82) (B8Wall F hd2) (B8Wall A hc0) (B8Wall F hd4) (B8Tail B h5f) (B8Wall F hd6) (B8Wall A hdc) (B8Wall F hd8) (B8Tail E h6d) (B8Wall F hda) B8Halt (B8Wall F hdc) (B8Tail E h6f) (B8Wall F hde))
    (N16 (B8Wall A he4) (B8Wall F he0) (B8Wall F hf2) (B8Wall F he2) (B8Tail B h7e) (B8Wall F he4) (B8Tail C hff) (B8Wall F he6) (B8Wall A hec) (B8Wall F he8) (B8Tail B h75) (B8Wall F hea) B8Halt (B8Wall F hec) (B8Tail B h77) (B8Wall F hee))
    (N16 (B8Wall A hf4) (B8Wall F hf0) B8Halt (B8Wall F hf2) (B8Wall A he0) (B8Wall F hf4) B8Halt (B8Wall F hf6) (B8Wall A hfc) (B8Wall F hf8) (B8Tail B h7d) (B8Wall F hfa) B8Halt (B8Wall F hfc) (B8Tail B h7f) (B8Wall F hfe)).
Definition b8Tab_0_2 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall D h00) (B8Wall B h09) (B8Wall D h02) (B8Wall A h00) (B8Wall D h04) (B8Wall A h24) (B8Wall D h06) (B8Wall A h04) (B8Wall D h08) (B8Tail B h7c) (B8Wall D h0a) (B8Wall A h08) (B8Wall D h0c) (B8Tail A h9e) (B8Wall D h0e) (B8Wall A h0c))
    (N16 (B8Wall D h10) (B8Wall B h19) (B8Wall D h12) (B8Wall A h10) (B8Wall D h14) (B8Tail D hce) (B8Wall D h16) (B8Wall A h14) (B8Wall D h18) (B8Tail C hbc) (B8Wall D h1a) (B8Wall A h18) (B8Wall D h1c) (B8Wall A h90) (B8Wall D h1e) (B8Wall A h1c))
    (N16 (B8Wall D h20) (B8Wall B h29) (B8Wall D h22) (B8Wall A h20) (B8Wall D h24) (B8Tail C hf2) (B8Wall D h26) (B8Wall A h24) (B8Wall D h28) (B8Wall B h01) (B8Wall D h2a) (B8Wall A h28) (B8Wall D h2c) (B8Tail C hf6) (B8Wall D h2e) (B8Wall A h2c))
    (N16 (B8Wall D h30) (B8Wall B h39) (B8Wall D h32) (B8Wall A h30) (B8Wall D h34) (B8Tail B h7a) (B8Wall D h36) (B8Wall A h34) (B8Wall D h38) B8Halt (B8Wall D h3a) (B8Wall A h38) (B8Wall D h3c) (B8Tail B h7e) (B8Wall D h3e) (B8Wall A h3c))
    (N16 (B8Wall D h40) (B8Wall B h49) (B8Wall D h42) (B8Wall A h40) (B8Wall D h44) (B8Wall A h64) (B8Wall D h46) (B8Wall A h44) (B8Wall D h48) (B8Tail C hbc) (B8Wall D h4a) (B8Wall A h48) (B8Wall D h4c) (B8Tail A hbe) (B8Wall D h4e) (B8Wall A h4c))
    (N16 (B8Wall D h50) (B8Wall B h59) (B8Wall D h52) (B8Wall A h50) (B8Wall D h54) (B8Tail C haa) (B8Wall D h56) (B8Wall A h54) (B8Wall D h58) (B8Tail B hec) (B8Wall D h5a) (B8Wall A h58) (B8Wall D h5c) (B8Tail C hae) (B8Wall D h5e) (B8Wall A h5c))
    (N16 (B8Wall D h60) (B8Wall B h69) (B8Wall D h62) (B8Wall A h60) (B8Wall D h64) (B8Tail A hb2) (B8Wall D h66) (B8Wall A h64) (B8Wall D h68) (B8Wall B h41) (B8Wall D h6a) (B8Wall A h68) (B8Wall D h6c) (B8Tail A hb6) (B8Wall D h6e) (B8Wall A h6c))
    (N16 (B8Wall D h70) (B8Wall B h79) (B8Wall D h72) (B8Wall A h70) (B8Wall D h74) (B8Tail C hba) (B8Wall D h76) (B8Wall A h74) (B8Wall D h78) B8Halt (B8Wall D h7a) (B8Wall A h78) (B8Wall D h7c) (B8Tail C hbe) (B8Wall D h7e) (B8Wall A h7c))
    (N16 (B8Wall D h80) (B8Wall B h89) (B8Wall D h82) (B8Wall A h80) (B8Wall D h84) (B8Wall A ha4) (B8Wall D h86) (B8Wall A h84) (B8Wall D h88) (B8Tail D hdc) (B8Wall D h8a) (B8Wall A h88) (B8Wall D h8c) (B8Tail B h5e) (B8Wall D h8e) (B8Wall A h8c))
    (N16 (B8Wall D h90) (B8Wall B h99) (B8Wall D h92) (B8Wall A h90) (B8Wall D h94) (B8Tail D hca) (B8Wall D h96) (B8Wall A h94) (B8Wall D h98) (B8Tail C hfc) (B8Wall D h9a) (B8Wall A h98) (B8Wall D h9c) (B8Tail D hce) (B8Wall D h9e) (B8Wall A h9c))
    (N16 (B8Wall D ha0) (B8Wall B ha9) (B8Wall D ha2) (B8Wall A ha0) (B8Wall D ha4) (B8Wall A h04) (B8Wall D ha6) (B8Wall A ha4) (B8Wall D ha8) (B8Wall B h81) (B8Wall D haa) (B8Wall A ha8) (B8Wall D hac) (B8Tail C hbe) (B8Wall D hae) (B8Wall A hac))
    (N16 (B8Wall D hb0) (B8Wall B hb9) (B8Wall D hb2) (B8Wall A hb0) (B8Wall D hb4) (B8Tail D hda) (B8Wall D hb6) (B8Wall A hb4) (B8Wall D hb8) B8Halt (B8Wall D hba) (B8Wall A hb8) (B8Wall D hbc) (B8Tail D hde) (B8Wall D hbe) (B8Wall A hbc))
    (N16 (B8Wall D hc0) (B8Wall B hc9) (B8Wall D hc2) (B8Wall A hc0) (B8Wall D hc4) (B8Wall A he4) (B8Wall D hc6) (B8Wall A hc4) (B8Wall D hc8) (B8Tail C hfc) (B8Wall D hca) (B8Wall A hc8) (B8Wall D hcc) (B8Tail B h7e) (B8Wall D hce) (B8Wall A hcc))
    (N16 (B8Wall D hd0) (B8Wall B hd9) (B8Wall D hd2) (B8Wall A hd0) (B8Wall D hd4) (B8Tail C hea) (B8Wall D hd6) (B8Wall A hd4) (B8Wall D hd8) (B8Tail E h6c) (B8Wall D hda) (B8Wall A hd8) (B8Wall D hdc) (B8Tail C hee) (B8Wall D hde) (B8Wall A hdc))
    (N16 (B8Wall D he0) (B8Wall B he9) (B8Wall D he2) (B8Wall A he0) (B8Wall D he4) B8Halt (B8Wall D he6) (B8Wall A he4) (B8Wall D he8) (B8Wall B hc1) (B8Wall D hea) (B8Wall A he8) (B8Wall D hec) B8Halt (B8Wall D hee) (B8Wall A hec))
    (N16 (B8Wall D hf0) (B8Wall B hf9) (B8Wall D hf2) (B8Wall A hf0) (B8Wall D hf4) (B8Tail C hfa) (B8Wall D hf6) (B8Wall A hf4) (B8Wall D hf8) B8Halt (B8Wall D hfa) (B8Wall A hf8) (B8Wall D hfc) (B8Tail C hfe) (B8Wall D hfe) (B8Wall A hfc)).
Definition b8Tab_0_3 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall F h48) (B8Wall A h04) (B8Wall F h00) B8Halt (B8Wall F h24) (B8Tail C hbe) (B8Wall F h04) B8Halt (B8Tail B h7d) (B8Wall A h0c) (B8Wall F h08) B8Halt (B8Tail A h9f) (B8Tail A h9e) (B8Wall F h0c) B8Halt)
    (N16 (B8Tail C hbf) (B8Wall A h14) (B8Wall F h10) B8Halt (B8Tail D hcf) (B8Wall A h00) (B8Wall F h14) B8Halt (B8Tail C hbd) (B8Wall A h1c) (B8Wall F h18) B8Halt (B8Wall F h90) B8Halt (B8Wall F h1c) B8Halt)
    (N16 (B8Tail A h97) (B8Wall A h24) (B8Wall F h20) B8Halt (B8Tail C hf3) (B8Tail A h9e) (B8Wall F h24) B8Halt (B8Wall F h90) (B8Wall A h2c) (B8Wall F h28) B8Halt (B8Tail C hf7) (B8Tail C hf6) (B8Wall F h2c) B8Halt)
    (N16 (B8Tail A h9f) (B8Wall A h34) (B8Wall F h30) B8Halt (B8Tail B h7b) (B8Wall A h20) (B8Wall F h34) B8Halt B8Halt (B8Wall A h3c) (B8Wall F h38) B8Halt (B8Tail B h7f) B8Halt (B8Wall F h3c) B8Halt)
    (N16 (B8Tail B he7) (B8Wall A h44) (B8Wall F h40) B8Halt (B8Wall F h64) (B8Tail B hee) (B8Wall F h44) B8Halt (B8Tail C hbd) (B8Wall A h4c) (B8Wall F h48) B8Halt (B8Tail A hbf) (B8Tail A hbe) (B8Wall F h4c) B8Halt)
    (N16 (B8Tail B hef) (B8Wall A h54) (B8Wall F h50) B8Halt (B8Tail C hab) (B8Wall A h40) (B8Wall F h54) B8Halt (B8Tail B hed) (B8Wall A h5c) (B8Wall F h58) B8Halt (B8Tail C haf) B8Halt (B8Wall F h5c) B8Halt)
    (N16 (B8Tail A hb7) (B8Wall A h64) (B8Wall F h60) B8Halt (B8Tail A hb3) (B8Tail A hbe) (B8Wall F h64) B8Halt (B8Tail C haf) (B8Wall A h6c) (B8Wall F h68) B8Halt (B8Tail A hb7) (B8Tail A hb6) (B8Wall F h6c) B8Halt)
    (N16 (B8Tail A hbf) (B8Wall A h74) (B8Wall F h70) B8Halt (B8Tail C hbb) (B8Wall A h60) (B8Wall F h74) B8Halt B8Halt (B8Wall A h7c) (B8Wall F h78) B8Halt (B8Tail C hbf) B8Halt (B8Wall F h7c) B8Halt)
    (N16 (B8Wall F hc8) (B8Wall A h84) (B8Wall F h80) B8Halt (B8Wall F ha4) (B8Tail C hfe) (B8Wall F h84) B8Halt (B8Tail D hdd) (B8Wall A h8c) (B8Wall F h88) B8Halt (B8Tail B h5f) (B8Tail B h5e) (B8Wall F h8c) B8Halt)
    (N16 (B8Tail C hff) (B8Wall A h94) (B8Wall F h90) B8Halt (B8Tail D hcb) (B8Wall A h80) (B8Wall F h94) B8Halt (B8Tail C hfd) (B8Wall A h9c) (B8Wall F h98) B8Halt (B8Tail D hcf) B8Halt (B8Wall F h9c) B8Halt)
    (N16 (B8Tail B h57) (B8Wall A ha4) (B8Wall F ha0) B8Halt (B8Wall F h04) (B8Tail B h5e) (B8Wall F ha4) B8Halt (B8Tail D hcf) (B8Wall A hac) (B8Wall F ha8) B8Halt (B8Tail C hbf) (B8Tail C hbe) (B8Wall F hac) B8Halt)
    (N16 (B8Tail B h5f) (B8Wall A hb4) (B8Wall F hb0) B8Halt (B8Tail D hdb) (B8Wall A ha0) (B8Wall F hb4) B8Halt B8Halt (B8Wall A hbc) (B8Wall F hb8) B8Halt (B8Tail D hdf) B8Halt (B8Wall F hbc) B8Halt)
    (N16 (B8Tail E h67) (B8Wall A hc4) (B8Wall F hc0) B8Halt (B8Wall F he4) (B8Tail E h6e) (B8Wall F hc4) B8Halt (B8Tail C hfd) (B8Wall A hcc) (B8Wall F hc8) B8Halt (B8Tail B h7f) (B8Tail B h7e) (B8Wall F hcc) B8Halt)
    (N16 (B8Tail E h6f) (B8Wall A hd4) (B8Wall F hd0) B8Halt (B8Tail C heb) (B8Wall A hc0) (B8Wall F hd4) B8Halt (B8Tail E h6d) (B8Wall A hdc) (B8Wall F hd8) B8Halt (B8Tail C hef) B8Halt (B8Wall F hdc) B8Halt)
    (N16 (B8Tail B h77) (B8Wall A he4) (B8Wall F he0) B8Halt B8Halt (B8Tail B h7e) (B8Wall F he4) B8Halt (B8Tail C hef) (B8Wall A hec) (B8Wall F he8) B8Halt B8Halt B8Halt (B8Wall F hec) B8Halt)
    (N16 (B8Tail B h7f) (B8Wall A hf4) (B8Wall F hf0) B8Halt (B8Tail C hfb) (B8Wall A he0) (B8Wall F hf4) B8Halt B8Halt (B8Wall A hfc) (B8Wall F hf8) B8Halt (B8Tail C hff) B8Halt (B8Wall F hfc) B8Halt).
Definition b8Tab_0_4 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall F h02) B8Halt (B8Tail A h9f) B8Halt (B8Wall F h06) B8Halt (B8Wall F h90) B8Halt (B8Wall F h0a) B8Halt (B8Wall F h00) B8Halt (B8Wall F h0e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h12) B8Halt (B8Wall F h90) B8Halt (B8Wall F h16) B8Halt (B8Tail A hbb) B8Halt (B8Wall F h1a) B8Halt (B8Wall F h10) B8Halt (B8Wall F h1e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h22) B8Halt (B8Tail C hf7) B8Halt (B8Wall F h26) B8Halt (B8Tail B h7f) B8Halt (B8Wall F h2a) B8Halt (B8Wall F h20) B8Halt (B8Wall F h2e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h32) B8Halt (B8Tail B h7f) B8Halt (B8Wall F h36) B8Halt (B8Tail B h7b) B8Halt (B8Wall F h3a) B8Halt (B8Wall F h30) B8Halt (B8Wall F h3e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h42) B8Halt (B8Tail A hbf) B8Halt (B8Wall F h46) B8Halt (B8Tail C haf) B8Halt (B8Wall F h4a) B8Halt (B8Wall F h40) B8Halt (B8Wall F h4e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h52) B8Halt (B8Tail C haf) B8Halt (B8Wall F h56) B8Halt (B8Tail A h9f) B8Halt (B8Wall F h5a) B8Halt (B8Wall F h50) B8Halt (B8Wall F h5e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h62) B8Halt (B8Tail A hb7) B8Halt (B8Wall F h66) B8Halt (B8Tail C hbf) B8Halt (B8Wall F h6a) B8Halt (B8Wall F h60) B8Halt (B8Wall F h6e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h72) B8Halt (B8Tail C hbf) B8Halt (B8Wall F h76) B8Halt B8Halt B8Halt (B8Wall F h7a) B8Halt (B8Wall F h70) B8Halt (B8Wall F h7e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h82) B8Halt (B8Tail B h5f) B8Halt (B8Wall F h86) B8Halt (B8Tail D hcf) B8Halt (B8Wall F h8a) B8Halt (B8Wall F h80) B8Halt (B8Wall F h8e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F h92) B8Halt (B8Tail D hcf) B8Halt (B8Wall F h96) B8Halt (B8Tail B h7b) B8Halt (B8Wall F h9a) B8Halt (B8Wall F h90) B8Halt (B8Wall F h9e) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F ha2) B8Halt (B8Tail C hbf) B8Halt (B8Wall F ha6) B8Halt (B8Tail D hdf) B8Halt (B8Wall F haa) B8Halt (B8Wall F ha0) B8Halt (B8Wall F hae) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F hb2) B8Halt (B8Tail D hdf) B8Halt (B8Wall F hb6) B8Halt (B8Tail D hdb) B8Halt (B8Wall F hba) B8Halt (B8Wall F hb0) B8Halt (B8Wall F hbe) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F hc2) B8Halt (B8Tail B h7f) B8Halt (B8Wall F hc6) B8Halt (B8Tail C hef) B8Halt (B8Wall F hca) B8Halt (B8Wall F hc0) B8Halt (B8Wall F hce) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F hd2) B8Halt (B8Tail C hef) B8Halt (B8Wall F hd6) B8Halt (B8Tail B h5f) B8Halt (B8Wall F hda) B8Halt (B8Wall F hd0) B8Halt (B8Wall F hde) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F he2) B8Halt B8Halt B8Halt (B8Wall F he6) B8Halt (B8Tail C hff) B8Halt (B8Wall F hea) B8Halt (B8Wall F he0) B8Halt (B8Wall F hee) B8Halt B8Halt B8Halt)
    (N16 (B8Wall F hf2) B8Halt (B8Tail C hff) B8Halt (B8Wall F hf6) B8Halt B8Halt B8Halt (B8Wall F hfa) B8Halt (B8Wall F hf0) B8Halt (B8Wall F hfe) B8Halt B8Halt B8Halt).
Definition b8Tab_0_5 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Wall A h00) (B8Wall F h00) (B8Wall A h02) (B8Wall F h02) (B8Wall A h04) (B8Wall F h04) (B8Wall A h06) (B8Wall F h06) (B8Wall A h08) (B8Wall F h08) (B8Wall A h0a) (B8Wall F h0a) (B8Wall A h0c) (B8Wall F h0c) (B8Wall A h0e) (B8Wall F h0e))
    (N16 (B8Wall A h10) (B8Wall F h10) (B8Wall A h12) (B8Wall F h12) (B8Wall A h14) (B8Wall F h14) (B8Wall A h16) (B8Wall F h16) (B8Wall A h18) (B8Wall F h18) (B8Wall A h1a) (B8Wall F h1a) (B8Wall A h1c) (B8Wall F h1c) (B8Wall A h1e) (B8Wall F h1e))
    (N16 (B8Wall A h20) (B8Wall F h20) (B8Wall A h22) (B8Wall F h22) (B8Wall A h24) (B8Wall F h24) (B8Wall A h26) (B8Wall F h26) (B8Wall A h28) (B8Wall F h28) (B8Wall A h2a) (B8Wall F h2a) (B8Wall A h2c) (B8Wall F h2c) (B8Wall A h2e) (B8Wall F h2e))
    (N16 (B8Wall A h30) (B8Wall F h30) (B8Wall A h32) (B8Wall F h32) (B8Wall A h34) (B8Wall F h34) (B8Wall A h36) (B8Wall F h36) (B8Wall A h38) (B8Wall F h38) (B8Wall A h3a) (B8Wall F h3a) (B8Wall A h3c) (B8Wall F h3c) (B8Wall A h3e) (B8Wall F h3e))
    (N16 (B8Wall A h40) (B8Wall F h40) (B8Wall A h42) (B8Wall F h42) (B8Wall A h44) (B8Wall F h44) (B8Wall A h46) (B8Wall F h46) (B8Wall A h48) (B8Wall F h48) (B8Wall A h4a) (B8Wall F h4a) (B8Wall A h4c) (B8Wall F h4c) (B8Wall A h4e) (B8Wall F h4e))
    (N16 (B8Wall A h50) (B8Wall F h50) (B8Wall A h52) (B8Wall F h52) (B8Wall A h54) (B8Wall F h54) (B8Wall A h56) (B8Wall F h56) (B8Wall A h58) (B8Wall F h58) (B8Wall A h5a) (B8Wall F h5a) (B8Wall A h5c) (B8Wall F h5c) (B8Wall A h5e) (B8Wall F h5e))
    (N16 (B8Wall A h60) (B8Wall F h60) (B8Wall A h62) (B8Wall F h62) (B8Wall A h64) (B8Wall F h64) (B8Wall A h66) (B8Wall F h66) (B8Wall A h68) (B8Wall F h68) (B8Wall A h6a) (B8Wall F h6a) (B8Wall A h6c) (B8Wall F h6c) (B8Wall A h6e) (B8Wall F h6e))
    (N16 (B8Wall A h70) (B8Wall F h70) (B8Wall A h72) (B8Wall F h72) (B8Wall A h74) (B8Wall F h74) (B8Wall A h76) (B8Wall F h76) (B8Wall A h78) (B8Wall F h78) (B8Wall A h7a) (B8Wall F h7a) (B8Wall A h7c) (B8Wall F h7c) (B8Wall A h7e) (B8Wall F h7e))
    (N16 (B8Wall A h80) (B8Wall F h80) (B8Wall A h82) (B8Wall F h82) (B8Wall A h84) (B8Wall F h84) (B8Wall A h86) (B8Wall F h86) (B8Wall A h88) (B8Wall F h88) (B8Wall A h8a) (B8Wall F h8a) (B8Wall A h8c) (B8Wall F h8c) (B8Wall A h8e) (B8Wall F h8e))
    (N16 (B8Wall A h90) (B8Wall F h90) (B8Wall A h92) (B8Wall F h92) (B8Wall A h94) (B8Wall F h94) (B8Wall A h96) (B8Wall F h96) (B8Wall A h98) (B8Wall F h98) (B8Wall A h9a) (B8Wall F h9a) (B8Wall A h9c) (B8Wall F h9c) (B8Wall A h9e) (B8Wall F h9e))
    (N16 (B8Wall A ha0) (B8Wall F ha0) (B8Wall A ha2) (B8Wall F ha2) (B8Wall A ha4) (B8Wall F ha4) (B8Wall A ha6) (B8Wall F ha6) (B8Wall A ha8) (B8Wall F ha8) (B8Wall A haa) (B8Wall F haa) (B8Wall A hac) (B8Wall F hac) (B8Wall A hae) (B8Wall F hae))
    (N16 (B8Wall A hb0) (B8Wall F hb0) (B8Wall A hb2) (B8Wall F hb2) (B8Wall A hb4) (B8Wall F hb4) (B8Wall A hb6) (B8Wall F hb6) (B8Wall A hb8) (B8Wall F hb8) (B8Wall A hba) (B8Wall F hba) (B8Wall A hbc) (B8Wall F hbc) (B8Wall A hbe) (B8Wall F hbe))
    (N16 (B8Wall A hc0) (B8Wall F hc0) (B8Wall A hc2) (B8Wall F hc2) (B8Wall A hc4) (B8Wall F hc4) (B8Wall A hc6) (B8Wall F hc6) (B8Wall A hc8) (B8Wall F hc8) (B8Wall A hca) (B8Wall F hca) (B8Wall A hcc) (B8Wall F hcc) (B8Wall A hce) (B8Wall F hce))
    (N16 (B8Wall A hd0) (B8Wall F hd0) (B8Wall A hd2) (B8Wall F hd2) (B8Wall A hd4) (B8Wall F hd4) (B8Wall A hd6) (B8Wall F hd6) (B8Wall A hd8) (B8Wall F hd8) (B8Wall A hda) (B8Wall F hda) (B8Wall A hdc) (B8Wall F hdc) (B8Wall A hde) (B8Wall F hde))
    (N16 (B8Wall A he0) (B8Wall F he0) (B8Wall A he2) (B8Wall F he2) (B8Wall A he4) (B8Wall F he4) (B8Wall A he6) (B8Wall F he6) (B8Wall A he8) (B8Wall F he8) (B8Wall A hea) (B8Wall F hea) (B8Wall A hec) (B8Wall F hec) (B8Wall A hee) (B8Wall F hee))
    (N16 (B8Wall A hf0) (B8Wall F hf0) (B8Wall A hf2) (B8Wall F hf2) (B8Wall A hf4) (B8Wall F hf4) (B8Wall A hf6) (B8Wall F hf6) (B8Wall A hf8) (B8Wall F hf8) (B8Wall A hfa) (B8Wall F hfa) (B8Wall A hfc) (B8Wall F hfc) (B8Wall A hfe) (B8Wall F hfe)).
Definition b8Tab_1_0 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail B h40) (B8Tail B h41) (B8Tail B h42) (B8Tail B h43) (B8Tail B h44) (B8Tail B h45) (B8Tail B h46) (B8Tail B h47) (B8Tail B h48) (B8Tail B h49) (B8Tail B h4a) (B8Tail B h4b) (B8Tail B h4c) (B8Tail B h4d) (B8Tail B h4e) (B8Tail B h4f))
    (N16 (B8Tail B h50) (B8Tail B h51) (B8Tail B h52) (B8Tail B h53) (B8Tail B h54) (B8Tail B h55) (B8Tail B h56) (B8Tail B h57) (B8Tail B h58) (B8Tail B h59) (B8Tail B h5a) (B8Tail B h5b) (B8Tail B h5c) (B8Tail B h5d) (B8Tail B h5e) (B8Tail B h5f))
    (N16 (B8Tail B h60) (B8Tail B h61) (B8Tail B h62) (B8Tail B h63) (B8Tail B h64) (B8Tail B h65) (B8Tail B h66) (B8Tail B h67) (B8Tail B h68) (B8Tail B h69) (B8Tail B h6a) (B8Tail B h6b) (B8Tail B h6c) (B8Tail B h6d) (B8Tail B h6e) (B8Tail B h6f))
    (N16 (B8Tail B h70) (B8Tail B h71) (B8Tail B h72) (B8Tail B h73) (B8Tail B h74) (B8Tail B h75) (B8Tail B h76) (B8Tail B h77) (B8Tail B h78) (B8Tail B h79) (B8Tail B h7a) (B8Tail B h7b) (B8Tail B h7c) (B8Tail B h7d) (B8Tail B h7e) (B8Tail B h7f))
    (N16 (B8Tail D hc8) (B8Tail D hc9) (B8Tail D hca) (B8Tail D hcb) (B8Tail D hcc) (B8Tail D hcd) (B8Tail D hce) (B8Tail D hcf) (B8Tail B h79) (B8Wall F h92) (B8Tail D hce) (B8Tail D hcf) (B8Wall B h91) (B8Tail B h7b) (B8Wall A h90) (B8Wall F h90))
    (N16 (B8Tail B h70) (B8Tail B h71) (B8Tail B h72) (B8Tail B h73) (B8Tail B h74) (B8Tail B h75) (B8Tail B h76) (B8Tail B h77) (B8Tail B h78) (B8Tail B h79) (B8Tail B h7a) (B8Tail B h7b) (B8Tail B h7c) (B8Tail B h7d) (B8Tail B h7e) (B8Tail B h7f))
    (N16 (B8Wall B hc9) (B8Tail E h67) (B8Wall A hc8) (B8Wall F hc8) (B8Wall B h89) (B8Wall F hc8) (B8Wall A h88) (B8Wall F h88) (B8Tail D hd8) (B8Tail D hd9) (B8Tail D hda) (B8Tail D hdb) (B8Tail D hdc) (B8Tail D hdd) (B8Tail D hde) (B8Tail D hdf))
    (N16 (B8Wall A ha4) (B8Wall F ha4) (B8Wall A h84) (B8Wall F h84) (B8Tail C hfc) (B8Tail C hfd) (B8Tail C hfe) (B8Tail C hff) (B8Wall F h92) (B8Wall F h82) (B8Tail B h5e) (B8Tail B h5f) (B8Wall B h81) (B8Tail D hcf) (B8Wall A h80) (B8Wall F h80))
    (N16 (B8Tail D h80) (B8Tail D h81) (B8Tail D h82) (B8Tail D h83) (B8Tail D h84) (B8Tail D h85) (B8Tail D h86) (B8Tail D h87) (B8Tail D h88) (B8Tail D h89) (B8Tail D h8a) (B8Tail D h8b) (B8Tail D h8c) (B8Tail D h8d) (B8Tail D h8e) (B8Tail D h8f))
    (N16 (B8Tail D h90) (B8Tail D h91) (B8Tail D h92) (B8Tail D h93) (B8Tail D h94) (B8Tail D h95) (B8Tail D h96) (B8Tail D h97) (B8Tail D h98) (B8Tail D h99) (B8Tail D h9a) (B8Tail D h9b) (B8Tail D h9c) (B8Tail D h9d) (B8Tail D h9e) (B8Tail D h9f))
    (N16 (B8Tail D ha0) (B8Tail D ha1) (B8Tail D ha2) (B8Tail D ha3) (B8Tail D ha4) (B8Tail D ha5) (B8Tail D ha6) (B8Tail D ha7) (B8Tail D ha8) (B8Tail D ha9) (B8Tail D haa) (B8Tail D hab) (B8Tail D hac) (B8Tail D had) (B8Tail D hae) (B8Tail D haf))
    (N16 (B8Tail D hb0) (B8Tail D hb1) (B8Tail D hb2) (B8Tail D hb3) (B8Tail D hb4) (B8Tail D hb5) (B8Tail D hb6) (B8Tail D hb7) (B8Tail D hb8) (B8Tail D hb9) (B8Tail D hba) (B8Tail D hbb) (B8Tail D hbc) (B8Tail D hbd) (B8Tail D hbe) (B8Tail D hbf))
    (N16 (B8Tail D hc0) (B8Tail D hc1) (B8Tail D hc2) (B8Tail D hc3) (B8Tail D hc4) (B8Tail D hc5) (B8Tail D hc6) (B8Tail D hc7) (B8Tail D hc8) (B8Tail D hc9) (B8Tail D hca) (B8Tail D hcb) (B8Tail D hcc) (B8Tail D hcd) (B8Tail D hce) (B8Tail D hcf))
    (N16 (B8Tail D hd0) (B8Tail D hd1) (B8Tail D hd2) (B8Tail D hd3) (B8Tail D hd4) (B8Tail D hd5) (B8Tail D hd6) (B8Tail D hd7) (B8Tail D hd8) (B8Tail D hd9) (B8Tail D hda) (B8Tail D hdb) (B8Tail D hdc) (B8Tail D hdd) (B8Tail D hde) (B8Tail D hdf))
    (N16 (B8Tail D he0) (B8Tail D he1) (B8Tail D he2) (B8Tail D he3) (B8Tail D he4) (B8Tail D he5) (B8Tail D he6) (B8Tail D he7) (B8Tail D he8) (B8Tail D he9) (B8Tail D hea) (B8Tail D heb) (B8Tail D hec) (B8Tail D hed) (B8Tail D hee) (B8Tail D hef))
    (N16 (B8Tail D hf0) (B8Tail D hf1) (B8Tail D hf2) (B8Tail D hf3) (B8Tail D hf4) (B8Tail D hf5) (B8Tail D hf6) (B8Tail D hf7) (B8Tail D hf8) (B8Tail D hf9) (B8Tail D hfa) (B8Tail D hfb) (B8Tail D hfc) (B8Tail D hfd) (B8Tail D hfe) (B8Tail D hff)).
Definition b8Tab_1_1 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail C h80) (B8Tail C h81) (B8Tail C h82) (B8Tail C h83) (B8Tail C h84) (B8Tail C h85) (B8Tail C h86) (B8Tail C h87) (B8Tail C h88) (B8Tail C h89) (B8Tail C h8a) (B8Tail C h8b) (B8Tail C h8c) (B8Tail C h8d) (B8Tail C h8e) (B8Tail C h8f))
    (N16 (B8Tail C h90) (B8Tail C h91) (B8Tail C h92) (B8Tail C h93) (B8Tail C h94) (B8Tail C h95) (B8Tail C h96) (B8Tail C h97) (B8Tail C h98) (B8Tail C h99) (B8Tail C h9a) (B8Tail C h9b) (B8Tail C h9c) (B8Tail C h9d) (B8Tail C h9e) (B8Tail C h9f))
    (N16 (B8Tail C ha0) (B8Tail C ha1) (B8Tail C ha2) (B8Tail C ha3) (B8Tail C ha4) (B8Tail C ha5) (B8Tail C ha6) (B8Tail C ha7) (B8Tail C ha8) (B8Tail C ha9) (B8Tail C haa) (B8Tail C hab) (B8Tail C hac) (B8Tail C had) (B8Tail C hae) (B8Tail C haf))
    (N16 (B8Tail C hb0) (B8Tail C hb1) (B8Tail C hb2) (B8Tail C hb3) (B8Tail C hb4) (B8Tail C hb5) (B8Tail C hb6) (B8Tail C hb7) (B8Tail C hb8) (B8Tail C hb9) (B8Tail C hba) (B8Tail C hbb) (B8Tail C hbc) (B8Tail C hbd) (B8Tail C hbe) (B8Tail C hbf))
    (N16 (B8Tail C hc0) (B8Tail C hc1) (B8Tail C hc2) (B8Tail C hc3) (B8Tail C hc4) (B8Tail C hc5) (B8Tail C hc6) (B8Tail C hc7) (B8Tail C hc8) (B8Tail C hc9) (B8Tail C hca) (B8Tail C hcb) (B8Tail C hcc) (B8Tail C hcd) (B8Tail C hce) (B8Tail C hcf))
    (N16 (B8Tail C hd0) (B8Tail C hd1) (B8Tail C hd2) (B8Tail C hd3) (B8Tail C hd4) (B8Tail C hd5) (B8Tail C hd6) (B8Tail C hd7) (B8Tail C hd8) (B8Tail C hd9) (B8Tail C hda) (B8Tail C hdb) (B8Tail C hdc) (B8Tail C hdd) (B8Tail C hde) (B8Tail C hdf))
    (N16 (B8Tail C he0) (B8Tail C he1) (B8Tail C he2) (B8Tail C he3) (B8Tail C he4) (B8Tail C he5) (B8Tail C he6) (B8Tail C he7) (B8Tail C he8) (B8Tail C he9) (B8Tail C hea) (B8Tail C heb) (B8Tail C hec) (B8Tail C hed) (B8Tail C hee) (B8Tail C hef))
    (N16 (B8Tail C hf0) (B8Tail C hf1) (B8Tail C hf2) (B8Tail C hf3) (B8Tail C hf4) (B8Tail C hf5) (B8Tail C hf6) (B8Tail C hf7) (B8Tail C hf8) (B8Tail C hf9) (B8Tail C hfa) (B8Tail C hfb) (B8Tail C hfc) (B8Tail C hfd) (B8Tail C hfe) (B8Tail C hff))
    (N16 (B8Tail A h90) (B8Tail A h91) (B8Tail A h92) (B8Tail A h93) (B8Tail A h94) (B8Tail A h95) (B8Tail A h96) (B8Tail A h97) (B8Tail A h98) (B8Tail A h99) (B8Tail A h9a) (B8Tail A h9b) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f))
    (N16 (B8Tail C hf2) (B8Tail C hf3) (B8Wall A h24) (B8Wall F h24) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f) (B8Wall F h32) (B8Wall F h22) (B8Tail C hf6) (B8Tail C hf7) (B8Wall B h21) (B8Tail B h7f) (B8Wall A h20) (B8Wall F h20))
    (N16 (B8Tail C he0) (B8Tail C he1) (B8Tail C he2) (B8Tail C he3) (B8Tail C he4) (B8Tail C he5) (B8Tail C he6) (B8Tail C he7) (B8Tail C he8) (B8Tail C he9) (B8Tail C hea) (B8Tail C heb) (B8Tail C hec) (B8Tail C hed) (B8Tail C hee) (B8Tail C hef))
    (N16 (B8Tail C hf0) (B8Tail C hf1) (B8Tail C hf2) (B8Tail C hf3) (B8Tail C hf4) (B8Tail C hf5) (B8Tail C hf6) (B8Tail C hf7) (B8Tail C hf8) (B8Tail C hf9) (B8Tail C hfa) (B8Tail C hfb) (B8Tail C hfc) (B8Tail C hfd) (B8Tail C hfe) (B8Tail C hff))
    (N16 (B8Tail B h79) (B8Wall F h92) (B8Tail D hce) (B8Tail D hcf) (B8Wall B h91) (B8Tail B h7b) (B8Wall A h90) (B8Wall F h90) (B8Tail A hb9) (B8Wall F h12) (B8Wall A h90) (B8Wall F h90) (B8Wall B h11) (B8Tail A hbb) (B8Wall A h10) (B8Wall F h10))
    (N16 (B8Tail A hb0) (B8Tail A hb1) (B8Tail A hb2) (B8Tail A hb3) (B8Tail A hb4) (B8Tail A hb5) (B8Tail A hb6) (B8Tail A hb7) (B8Tail A hb8) (B8Tail A hb9) (B8Tail A hba) (B8Tail A hbb) (B8Tail A hbc) (B8Tail A hbd) (B8Tail A hbe) (B8Tail A hbf))
    (N16 (B8Wall B h49) (B8Tail B he7) (B8Wall A h48) (B8Wall F h48) (B8Wall B h09) (B8Wall F h48) (B8Wall A h08) (B8Wall F h08) (B8Tail B h78) (B8Tail B h79) (B8Tail B h7a) (B8Tail B h7b) (B8Tail B h7c) (B8Tail B h7d) (B8Tail B h7e) (B8Tail B h7f))
    (N16 (B8Wall A h24) (B8Wall F h24) (B8Wall A h04) (B8Wall F h04) (B8Tail C hbc) (B8Tail C hbd) (B8Tail C hbe) (B8Tail C hbf) (B8Wall F h12) (B8Wall F h02) (B8Tail A h9e) (B8Tail A h9f) (B8Wall B h01) (B8Wall F h90) (B8Wall A h00) (B8Wall F h00)).
Definition b8Tab_1_2 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail C hc0) (B8Tail C hc1) (B8Tail C hc2) (B8Tail C hc3) (B8Tail C hc4) (B8Tail C hc5) (B8Tail C hc6) (B8Tail C hc7) (B8Tail C hc8) (B8Tail C hc9) (B8Tail C hca) (B8Tail C hcb) (B8Tail C hcc) (B8Tail C hcd) (B8Tail C hce) (B8Tail C hcf))
    (N16 (B8Tail C hd0) (B8Tail C hd1) (B8Tail C hd2) (B8Tail C hd3) (B8Tail C hd4) (B8Tail C hd5) (B8Tail C hd6) (B8Tail C hd7) (B8Tail C hd8) (B8Tail C hd9) (B8Tail C hda) (B8Tail C hdb) (B8Tail C hdc) (B8Tail C hdd) (B8Tail C hde) (B8Tail C hdf))
    (N16 (B8Tail C he0) (B8Tail C he1) (B8Tail C he2) (B8Tail C he3) (B8Tail C he4) (B8Tail C he5) (B8Tail C he6) (B8Tail C he7) (B8Tail C he8) (B8Tail C he9) (B8Tail C hea) (B8Tail C heb) (B8Tail C hec) (B8Tail C hed) (B8Tail C hee) (B8Tail C hef))
    (N16 (B8Tail C hf0) (B8Tail C hf1) (B8Tail C hf2) (B8Tail C hf3) (B8Tail C hf4) (B8Tail C hf5) (B8Tail C hf6) (B8Tail C hf7) (B8Tail C hf8) (B8Tail C hf9) (B8Tail C hfa) (B8Tail C hfb) (B8Tail C hfc) (B8Tail C hfd) (B8Tail C hfe) (B8Tail C hff))
    (N16 (B8Tail A h80) (B8Tail A h81) (B8Tail A h82) (B8Tail A h83) (B8Tail A h84) (B8Tail A h85) (B8Tail A h86) (B8Tail A h87) (B8Tail A h88) (B8Tail A h89) (B8Tail A h8a) (B8Tail A h8b) (B8Tail A h8c) (B8Tail A h8d) (B8Tail A h8e) (B8Tail A h8f))
    (N16 (B8Tail A h90) (B8Tail A h91) (B8Tail A h92) (B8Tail A h93) (B8Tail A h94) (B8Tail A h95) (B8Tail A h96) (B8Tail A h97) (B8Tail A h98) (B8Tail A h99) (B8Tail A h9a) (B8Tail A h9b) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f))
    (N16 (B8Tail A ha0) (B8Tail A ha1) (B8Tail A ha2) (B8Tail A ha3) (B8Tail A ha4) (B8Tail A ha5) (B8Tail A ha6) (B8Tail A ha7) (B8Tail A ha8) (B8Tail A ha9) (B8Tail A haa) (B8Tail A hab) (B8Tail A hac) (B8Tail A had) (B8Tail A hae) (B8Tail A haf))
    (N16 (B8Tail A hb0) (B8Tail A hb1) (B8Tail A hb2) (B8Tail A hb3) (B8Tail A hb4) (B8Tail A hb5) (B8Tail A hb6) (B8Tail A hb7) (B8Tail A hb8) (B8Tail A hb9) (B8Tail A hba) (B8Tail A hbb) (B8Tail A hbc) (B8Tail A hbd) (B8Tail A hbe) (B8Tail A hbf))
    (N16 (B8Tail B h00) (B8Tail B h01) (B8Tail B h02) (B8Tail B h03) (B8Tail B h04) (B8Tail B h05) (B8Tail B h06) (B8Tail B h07) (B8Tail B h08) (B8Tail B h09) (B8Tail B h0a) (B8Tail B h0b) (B8Tail B h0c) (B8Tail B h0d) (B8Tail B h0e) (B8Tail B h0f))
    (N16 (B8Tail B h10) (B8Tail B h11) (B8Tail B h12) (B8Tail B h13) (B8Tail B h14) (B8Tail B h15) (B8Tail B h16) (B8Tail B h17) (B8Tail B h18) (B8Tail B h19) (B8Tail B h1a) (B8Tail B h1b) (B8Tail B h1c) (B8Tail B h1d) (B8Tail B h1e) (B8Tail B h1f))
    (N16 (B8Tail B h20) (B8Tail B h21) (B8Tail B h22) (B8Tail B h23) (B8Tail B h24) (B8Tail B h25) (B8Tail B h26) (B8Tail B h27) (B8Tail B h28) (B8Tail B h29) (B8Tail B h2a) (B8Tail B h2b) (B8Tail B h2c) (B8Tail B h2d) (B8Tail B h2e) (B8Tail B h2f))
    (N16 (B8Tail B h30) (B8Tail B h31) (B8Tail B h32) (B8Tail B h33) (B8Tail B h34) (B8Tail B h35) (B8Tail B h36) (B8Tail B h37) (B8Tail B h38) (B8Tail B h39) (B8Tail B h3a) (B8Tail B h3b) (B8Tail B h3c) (B8Tail B h3d) (B8Tail B h3e) (B8Tail B h3f))
    (N16 (B8Tail B h40) (B8Tail B h41) (B8Tail B h42) (B8Tail B h43) (B8Tail B h44) (B8Tail B h45) (B8Tail B h46) (B8Tail B h47) (B8Tail B h48) (B8Tail B h49) (B8Tail B h4a) (B8Tail B h4b) (B8Tail B h4c) (B8Tail B h4d) (B8Tail B h4e) (B8Tail B h4f))
    (N16 (B8Tail B h50) (B8Tail B h51) (B8Tail B h52) (B8Tail B h53) (B8Tail B h54) (B8Tail B h55) (B8Tail B h56) (B8Tail B h57) (B8Tail B h58) (B8Tail B h59) (B8Tail B h5a) (B8Tail B h5b) (B8Tail B h5c) (B8Tail B h5d) (B8Tail B h5e) (B8Tail B h5f))
    (N16 (B8Tail B h60) (B8Tail B h61) (B8Tail B h62) (B8Tail B h63) (B8Tail B h64) (B8Tail B h65) (B8Tail B h66) (B8Tail B h67) (B8Tail B h68) (B8Tail B h69) (B8Tail B h6a) (B8Tail B h6b) (B8Tail B h6c) (B8Tail B h6d) (B8Tail B h6e) (B8Tail B h6f))
    (N16 (B8Tail B h70) (B8Tail B h71) (B8Tail B h72) (B8Tail B h73) (B8Tail B h74) (B8Tail B h75) (B8Tail B h76) (B8Tail B h77) (B8Tail B h78) (B8Tail B h79) (B8Tail B h7a) (B8Tail B h7b) (B8Tail B h7c) (B8Tail B h7d) (B8Tail B h7e) (B8Tail B h7f)).
Definition b8Tab_1_3 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail B h80) (B8Tail B h81) (B8Tail B h82) (B8Tail B h83) (B8Tail B h84) (B8Tail B h85) (B8Tail B h86) (B8Tail B h87) (B8Tail B h88) (B8Tail B h89) (B8Tail B h8a) (B8Tail B h8b) (B8Tail B h8c) (B8Tail B h8d) (B8Tail B h8e) (B8Tail B h8f))
    (N16 (B8Tail B h90) (B8Tail B h91) (B8Tail B h92) (B8Tail B h93) (B8Tail B h94) (B8Tail B h95) (B8Tail B h96) (B8Tail B h97) (B8Tail B h98) (B8Tail B h99) (B8Tail B h9a) (B8Tail B h9b) (B8Tail B h9c) (B8Tail B h9d) (B8Tail B h9e) (B8Tail B h9f))
    (N16 (B8Tail B ha0) (B8Tail B ha1) (B8Tail B ha2) (B8Tail B ha3) (B8Tail B ha4) (B8Tail B ha5) (B8Tail B ha6) (B8Tail B ha7) (B8Tail B ha8) (B8Tail B ha9) (B8Tail B haa) (B8Tail B hab) (B8Tail B hac) (B8Tail B had) (B8Tail B hae) (B8Tail B haf))
    (N16 (B8Tail B hb0) (B8Tail B hb1) (B8Tail B hb2) (B8Tail B hb3) (B8Tail B hb4) (B8Tail B hb5) (B8Tail B hb6) (B8Tail B hb7) (B8Tail B hb8) (B8Tail B hb9) (B8Tail B hba) (B8Tail B hbb) (B8Tail B hbc) (B8Tail B hbd) (B8Tail B hbe) (B8Tail B hbf))
    (N16 (B8Tail B hc0) (B8Tail B hc1) (B8Tail B hc2) (B8Tail B hc3) (B8Tail B hc4) (B8Tail B hc5) (B8Tail B hc6) (B8Tail B hc7) (B8Tail B hc8) (B8Tail B hc9) (B8Tail B hca) (B8Tail B hcb) (B8Tail B hcc) (B8Tail B hcd) (B8Tail B hce) (B8Tail B hcf))
    (N16 (B8Tail B hd0) (B8Tail B hd1) (B8Tail B hd2) (B8Tail B hd3) (B8Tail B hd4) (B8Tail B hd5) (B8Tail B hd6) (B8Tail B hd7) (B8Tail B hd8) (B8Tail B hd9) (B8Tail B hda) (B8Tail B hdb) (B8Tail B hdc) (B8Tail B hdd) (B8Tail B hde) (B8Tail B hdf))
    (N16 (B8Tail B he0) (B8Tail B he1) (B8Tail B he2) (B8Tail B he3) (B8Tail B he4) (B8Tail B he5) (B8Tail B he6) (B8Tail B he7) (B8Tail B he8) (B8Tail B he9) (B8Tail B hea) (B8Tail B heb) (B8Tail B hec) (B8Tail B hed) (B8Tail B hee) (B8Tail B hef))
    (N16 (B8Tail B hf0) (B8Tail B hf1) (B8Tail B hf2) (B8Tail B hf3) (B8Tail B hf4) (B8Tail B hf5) (B8Tail B hf6) (B8Tail B hf7) (B8Tail B hf8) (B8Tail B hf9) (B8Tail B hfa) (B8Tail B hfb) (B8Tail B hfc) (B8Tail B hfd) (B8Tail B hfe) (B8Tail B hff))
    (N16 (B8Tail E h00) (B8Tail E h01) (B8Tail E h02) (B8Tail E h03) (B8Tail E h04) (B8Tail E h05) (B8Tail E h06) (B8Tail E h07) (B8Tail E h08) (B8Tail E h09) (B8Tail E h0a) (B8Tail E h0b) (B8Tail E h0c) (B8Tail E h0d) (B8Tail E h0e) (B8Tail E h0f))
    (N16 (B8Tail E h10) (B8Tail E h11) (B8Tail E h12) (B8Tail E h13) (B8Tail E h14) (B8Tail E h15) (B8Tail E h16) (B8Tail E h17) (B8Tail E h18) (B8Tail E h19) (B8Tail E h1a) (B8Tail E h1b) (B8Tail E h1c) (B8Tail E h1d) (B8Tail E h1e) (B8Tail E h1f))
    (N16 (B8Tail E h20) (B8Tail E h21) (B8Tail E h22) (B8Tail E h23) (B8Tail E h24) (B8Tail E h25) (B8Tail E h26) (B8Tail E h27) (B8Tail E h28) (B8Tail E h29) (B8Tail E h2a) (B8Tail E h2b) (B8Tail E h2c) (B8Tail E h2d) (B8Tail E h2e) (B8Tail E h2f))
    (N16 (B8Tail E h30) (B8Tail E h31) (B8Tail E h32) (B8Tail E h33) (B8Tail E h34) (B8Tail E h35) (B8Tail E h36) (B8Tail E h37) (B8Tail E h38) (B8Tail E h39) (B8Tail E h3a) (B8Tail E h3b) (B8Tail E h3c) (B8Tail E h3d) (B8Tail E h3e) (B8Tail E h3f))
    (N16 (B8Tail E h40) (B8Tail E h41) (B8Tail E h42) (B8Tail E h43) (B8Tail E h44) (B8Tail E h45) (B8Tail E h46) (B8Tail E h47) (B8Tail E h48) (B8Tail E h49) (B8Tail E h4a) (B8Tail E h4b) (B8Tail E h4c) (B8Tail E h4d) (B8Tail E h4e) (B8Tail E h4f))
    (N16 (B8Tail E h50) (B8Tail E h51) (B8Tail E h52) (B8Tail E h53) (B8Tail E h54) (B8Tail E h55) (B8Tail E h56) (B8Tail E h57) (B8Tail E h58) (B8Tail E h59) (B8Tail E h5a) (B8Tail E h5b) (B8Tail E h5c) (B8Tail E h5d) (B8Tail E h5e) (B8Tail E h5f))
    (N16 (B8Tail E h60) (B8Tail E h61) (B8Tail E h62) (B8Tail E h63) (B8Tail E h64) (B8Tail E h65) (B8Tail E h66) (B8Tail E h67) (B8Tail E h68) (B8Tail E h69) (B8Tail E h6a) (B8Tail E h6b) (B8Tail E h6c) (B8Tail E h6d) (B8Tail E h6e) (B8Tail E h6f))
    (N16 (B8Tail E h70) (B8Tail E h71) (B8Tail E h72) (B8Tail E h73) (B8Tail E h74) (B8Tail E h75) (B8Tail E h76) (B8Tail E h77) (B8Tail E h78) (B8Tail E h79) (B8Tail E h7a) (B8Tail E h7b) (B8Tail E h7c) (B8Tail E h7d) (B8Tail E h7e) (B8Tail E h7f)).
Definition b8Tab_1_4 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail A h80) (B8Tail A h81) (B8Tail A h82) (B8Tail A h83) (B8Tail A h84) (B8Tail A h85) (B8Tail A h86) (B8Tail A h87) (B8Tail A h88) (B8Tail A h89) (B8Tail A h8a) (B8Tail A h8b) (B8Tail A h8c) (B8Tail A h8d) (B8Tail A h8e) (B8Tail A h8f))
    (N16 (B8Tail A h90) (B8Tail A h91) (B8Tail A h92) (B8Tail A h93) (B8Tail A h94) (B8Tail A h95) (B8Tail A h96) (B8Tail A h97) (B8Tail A h98) (B8Tail A h99) (B8Tail A h9a) (B8Tail A h9b) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f))
    (N16 (B8Tail A ha0) (B8Tail A ha1) (B8Tail A ha2) (B8Tail A ha3) (B8Tail A ha4) (B8Tail A ha5) (B8Tail A ha6) (B8Tail A ha7) (B8Tail A ha8) (B8Tail A ha9) (B8Tail A haa) (B8Tail A hab) (B8Tail A hac) (B8Tail A had) (B8Tail A hae) (B8Tail A haf))
    (N16 (B8Tail A hb0) (B8Tail A hb1) (B8Tail A hb2) (B8Tail A hb3) (B8Tail A hb4) (B8Tail A hb5) (B8Tail A hb6) (B8Tail A hb7) (B8Tail A hb8) (B8Tail A hb9) (B8Tail A hba) (B8Tail A hbb) (B8Tail A hbc) (B8Tail A hbd) (B8Tail A hbe) (B8Tail A hbf))
    (N16 (B8Tail A hc0) (B8Tail A hc1) (B8Tail A hc2) (B8Tail A hc3) (B8Tail A hc4) (B8Tail A hc5) (B8Tail A hc6) (B8Tail A hc7) (B8Tail A hc8) (B8Tail A hc9) (B8Tail A hca) (B8Tail A hcb) (B8Tail A hcc) (B8Tail A hcd) (B8Tail A hce) (B8Tail A hcf))
    (N16 (B8Tail A hd0) (B8Tail A hd1) (B8Tail A hd2) (B8Tail A hd3) (B8Tail A hd4) (B8Tail A hd5) (B8Tail A hd6) (B8Tail A hd7) (B8Tail A hd8) (B8Tail A hd9) (B8Tail A hda) (B8Tail A hdb) (B8Tail A hdc) (B8Tail A hdd) (B8Tail A hde) (B8Tail A hdf))
    (N16 (B8Tail A he0) (B8Tail A he1) (B8Tail A he2) (B8Tail A he3) (B8Tail A he4) (B8Tail A he5) (B8Tail A he6) (B8Tail A he7) (B8Tail A he8) (B8Tail A he9) (B8Tail A hea) (B8Tail A heb) (B8Tail A hec) (B8Tail A hed) (B8Tail A hee) (B8Tail A hef))
    (N16 (B8Tail A hf0) (B8Tail A hf1) (B8Tail A hf2) (B8Tail A hf3) (B8Tail A hf4) (B8Tail A hf5) (B8Tail A hf6) (B8Tail A hf7) (B8Tail A hf8) (B8Tail A hf9) (B8Tail A hfa) (B8Tail A hfb) (B8Tail A hfc) (B8Tail A hfd) (B8Tail A hfe) (B8Tail A hff))
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt)
    (N16 B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt B8Halt).
Definition b8Tab_1_5 : Nib16 (Nib16 B8Out) :=
  N16
    (N16 (B8Tail C ha0) (B8Tail C ha1) (B8Tail C ha2) (B8Tail C ha3) (B8Tail C ha4) (B8Tail C ha5) (B8Tail C ha6) (B8Tail C ha7) (B8Tail C ha8) (B8Tail C ha9) (B8Tail C haa) (B8Tail C hab) (B8Tail C hac) (B8Tail C had) (B8Tail C hae) (B8Tail C haf))
    (N16 (B8Tail C hb0) (B8Tail C hb1) (B8Tail C hb2) (B8Tail C hb3) (B8Tail C hb4) (B8Tail C hb5) (B8Tail C hb6) (B8Tail C hb7) (B8Tail C hb8) (B8Tail C hb9) (B8Tail C hba) (B8Tail C hbb) (B8Tail C hbc) (B8Tail C hbd) (B8Tail C hbe) (B8Tail C hbf))
    (N16 (B8Tail B he4) (B8Tail B he5) (B8Tail B he6) (B8Tail B he7) (B8Wall B h49) (B8Tail B he7) (B8Wall A h48) (B8Wall F h48) (B8Tail C hb8) (B8Tail C hb9) (B8Tail C hba) (B8Tail C hbb) (B8Tail C hbc) (B8Tail C hbd) (B8Tail C hbe) (B8Tail C hbf))
    (N16 (B8Wall A h64) (B8Wall F h64) (B8Wall A h44) (B8Wall F h44) (B8Tail B hec) (B8Tail B hed) (B8Tail B hee) (B8Tail B hef) (B8Wall F h52) (B8Wall F h42) (B8Tail A hbe) (B8Tail A hbf) (B8Wall B h41) (B8Tail C haf) (B8Wall A h40) (B8Wall F h40))
    (N16 (B8Tail B hc0) (B8Tail B hc1) (B8Tail B hc2) (B8Tail B hc3) (B8Tail B hc4) (B8Tail B hc5) (B8Tail B hc6) (B8Tail B hc7) (B8Tail B hc8) (B8Tail B hc9) (B8Tail B hca) (B8Tail B hcb) (B8Tail B hcc) (B8Tail B hcd) (B8Tail B hce) (B8Tail B hcf))
    (N16 (B8Tail B hd0) (B8Tail B hd1) (B8Tail B hd2) (B8Tail B hd3) (B8Tail B hd4) (B8Tail B hd5) (B8Tail B hd6) (B8Tail B hd7) (B8Tail B hd8) (B8Tail B hd9) (B8Tail B hda) (B8Tail B hdb) (B8Tail B hdc) (B8Tail B hdd) (B8Tail B hde) (B8Tail B hdf))
    (N16 (B8Tail B he0) (B8Tail B he1) (B8Tail B he2) (B8Tail B he3) (B8Tail B he4) (B8Tail B he5) (B8Tail B he6) (B8Tail B he7) (B8Tail B he8) (B8Tail B he9) (B8Tail B hea) (B8Tail B heb) (B8Tail B hec) (B8Tail B hed) (B8Tail B hee) (B8Tail B hef))
    (N16 (B8Tail B hf0) (B8Tail B hf1) (B8Tail B hf2) (B8Tail B hf3) (B8Tail B hf4) (B8Tail B hf5) (B8Tail B hf6) (B8Tail B hf7) (B8Tail B hf8) (B8Tail B hf9) (B8Tail B hfa) (B8Tail B hfb) (B8Tail B hfc) (B8Tail B hfd) (B8Tail B hfe) (B8Tail B hff))
    (N16 (B8Tail A h90) (B8Tail A h91) (B8Tail A h92) (B8Tail A h93) (B8Tail A h94) (B8Tail A h95) (B8Tail A h96) (B8Tail A h97) (B8Tail A h98) (B8Tail A h99) (B8Tail A h9a) (B8Tail A h9b) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f))
    (N16 (B8Tail C hf2) (B8Tail C hf3) (B8Wall A h24) (B8Wall F h24) (B8Tail A h9c) (B8Tail A h9d) (B8Tail A h9e) (B8Tail A h9f) (B8Wall F h32) (B8Wall F h22) (B8Tail C hf6) (B8Tail C hf7) (B8Wall B h21) (B8Tail B h7f) (B8Wall A h20) (B8Wall F h20))
    (N16 (B8Tail C he0) (B8Tail C he1) (B8Tail C he2) (B8Tail C he3) (B8Tail C he4) (B8Tail C he5) (B8Tail C he6) (B8Tail C he7) (B8Tail C he8) (B8Tail C he9) (B8Tail C hea) (B8Tail C heb) (B8Tail C hec) (B8Tail C hed) (B8Tail C hee) (B8Tail C hef))
    (N16 (B8Tail C hf0) (B8Tail C hf1) (B8Tail C hf2) (B8Tail C hf3) (B8Tail C hf4) (B8Tail C hf5) (B8Tail C hf6) (B8Tail C hf7) (B8Tail C hf8) (B8Tail C hf9) (B8Tail C hfa) (B8Tail C hfb) (B8Tail C hfc) (B8Tail C hfd) (B8Tail C hfe) (B8Tail C hff))
    (N16 (B8Tail B h79) (B8Wall F h92) (B8Tail D hce) (B8Tail D hcf) (B8Wall B h91) (B8Tail B h7b) (B8Wall A h90) (B8Wall F h90) (B8Tail A hb9) (B8Wall F h12) (B8Wall A h90) (B8Wall F h90) (B8Wall B h11) (B8Tail A hbb) (B8Wall A h10) (B8Wall F h10))
    (N16 (B8Tail A hb0) (B8Tail A hb1) (B8Tail A hb2) (B8Tail A hb3) (B8Tail A hb4) (B8Tail A hb5) (B8Tail A hb6) (B8Tail A hb7) (B8Tail A hb8) (B8Tail A hb9) (B8Tail A hba) (B8Tail A hbb) (B8Tail A hbc) (B8Tail A hbd) (B8Tail A hbe) (B8Tail A hbf))
    (N16 (B8Wall B h49) (B8Tail B he7) (B8Wall A h48) (B8Wall F h48) (B8Wall B h09) (B8Wall F h48) (B8Wall A h08) (B8Wall F h08) (B8Tail B h78) (B8Tail B h79) (B8Tail B h7a) (B8Tail B h7b) (B8Tail B h7c) (B8Tail B h7d) (B8Tail B h7e) (B8Tail B h7f))
    (N16 (B8Wall A h24) (B8Wall F h24) (B8Wall A h04) (B8Wall F h04) (B8Tail C hbc) (B8Tail C hbd) (B8Tail C hbe) (B8Tail C hbf) (B8Wall F h12) (B8Wall F h02) (B8Tail A h9e) (B8Tail A h9f) (B8Wall B h01) (B8Wall F h90) (B8Wall A h00) (B8Wall F h00)).

Inductive B8Table : Type :=
  | MkB8T (t00 t01 t02 t03 t04 t05 t10 t11 t12 t13 t14 t15 : Nib16 (Nib16 B8Out)).

Definition theB8Table : B8Table :=
  MkB8T b8Tab_0_0 b8Tab_0_1 b8Tab_0_2 b8Tab_0_3 b8Tab_0_4 b8Tab_0_5
        b8Tab_1_0 b8Tab_1_1 b8Tab_1_2 b8Tab_1_3 b8Tab_1_4 b8Tab_1_5.
Arguments theB8Table : simpl never.

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
  if side_b then (sL {{q}}> byteBitsRevToSide b sR)
  else (byteBitsToSide b sL <{{q}} sR).

Fixpoint simB8Raw (fuel : nat) (q : Q) (rb : list bool) (cur : bool) (lb : list bool) : B8Out :=
  match fuel with
  | O => B8Fail
  | S fuel' =>
    match tmStepRaw q cur with
    | None => B8Halt
    | Some (nq, w, false) =>
      match lb with
      | [] => B8Tail nq (packBitsList (rev rb ++ [w]))
      | nl :: l' => simB8Raw fuel' nq (w :: rb) nl l'
      end
    | Some (nq, w, true) =>
      match rb with
      | [] => B8Wall nq (packBitsList (w :: lb))
      | nr :: r' => simB8Raw fuel' nq r' nr (w :: lb)
      end
    end
  end.

Lemma simB8Raw_sound fuel q rb cur lb (sL sR : side) :
  (length rb + 1 + length lb = 8)%nat ->
  match simB8Raw fuel q rb cur lb with
  | B8Wall qOut outB =>
    bitsToSide (cur :: lb) sL <{{q}} bitsToSide rb sR -->*
    byteBitsToSide outB sL {{qOut}}> sR
  | B8Tail qOut outB =>
    bitsToSide (cur :: lb) sL <{{q}} bitsToSide rb sR -->*
    sL <{{qOut}} byteBitsRevToSide outB sR
  | B8Halt =>
    halts tm (bitsToSide (cur :: lb) sL <{{q}} bitsToSide rb sR)
  | B8Fail => True
  end.
Proof.
  revert q rb cur lb. induction fuel as [|fuel IH]; intros q rb cur lb Hlen; simpl.
  - exact I.
  - destruct (tmStepRaw q cur) as [[[nq w] [|]] |] eqn:Hst.
    + destruct rb as [|nr r'].
      * assert (Hlen8 : length (w :: lb) = 8%nat) by (simpl in Hlen |- *; lia).
        unfold byteBitsToSide.
        rewrite (byteBits_packBitsList _ Hlen8). simpl bitsToSide.
        exact (step_raw_hl_right _ _ _ _ (bitsToSide lb sL) sR Hst).
      * assert (Hlen' : (length r' + 1 + length (w :: lb) = 8)%nat)
          by (simpl in Hlen |- *; lia).
        pose proof (IH nq r' nr (w :: lb) Hlen') as Hih.
        pose proof (step_raw_hl_right _ _ _ _ (bitsToSide lb sL) (bitsToSide (nr :: r') sR) Hst) as Hs.
        simpl bitsToSide in Hs, Hih |- *.
        destruct (simB8Raw fuel nq r' nr (w :: lb)).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (evstep_halts _ _ Hs Hih).
        -- exact I.
    + destruct lb as [|nl l'].
      * assert (Hlen8 : length (rev rb ++ [w]) = 8%nat).
        { rewrite length_app, length_rev. simpl in Hlen |- *; lia. }
        unfold byteBitsRevToSide.
        rewrite (byteBits_packBitsList _ Hlen8).
        rewrite rev_app_distr, rev_involutive; simpl.
        exact (step_raw_hl_left _ _ _ _ sL (bitsToSide rb sR) Hst).
      * assert (Hlen' : (length (w :: rb) + 1 + length l' = 8)%nat)
          by (simpl in Hlen |- *; lia).
        pose proof (IH nq (w :: rb) nl l' Hlen') as Hih.
        pose proof (step_raw_hl_left _ _ _ _ (bitsToSide (nl :: l') sL) (bitsToSide rb sR) Hst) as Hs.
        simpl bitsToSide in Hs, Hih |- *.
        destruct (simB8Raw fuel nq (w :: rb) nl l').
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (ev_trans _ _ _ Hs Hih).
        -- exact (evstep_halts _ _ Hs Hih).
        -- exact I.
    + exact (step_raw_hl_none _ _ _ _ Hst).
Qed.

Definition checkB8One (tbl : B8Table) (rawFuel : nat) (side_b : bool) (q : Q) (b : Byte) : bool :=
  if side_b then
    match rev (byteBits b) with
    | [] => false
    | c :: r => b8OutEqb (simB8Raw rawFuel q r c []) (b8EntryT tbl true q b)
    end
  else
    match byteBits b with
    | [] => false
    | c :: l => b8OutEqb (simB8Raw rawFuel q [] c l) (b8EntryT tbl false q b)
    end.

Definition allNib (f : Nib -> bool) : bool :=
  f X0 && f X1 && f X2 && f X3 && f X4 && f X5 && f X6 && f X7 &&
  f X8 && f X9 && f XA && f XB && f XC && f XD && f XE && f XF.

Lemma allNib_sound f : allNib f = true -> forall n, f n = true.
Proof.
  intros H n. unfold allNib in H.
  repeat (apply andb_prop in H as [H ?]).
  destruct n; assumption.
Qed.

Definition allByte (f : Byte -> bool) : bool :=
  allNib (fun hi => allNib (fun lo => f (MkB hi lo))).

Lemma allByte_sound f : allByte f = true -> forall b, f b = true.
Proof.
  intros H [hi lo].
  exact (allNib_sound _ (allNib_sound _ H hi) lo).
Qed.

Definition allQ (f : Q -> bool) : bool :=
  f A && f B && f C && f D && f E && f F.

Lemma allQ_sound f : allQ f = true -> forall q, f q = true.
Proof.
  intros H q. unfold allQ in H.
  repeat (apply andb_prop in H as [H ?]).
  destruct q; assumption.
Qed.

Definition checkB8AllWith (rawFuel : nat) : bool :=
  allQ (fun q => allByte (checkB8One theB8Table rawFuel false q)) &&
  allQ (fun q => allByte (checkB8One theB8Table rawFuel true q)).

Lemma b8_valid : checkB8AllWith 45%nat = true.
Proof. vm_check_eq. Qed.

Lemma checkB8AllWith_sound rawFuel side_b q b (sL sR : side) :
  checkB8AllWith rawFuel = true ->
  match b8EntryT theB8Table side_b q b with
  | B8Wall qOut outB =>
    byteEntryCfg side_b q b sL sR -->* byteBitsToSide outB sL {{qOut}}> sR
  | B8Tail qOut outB =>
    byteEntryCfg side_b q b sL sR -->* sL <{{qOut}} byteBitsRevToSide outB sR
  | B8Halt => halts tm (byteEntryCfg side_b q b sL sR)
  | B8Fail => True
  end.
Proof.
  intros Hv. unfold checkB8AllWith in Hv.
  apply andb_prop in Hv as [HvF HvT].
  destruct side_b.
  - pose proof (allByte_sound _ (allQ_sound _ HvT q) b) as He.
    unfold checkB8One in He.
    pose proof (byteBits_len b) as Hlen.
    assert (Hrlen : length (rev (byteBits b)) = 8%nat) by (rewrite length_rev; exact Hlen).
    destruct (rev (byteBits b)) as [|c r] eqn:Hr; [discriminate |].
    apply b8OutEqb_eq in He. rewrite <- He.
    assert (Hlen8 : (length r + 1 + length (@nil bool) = 8)%nat) by (simpl in Hrlen |- *; lia).
    pose proof (simB8Raw_sound rawFuel q r c [] sL sR Hlen8) as Hs.
    unfold byteEntryCfg, byteBitsRevToSide. rewrite Hr.
    simpl bitsToSide in Hs |- *.
    destruct (simB8Raw rawFuel q r c []); exact Hs.
  - pose proof (allByte_sound _ (allQ_sound _ HvF q) b) as He.
    unfold checkB8One in He.
    pose proof (byteBits_len b) as Hlen.
    destruct (byteBits b) as [|c l] eqn:Hb; [discriminate |].
    apply b8OutEqb_eq in He. rewrite <- He.
    assert (Hlen8 : (length (@nil bool) + 1 + length l = 8)%nat) by (simpl in Hlen |- *; lia).
    pose proof (simB8Raw_sound rawFuel q [] c l sL sR Hlen8) as Hs.
    unfold byteEntryCfg, byteBitsToSide. rewrite Hb.
    simpl bitsToSide in Hs |- *.
    destruct (simB8Raw rawFuel q [] c l); exact Hs.
Qed.

Lemma b8Entry_sound side_b q b (sL sR : side) :
  match b8EntryT theB8Table side_b q b with
  | B8Wall qOut outB =>
    byteEntryCfg side_b q b sL sR -->* byteBitsToSide outB sL {{qOut}}> sR
  | B8Tail qOut outB =>
    byteEntryCfg side_b q b sL sR -->* sL <{{qOut}} byteBitsRevToSide outB sR
  | B8Halt => halts tm (byteEntryCfg side_b q b sL sR)
  | B8Fail => True
  end.
Proof.
  exact (checkB8AllWith_sound 45%nat side_b q b sL sR b8_valid).
Qed.

Fixpoint bytesToLeft (bs : list Byte) (sL : side) : side :=
  match bs with
  | [] => sL
  | b :: bs' => byteBitsToSide b (bytesToLeft bs' sL)
  end.

Fixpoint bytesToRight (bs : list Byte) (sR : side) : side :=
  match bs with
  | [] => sR
  | b :: bs' => byteBitsRevToSide b (bytesToRight bs' sR)
  end.

Lemma byteBitsToSide_zero : byteBitsToSide h00 0inf = 0inf.
Proof. exact (bitsToSide_zeros 8%nat). Qed.

Fixpoint isAllZeroBytes (xs : list Byte) : bool :=
  match xs with
  | [] => true
  | x :: xs' => byteEqb x h00 && isAllZeroBytes xs'
  end.

Lemma isAllZeroBytes_sound xs :
  isAllZeroBytes xs = true -> bytesToLeft xs 0inf = 0inf.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  intros H. apply andb_prop in H as [Hx Hxs].
  apply byteEqb_eq in Hx. subst x.
  rewrite (IH Hxs). exact byteBitsToSide_zero.
Qed.

Fixpoint bytesEqZeroPad (xs ys : list Byte) : bool :=
  match xs, ys with
  | [], _ => isAllZeroBytes ys
  | _ :: _, [] => isAllZeroBytes xs
  | x :: xs', y :: ys' => byteEqb x y && bytesEqZeroPad xs' ys'
  end.

Lemma bytesEqZeroPad_sound xs ys :
  bytesEqZeroPad xs ys = true -> bytesToLeft xs 0inf = bytesToLeft ys 0inf.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys H.
  - simpl in H |- *. symmetry. exact (isAllZeroBytes_sound ys H).
  - destruct ys as [|y ys]; [exact (isAllZeroBytes_sound (x :: xs) H) |].
    simpl in H |- *. apply andb_prop in H as [Hxy Hrest].
    apply byteEqb_eq in Hxy. subst y.
    rewrite (IH ys Hrest). reflexivity.
Qed.

Definition popByte (xs : list Byte) : Byte * list Byte :=
  match xs with
  | [] => (h00, [])
  | b :: bs => (b, bs)
  end.

Lemma popByte_spec xs :
  bytesToLeft xs 0inf = byteBitsToSide (fst (popByte xs)) (bytesToLeft (snd (popByte xs)) 0inf).
Proof.
  destruct xs as [|b bs]; simpl; [symmetry; exact byteBitsToSide_zero | reflexivity].
Qed.

Fixpoint popNBytes (n : nat) (xs : list Byte) : list Byte * list Byte :=
  match n with
  | O => ([], xs)
  | S n' =>
    let '(b, xs') := popByte xs in
    let '(bs, rest) := popNBytes n' xs' in
    (b :: bs, rest)
  end.

Lemma popNBytes_spec n xs :
  bytesToLeft xs 0inf =
  bytesToLeft (fst (popNBytes n xs)) (bytesToLeft (snd (popNBytes n xs)) 0inf).
Proof.
  revert xs. induction n as [|n IH]; intros xs; simpl; [reflexivity |].
  pose proof (popByte_spec xs) as Hpb.
  destruct (popByte xs) as [b xs']; simpl in Hpb.
  pose proof (IH xs') as Hih.
  destruct (popNBytes n xs') as [bs rest]; simpl in *.
  rewrite Hpb, Hih. reflexivity.
Qed.

Inductive SliceOut : Type :=
  | SliceWall (qOut : Q) (outB : Byte) (lBytes : list Byte)
  | SliceTail (qOut : Q) (outSlice : list Byte)
  | SliceHalt
  | SliceFail.

Fixpoint simSliceBytes (tbl : B8Table) (fuel : nat) (side_b : bool) (q : Q)
    (rb : list Byte) (cb : Byte) (lb : list Byte) : SliceOut :=
  match fuel with
  | O => SliceFail
  | S fuel' =>
    match b8EntryT tbl side_b q cb with
    | B8Wall qOut outB =>
      match rb with
      | [] => SliceWall qOut outB lb
      | pb :: rb' => simSliceBytes tbl fuel' true qOut rb' pb (outB :: lb)
      end
    | B8Tail qOut outB =>
      match lb with
      | [] => SliceTail qOut (outB :: rb)
      | nb :: lb' => simSliceBytes tbl fuel' false qOut (outB :: rb) nb lb'
      end
    | B8Halt => SliceHalt
    | B8Fail => SliceFail
    end
  end.

Lemma simSliceBytes_sound fuel side_b q rb cb lb (sL sR : side) :
  match simSliceBytes theB8Table fuel side_b q rb cb lb with
  | SliceWall qOut outB l' =>
    byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR) -->*
    bytesToLeft (outB :: l') sL {{qOut}}> sR
  | SliceTail qOut outSlice =>
    byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR) -->*
    sL <{{qOut}} bytesToRight outSlice sR
  | SliceHalt =>
    halts tm (byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR))
  | SliceFail => True
  end.
Proof.
  revert side_b q rb cb lb.
  induction fuel as [|fuel IH]; intros side_b q rb cb lb; simpl.
  - exact I.
  - pose proof (b8Entry_sound side_b q cb (bytesToLeft lb sL) (bytesToRight rb sR)) as Hb8.
    destruct (b8EntryT theB8Table side_b q cb) as [qOut outB | qOut outB | |].
    + destruct rb as [|pb rb']; simpl in Hb8 |- *.
      * exact Hb8.
      * pose proof (IH true qOut rb' pb (outB :: lb)) as Hih.
        simpl in Hih.
        destruct (simSliceBytes theB8Table fuel true qOut rb' pb (outB :: lb)).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (evstep_halts _ _ Hb8 Hih).
        -- exact I.
    + destruct lb as [|nb lb']; simpl in Hb8 |- *.
      * exact Hb8.
      * pose proof (IH false qOut (outB :: rb) nb lb') as Hih.
        simpl in Hih.
        destruct (simSliceBytes theB8Table fuel false qOut (outB :: rb) nb lb').
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (ev_trans _ _ _ Hb8 Hih).
        -- exact (evstep_halts _ _ Hb8 Hih).
        -- exact I.
    + exact Hb8.
    + exact I.
Qed.
Arguments simSliceBytes : simpl never.

(* ========================================================================== *)
(* Section 6: 14-Stage Wall-Tower DAG Tables & Inductive Soundness            *)
(* ========================================================================== *)

Inductive RuleSlot : Type :=
  | R0 : RuleSlot
  | RS (idOut : N) (qOut : Q) : RuleSlot.

Inductive DagNode : Type :=
  | MkDag (npar : N) (nslice : list Byte) (s0 s1 s3 s5 : RuleSlot).

Definition dagDefault : DagNode := MkDag 0%N [] R0 R0 R0 R0.

Definition bs2 (b0 b1 : Byte) : list Byte := b0 :: b1 :: nil.
Definition bs4 (b0 b1 b2 b3 : Byte) : list Byte := b0 :: b1 :: b2 :: b3 :: nil.
Definition bs5 (b0 b1 b2 b3 b4 : Byte) : list Byte := b0 :: b1 :: b2 :: b3 :: b4 :: nil.
Definition bs6 (b0 b1 b2 b3 b4 b5 : Byte) : list Byte := b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil.

Definition getRuleSlot (dn : DagNode) (q : Q) : RuleSlot :=
  let 'MkDag _ _ s0 s1 s3 s5 := dn in
  match q with
  | A => s0 | B => s1 | D => s3 | F => s5 | _ => R0
  end.

Inductive DagPTree : Type :=
  | DPEmpty : DagPTree
  | DPNode (v : DagNode) (l r : DagPTree) : DagPTree.

Fixpoint ptree_get (t : DagPTree) (p : positive) : DagNode :=
  match t with
  | DPEmpty => dagDefault
  | DPNode v l r =>
    match p with
    | xH => v
    | xO q => ptree_get l q
    | xI q => ptree_get r q
    end
  end.

Fixpoint ptree_forall (f : DagNode -> bool) (t : DagPTree) : bool :=
  match t with
  | DPEmpty => true
  | DPNode v l r => f v && ptree_forall f l && ptree_forall f r
  end.

Lemma ptree_forall_sound (f : DagNode -> bool) (t : DagPTree) :
  f dagDefault = true ->
  ptree_forall f t = true ->
  forall p : positive, f (ptree_get t p) = true.
Proof.
  intros Hdflt. induction t as [|v l IHl r IHr]; intros H p; simpl in *.
  - exact Hdflt.
  - apply andb_prop in H as [H1 Hr].
    apply andb_prop in H1 as [Hv Hl].
    destruct p as [q | q |]; [exact (IHr Hr q) | exact (IHl Hl q) | exact Hv].
Qed.

Inductive DagNTree : Type :=
  | MkDagNTree (v0 : DagNode) (rest : DagPTree) : DagNTree.

Definition emptyDagTree : DagNTree := MkDagNTree dagDefault DPEmpty.

Definition ntree_get (nt : DagNTree) (i : N) : DagNode :=
  let 'MkDagNTree v0 t := nt in
  match i with
  | N0 => v0
  | Npos p => ptree_get t p
  end.

Definition ntree_forall (f : DagNode -> bool) (nt : DagNTree) : bool :=
  let 'MkDagNTree v0 t := nt in f v0 && ptree_forall f t.

Lemma ntree_forall_sound (f : DagNode -> bool) (nt : DagNTree) :
  f dagDefault = true ->
  ntree_forall f nt = true ->
  forall i : N, f (ntree_get nt i) = true.
Proof.
  intros Hdflt H i. destruct nt as [v0 t]; simpl in *.
  apply andb_prop in H as [Hv0 Ht].
  destruct i as [|p]; [exact Hv0 | exact (ptree_forall_sound f t Hdflt Ht p)].
Qed.

Local Open Scope N_scope.

Definition dagTree_0 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 7 C) R0 R0) (DPNode (MkDag 5 nil R0 R0 R0 (RS 2 B)) (DPNode (MkDag 5 nil (RS 2 D)
    R0 R0 (RS 3 A)) (DPNode (MkDag 8 nil R0 (RS 5 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 9 nil R0 (RS 0 C) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 nil R0 (RS 4 C) R0 R0) (DPNode (MkDag 9 nil R0 (RS 6 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 nil R0 (RS 1 B) R0 R0) DPEmpty DPEmpty))).

Definition dagTree_1 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h9e h5f h2f hbf hfc) R0 (RS 38 A) R0 (RS 38 A)) (DPNode (MkDag 0 (bs5 hee h79 h7c hf3
    hfc) (RS 1 D) R0 R0 (RS 9 B)) (DPNode (MkDag 0 (bs5 hee h7f h3c hf3 hfc) (RS 2 D) R0 R0 (RS 92 B)) (DPNode
    (MkDag 0 (bs5 hfe h79 h7f h97 hfc) R0 (RS 67 C) (RS 68 E) (RS 67 C)) (DPNode (MkDag 0 (bs5 h9e h5f h3c hf3 hfc)
    R0 (RS 0 A) R0 (RS 0 A)) (DPNode (MkDag 0 (bs5 hbe h79 hfc hf3 hfc) R0 (RS 24 C) R0 R0) (DPNode (MkDag 0 (bs5
    h9e h79 h7c hbe hfc) R0 (RS 14 A) R0 (RS 14 A)) (DPNode (MkDag 0 (bs5 hbe h5f h3c hf3 hfc) R0 (RS 36 C) (RS 65
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hbe h79 hfc hfe hfc) R0 (RS 63 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h7c hbe he7 hff hfc) (RS 49 E) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7e h79 hfc hf3 hfc) R0 R0
    R0 (RS 24 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hfe h79 hfc hf3 hfc) R0 (RS 79 C) (RS 80 E) (RS
    79 C)) (DPNode (MkDag 0 (bs5 hbe h7f h3c hf3 hfc) R0 (RS 82 C) R0 R0) (DPNode (MkDag 0 (bs5 h9e h79 hf9 hff
    hfc) R0 (RS 3 A) R0 (RS 3 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3e h79 h79 hff hfc) R0 R0 R0 (RS
    11 B)) (DPNode (MkDag 0 (bs5 hfe h5f h2f hbf hfc) R0 (RS 97 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 0 (bs5 hbe h79 h7c hf3 hfc) R0 (RS 25 C) R0 R0) (DPNode (MkDag 0 (bs5 hfe h79 hef h97 hfc) (RS 20 D) (RS
    41 C) R0 (RS 41 C)) (DPNode (MkDag 0 (bs5 hfe h5f h3c hf3 hfc) R0 (RS 86 C) (RS 87 E) (RS 86 C)) (DPNode (MkDag
    0 (bs5 h7e h79 h7f h97 hfc) (RS 29 C) R0 R0 (RS 4 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7c hf7
    he7 h97 hfc) (RS 53 D) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7e h7f h2f hbf hfc) R0 R0 R0 (RS 7 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs5 hfe h79 hff h97 hfc) (RS 28 D) (RS 58 C) (RS 59 E) (RS 58 C)) (DPNode (MkDag 0
    (bs5 h3e h79 h7c hbe hfc) R0 R0 R0 (RS 1 B)) (DPNode (MkDag 0 (bs5 h73 hcf h3c hf3 hfc) R0 R0 R0 (RS 46 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfe h79 he7 h97 hfc) R0 (RS 96 C) R0 R0) (DPNode (MkDag 0 (bs5
    h7e h7f h3c hf3 hfc) (RS 7 C) R0 R0 (RS 82 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs5 h97 hcf h3c
    hf3 hfc) R0 (RS 31 A) R0 (RS 31 A)) (DPNode (MkDag 0 (bs5 hee h79 hfc hf3 hfc) R0 R0 R0 (RS 80 B)) (DPNode
    (MkDag 0 (bs5 hbe h79 h79 hff hfc) R0 (RS 35 C) (RS 56 E) (RS 35 C)) (DPNode (MkDag 0 (bs5 hbe h79 hff h97 hfc)
    R0 (RS 28 C) R0 (RS 28 C)) (DPNode (MkDag 0 (bs5 h7e h5f h2f hbf hfc) (RS 4 C) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 he5 hff h3f hbf hfc) R0 R0 R0 (RS 51 B)) (DPNode (MkDag 0 (bs5 hfe h7f h3c hf3
    hfc) R0 (RS 42 C) R0 (RS 42 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hee h5f h2f hbf hfc) (RS 26 D)
    R0 R0 (RS 66 B)) (DPNode (MkDag 0 (bs5 hbe h7f h2f hbf hfc) R0 (RS 7 C) (RS 83 E) R0) (DPNode (MkDag 0 (bs5 h9e
    h79 he7 h97 hfc) R0 (RS 75 A) R0 (RS 75 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbe h79 he7 h97
    hfc) R0 (RS 60 C) (RS 61 E) R0) (DPNode (MkDag 0 (bs5 h7e h79 he5 hff hfc) R0 R0 R0 (RS 29 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs5 h9e h79 h7c hf3 hfc) R0 (RS 73 A) R0 (RS 73 A)) (DPNode (MkDag 0 (bs5 h9e h79
    h7c hfe hfc) R0 (RS 46 C) R0 (RS 46 C)) (DPNode (MkDag 0 (bs5 h9e h79 h7f h97 hfc) R0 (RS 15 A) R0 (RS 15 A))
    (DPNode (MkDag 0 (bs5 hee h79 h7c hfe hfc) R0 R0 R0 (RS 13 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5
    hbc hff he7 h97 hfc) R0 (RS 55 C) R0 R0) (DPNode (MkDag 0 (bs5 hbe h5f h2f hbf hfc) R0 (RS 88 C) (RS 89 E) R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9e h79 hfc hf3 hfc) R0 (RS 72 A) R0 (RS 72 A)) (DPNode (MkDag
    0 (bs5 hf3 hcf h3c hf3 hfc) R0 (RS 5 C) (RS 76 E) (RS 5 C)) (DPNode (MkDag 0 (bs5 h3e h79 hfc hbe hfc) R0 R0 R0
    (RS 10 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7e h79 hfc hfe hfc) (RS 36 C) R0 R0 (RS 63 B))
    (DPNode (MkDag 0 (bs5 h7e h79 hfc hbe hfc) (RS 24 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))))) (DPNode (MkDag 0
    (bs5 h9e h7f h3c hf3 hfc) R0 (RS 33 A) R0 (RS 33 A)) (DPNode (MkDag 0 (bs5 hbe h79 hef h97 hfc) R0 (RS 20 C)
    (RS 39 E) R0) (DPNode (MkDag 0 (bs5 h7e h79 h7c hf3 hfc) (RS 35 C) R0 R0 (RS 25 B)) (DPNode (MkDag 0 (bs5 hbe
    h79 h7c hbe hfc) R0 (RS 85 C) (RS 44 E) R0) (DPNode (MkDag 0 (bs5 h9e h7f h2f hbf hfc) R0 (RS 32 A) R0 (RS 32
    A)) (DPNode (MkDag 0 (bs5 h3e h5f h3c hf3 hfc) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hbe
    h79 h7f h97 hfc) R0 (RS 4 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h65 hff h3f hbf hfc) R0 R0 R0 (RS
    50 B)) (DPNode (MkDag 0 (bs5 hfe h79 hf9 hff hfc) R0 (RS 40 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    0 (bs5 hfe h79 h7c hf3 hfc) R0 (RS 18 C) (RS 9 E) (RS 18 C)) (DPNode (MkDag 0 (bs5 hbe h79 hfc hbe hfc) R0 (RS
    77 C) (RS 78 E) R0) (DPNode (MkDag 0 (bs5 h9e h79 h79 hff hfc) R0 (RS 6 A) R0 (RS 6 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 h7e h79 h79 hff hfc) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 0 (bs5 h3e h5f h2f hbf
    hfc) R0 R0 R0 (RS 19 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h7e h79 h7c hfe hfc) R0 R0 R0 (RS 37
    B)) (DPNode (MkDag 0 (bs5 h3e h79 hf9 hff hfc) R0 R0 R0 (RS 2 B)) (DPNode (MkDag 0 (bs5 hfe h79 h7c hfe hfc) R0
    (RS 47 A) R0 (RS 47 A)) (DPNode (MkDag 0 (bs5 h3e h79 he5 hff hfc) R0 R0 R0 (RS 70 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 hdc hff he7 h97 hfc) R0 R0 R0 (RS 54 A)) (DPNode (MkDag 0 (bs5 hfe h79 h7c hbe
    hfc) R0 (RS 12 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hfe h79 he5 hff hfc) R0 (RS 45 C) (RS
    90 E) (RS 45 C)) (DPNode (MkDag 0 (bs5 hbe h79 h7c hfe hfc) R0 (RS 37 C) (RS 91 E) R0) (DPNode (MkDag 0 (bs5
    hfe h79 hfc hbe hfc) R0 (RS 16 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3e h79 he7 h97 hfc)
    R0 R0 R0 (RS 43 B)) (DPNode (MkDag 0 (bs5 hee h79 hfc hbe hfc) (RS 93 D) R0 R0 (RS 94 B)) DPEmpty DPEmpty)
    DPEmpty)))) (DPNode (MkDag 0 (bs5 hfe h7f h2f hbf hfc) R0 (RS 17 C) (RS 84 E) (RS 17 C)) (DPNode (MkDag 0 (bs5
    he7 hcf h3c hf3 hfc) (RS 11 D) R0 R0 (RS 27 A)) (DPNode (MkDag 0 (bs5 hee h79 h7f h97 hfc) R0 R0 R0 (RS 68 B))
    (DPNode (MkDag 0 (bs5 hfe h79 h79 hff hfc) R0 (RS 34 A) (RS 57 E) (RS 34 A)) (DPNode (MkDag 0 (bs5 hbe h79 he5
    hff hfc) R0 (RS 29 C) (RS 69 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 he7 h97 hdc hbe hfc) (RS 51
    D) R0 R0 (RS 52 B)) (DPNode (MkDag 0 (bs5 h3e h7f h2f hbf hfc) R0 R0 R0 (RS 23 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs5 h9e h79 hff h97 hfc) R0 (RS 74 A) R0 (RS 74 A)) (DPNode (MkDag 0 (bs5 hee h79 hfc hfe
    hfc) R0 R0 R0 (RS 62 B)) (DPNode (MkDag 0 (bs5 h9e h79 hfc hfe hfc) R0 (RS 8 A) R0 (RS 8 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 h7e h79 hff h97 hfc) R0 R0 R0 (RS 28 B)) (DPNode (MkDag 0 (bs5 h3e h79 h7c hfe
    hfc) R0 R0 R0 (RS 5 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h9e h79 he5 hff hfc) R0 (RS 22 A) R0
    (RS 22 A)) (DPNode (MkDag 0 (bs5 hee h79 h7c hbe hfc) (RS 23 D) R0 R0 (RS 95 B)) (DPNode (MkDag 0 (bs5 h3e h79
    hef h97 hfc) R0 R0 R0 (RS 93 B)) (DPNode (MkDag 0 (bs5 h9e h79 hfc hbe hfc) R0 (RS 30 A) R0 (RS 30 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfc hff he7 h97 hfc) R0 (RS 18 A) R0 R0) (DPNode (MkDag 0 (bs5 h7e h5f
    h3c hf3 hfc) R0 R0 R0 (RS 36 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f hcf h3c hf3 hfc) R0 (RS
    27 A) R0 (RS 27 A)) (DPNode (MkDag 0 (bs5 h9e h79 hef h97 hfc) R0 (RS 71 A) R0 (RS 71 A)) (DPNode (MkDag 0 (bs5
    hbe h79 hf9 hff hfc) R0 (RS 81 C) (RS 21 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfe h79 hfc hfe
    hfc) R0 (RS 64 C) R0 (RS 64 C)) (DPNode (MkDag 0 (bs5 h7e h79 h7c hbe hfc) (RS 25 C) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty)))))).

Definition dagSub_2_0 : DagPTree :=
  DPNode (MkDag 7 (bs5 h9f hf2 hfc hbe he7) R0 R0 R0 (RS 98 B)) (DPNode (MkDag 12 (bs5 hf2 hf9 he5 hf9 hfc) R0 R0
    (RS 201 E) (RS 202 C)) (DPNode (MkDag 20 (bs5 h77 hfc hbe h7f h3d) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 29 (bs5
    he7 hcb hdc hfe he7) R0 R0 R0 (RS 65 B)) (DPNode (MkDag 10 (bs5 h3c hf9 he5 hf2 hf9) R0 R0 R0 (RS 129 C))
    (DPNode (MkDag 18 (bs5 hbf hb9 h7d hff h3c) R0 R0 (RS 257 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5
    (bs5 h3f hcf h2f h3f h3c) R0 R0 R0 (RS 193 B)) DPEmpty DPEmpty)) (DPNode (MkDag 31 (bs5 h9f hcf h2f h3e he7) R0
    R0 R0 (RS 97 A)) (DPNode (MkDag 46 (bs5 hfe h5e he7 he7 he7) R0 R0 (RS 161 E) (RS 162 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 28 (bs5 h9f hf9 h7b h97 he7) R0 (RS 225 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs5 h7b
    h9f hcb hf2 hfb) R0 R0 R0 (RS 49 B)) (DPNode (MkDag 33 (bs5 hbe h79 h79 hff h2f) R0 R0 (RS 81 E) R0) (DPNode
    (MkDag 19 (bs5 h3e h5e h7f hf9 he7) R0 R0 R0 (RS 145 C)) DPEmpty DPEmpty) (DPNode (MkDag 45 (bs5 h9e h5f hfb
    h97 hdc) R0 R0 R0 (RS 209 A)) DPEmpty DPEmpty)) (DPNode (MkDag 38 (bs5 hfc hf9 hfd hff h3f) R0 R0 R0 (RS 113
    B)) (DPNode (MkDag 9 (bs5 h7e h5e he7 h9e h79) (RS 15 C) R0 R0 (RS 10 B)) DPEmpty DPEmpty) (DPNode (MkDag 4
    (bs5 h7e h7f h2f hff h3c) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 16 (bs5 hf7 hfc hbe h79 hfc) R0
    (RS 25 C) R0 R0) (DPNode (MkDag 11 (bs5 h3e h5e he7 h97 hcb) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 3 (bs5 he7 h97
    he7 hf7 h3f) (RS 72 D) R0 R0 (RS 73 B)) (DPNode (MkDag 18 (bs5 hbe h5f h3c hf9 hfc) R0 (RS 137 C) (RS 138 E)
    R0) DPEmpty DPEmpty) (DPNode (MkDag 41 (bs5 h7c hf2 hf9 hf9 hfc) (RS 16 C) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 3 (bs5 h3d hfe he7 hf7 h3f) R0 R0 R0 (RS 105 C)) (DPNode (MkDag 47 (bs5 hee h7f h3c hbf h3f) (RS 168 D)
    R0 R0 (RS 169 B)) DPEmpty DPEmpty) (DPNode (MkDag 44 (bs5 hbc hf3 hdc hfe hff) R0 R0 (RS 233 E) R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 27 (bs5 hf9 hf7 h3f h9f h2f) (RS 56 D) R0 R0 (RS 57 A)) (DPNode (MkDag 34 (bs5 h97
    hcf he5 hf3 he7) R0 R0 R0 (RS 89 A)) (DPNode (MkDag 44 (bs5 hbc hf3 hfc hfe hff) R0 (RS 153 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 9 (bs5 h9e h5e he7 h9e h79) R0 (RS 14 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs5
    h7c hbf h3c hf3 hfb) R0 R0 R0 (RS 119 B)) (DPNode (MkDag 33 (bs5 hee h5f h2f hbf h2f) (RS 184 D) R0 R0 (RS 185
    B)) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs5 hbe h7e he5 hf3 hfb) R0 R0 (RS 249 E) R0) DPEmpty DPEmpty)))).

Definition dagSub_2_1 : DagPTree :=
  DPNode (MkDag 5 (bs5 h2f hcf h2f h3f h3c) R0 R0 R0 (RS 191 C)) (DPNode (MkDag 13 (bs5 h72 hfc hbf h9e h79) R0 R0
    R0 (RS 19 B)) (DPNode (MkDag 11 (bs5 h7e h5f hcf h2f hcf) (RS 37 C) R0 R0 R0) (DPNode (MkDag 30 (bs5 h3f hbf
    h2f h9e he7) R0 R0 R0 (RS 69 B)) (DPNode (MkDag 2 (bs5 h3f hb9 he5 hf2 hf3) R0 R0 R0 (RS 133 B)) (DPNode (MkDag
    28 (bs5 hff hf9 h7b h97 he7) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 28 (bs5 hfc hf9 h7b
    h97 he7) R0 R0 R0 (RS 197 B)) DPEmpty DPEmpty)) (DPNode (MkDag 36 (bs5 hbc hbf h3c hff h3c) R0 (RS 101 C) R0
    R0) (DPNode (MkDag 1 (bs5 h7e h7f hf9 hff he7) (RS 4 C) R0 R0 (RS 165 B)) DPEmpty DPEmpty) (DPNode (MkDag 27
    (bs5 hf9 he5 he7 hb9 hfb) (RS 228 D) R0 R0 (RS 133 B)) DPEmpty DPEmpty))) (DPNode (MkDag 26 (bs5 hfc hfe h7c
    hf3 hcf) (RS 52 D) R0 R0 (RS 53 B)) (DPNode (MkDag 17 (bs5 h97 hcf h7c hbf h3c) R0 R0 R0 (RS 85 A)) (DPNode
    (MkDag 20 (bs5 h3f hfc hfc hbf h3f) R0 R0 R0 (RS 149 B)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 h9e h7f h2f hff
    h3c) R0 R0 R0 (RS 213 A)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 hf3 he7 he7 h9e h79) (RS 116 D) R0 R0 (RS 117
    C)) (DPNode (MkDag 22 (bs5 h7e h7e he5 hf3 hfb) R0 R0 R0 (RS 181 B)) DPEmpty DPEmpty) (DPNode (MkDag 39 (bs5
    hbe h5f h7c hbf h3f) R0 R0 (RS 245 E) R0) DPEmpty DPEmpty)))) (DPNode (MkDag 18 (bs5 h9e h7c hbe h79 hfc) R0 R0
    R0 (RS 29 A)) (DPNode (MkDag 22 (bs5 h7e h7e he5 he7 hff) R0 R0 R0 (RS 43 B)) (DPNode (MkDag 22 (bs5 hee h79
    he7 hf3 hfb) R0 R0 R0 (RS 77 B)) (DPNode (MkDag 43 (bs5 h7e h5f h3f hb9 he5) R0 R0 R0 (RS 141 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 19 (bs5 hf3 hfe h7f hf9 he7) R0 R0 (RS 205 E) (RS 154 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 3 (bs5 h3f hfe he7 hf7 h3f) R0 R0 R0 (RS 109 B)) (DPNode (MkDag 8 (bs5 hbe h79 he7 hf7 h3f) R0 R0 (RS 9
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hbc hbe h7f h97 h9f) R0 R0 (RS 237 E) R0) DPEmpty DPEmpty)))
    (DPNode (MkDag 5 (bs5 h7f h9f he7 hf7 h3c) R0 R0 R0 (RS 61 B)) (DPNode (MkDag 20 (bs5 h97 hcf h3f hbf hcf) R0
    R0 R0 (RS 93 A)) (DPNode (MkDag 4 (bs5 hfc hfe h7b h97 h9f) (RS 156 D) R0 R0 (RS 157 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h97 hcf h3c hf7 h2f) R0 (RS 0 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 40 (bs5 hfc hf9
    he7 h9f h3c) R0 (RS 125 B) R0 R0) (DPNode (MkDag 5 (bs5 hbd hcf h2f h3f h3c) R0 R0 (RS 189 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 6 (bs5 hbe h79 h7f hf7 h2f) R0 R0 (RS 253 E) R0) DPEmpty DPEmpty)))).

Definition dagSub_2_2 : DagPTree :=
  DPNode (MkDag 9 (bs5 hfe h5e he7 h9e h79) R0 R0 (RS 176 E) (RS 177 C)) (DPNode (MkDag 5 (bs5 h9f hcf h2f h3f h3c)
    R0 R0 R0 (RS 222 A)) (DPNode (MkDag 20 (bs5 h3f hfc hbe h7f h3d) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 20 (bs5 hcf
    hcf hf9 hff hcf) R0 R0 R0 (RS 67 C)) (DPNode (MkDag 2 (bs5 h2f hb9 he5 hf2 hf3) R0 R0 R0 (RS 131 C)) (DPNode
    (MkDag 28 (bs5 hef hf9 h7b h97 he7) R0 R0 R0 (RS 259 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 18 (bs5 he7
    hf9 h7d hff h3c) R0 R0 R0 (RS 195 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 h7f h97 he5 hff he7) (RS 99 D) R0
    R0 R0) (DPNode (MkDag 7 (bs5 hbe h7f hdc hfe he7) R0 R0 (RS 163 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5
    h9f hb9 he5 hf2 hf3) R0 (RS 227 B) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs5 h9f h9f hcb hf2 hfb) R0 (RS
    51 B) R0 R0) (DPNode (MkDag 27 (bs5 he7 hcf h3d hff h2f) R0 R0 R0 (RS 83 A)) (DPNode (MkDag 20 (bs5 h2f hfc hfc
    hbf h3f) R0 R0 R0 (RS 147 C)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs5 h9e h7f hdc hfe he7) R0 R0 R0 (RS 211 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 39 (bs5 hf9 hf3 hfc hbf h3f) R0 R0 R0 (RS 115 A)) (DPNode (MkDag 11 (bs5 h3e
    h7f he7 h9f hcf) R0 R0 R0 (RS 179 B)) DPEmpty DPEmpty) (DPNode (MkDag 47 (bs5 h3e h7f h3c hbf h3f) R0 R0 R0 (RS
    3 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 16 (bs5 hff hfc hbe h79 hfc) R0 (RS 27 C) R0 R0) (DPNode (MkDag 8 (bs5
    h7e h7f he5 hf3 hcf) (RS 43 C) R0 R0 R0) (DPNode (MkDag 2 (bs5 hbe h79 he7 h9f hcb) R0 R0 (RS 75 E) R0) (DPNode
    (MkDag 18 (bs5 h3e h5f h3c hf9 hfc) R0 R0 R0 (RS 139 B)) DPEmpty DPEmpty) (DPNode (MkDag 43 (bs5 hf2 hf7 h3f
    hb9 he5) R0 R0 (RS 203 E) (RS 204 C)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 h2f hfe he7 hf7 h3f) R0 R0 R0 (RS
    107 C)) (DPNode (MkDag 3 (bs5 hfe h7e he7 hf7 h3f) R0 R0 (RS 171 E) (RS 172 C)) DPEmpty DPEmpty) (DPNode (MkDag
    4 (bs5 hbc hbe h7b h97 h9f) R0 R0 (RS 235 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 5 (bs5 h97 h9e he7 hf7 h3c)
    R0 R0 R0 (RS 59 A)) (DPNode (MkDag 28 (bs5 h97 hcf he5 he7 he7) R0 R0 R0 (RS 91 A)) (DPNode (MkDag 4 (bs5 h7c
    hfe h7b h97 h9f) (RS 155 D) R0 R0 (RS 156 B)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 h9e h5f h3c hf3 hfb) R0 R0
    R0 (RS 219 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hff hcf h3c hf7 h2f) R0 (RS 123 C) R0 R0) (DPNode (MkDag
    33 (bs5 hfe h5f h2f hbf h2f) R0 R0 (RS 185 E) (RS 252 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hee h5f h3c
    hf3 hfb) R0 R0 R0 (RS 251 B)) DPEmpty DPEmpty)))).

Definition dagSub_2_3 : DagPTree :=
  DPNode (MkDag 11 (bs5 h9e h7f he7 h9f hcf) R0 R0 R0 (RS 217 A)) (DPNode (MkDag 15 (bs5 h97 hdc hbe h79 h7b) R0 R0
    R0 (RS 23 A)) (DPNode (MkDag 21 (bs5 h7e h5f he7 hf3 hcf) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 31 (bs5 h7f hf7
    h2f h3e he7) (RS 7 C) R0 R0 R0) (DPNode (MkDag 42 (bs5 hbe h79 h7f hf9 hfc) R0 (RS 135 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 27 (bs5 hbf he5 he7 hb9 hfb) R0 (RS 199 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 37
    (bs5 he5 hf7 h3f h3f h3c) (RS 102 D) R0 R0 (RS 103 C)) (DPNode (MkDag 4 (bs5 hbe h7f h2f hff h3c) R0 R0 (RS 167
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs5 h79 hf2 hff hcf hcf) R0 R0 R0 (RS 231 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 6 (bs5 hcf h9f h3c hff h2f) R0 R0 R0 (RS 55 A)) (DPNode (MkDag 17 (bs5 h97 hcf hfc hbf h3c) R0
    R0 R0 (RS 87 A)) (DPNode (MkDag 39 (bs5 h7f h97 he7 h97 hff) (RS 151 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 8 (bs5 h9e h79 he7 hf7 h3f) R0 (RS 215 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 38 (bs5 h73 hf3 he5
    hf3 hcf) R0 R0 R0 (RS 117 B)) (DPNode (MkDag 4 (bs5 hbe h5f h3c hf3 hfb) R0 R0 (RS 183 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 9 (bs5 hee h5e he7 h9e h79) R0 R0 R0 (RS 176 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 19 (bs5 h9f
    hdc hbe h79 he7) R0 R0 R0 (RS 31 C)) (DPNode (MkDag 23 (bs5 hf9 h79 hf9 h7d hcf) R0 (RS 47 C) R0 R0) (DPNode
    (MkDag 4 (bs5 hfe h79 h7c hf3 hfb) R0 R0 (RS 79 E) (RS 80 C)) (DPNode (MkDag 19 (bs5 hbe h5e h7f hf9 he7) R0
    (RS 143 C) (RS 144 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hbc hfe h7f h97 h9f) R0 (RS 207 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5 he7 hf9 he7 hf7 h3f) R0 R0 R0 (RS 111 B)) (DPNode (MkDag 39 (bs5 hee
    h5f h7c hbf h3f) (RS 174 D) R0 R0 (RS 175 B)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs5 hbf hfb hfc hf9 hfd) R0
    (RS 239 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 28 (bs5 hbf hcb he7 he7 he7) R0 R0 (RS 63 E) R0) (DPNode
    (MkDag 35 (bs5 h97 h9f h97 hfe h7b) R0 R0 R0 (RS 95 A)) (DPNode (MkDag 45 (bs5 h5e h5f hfb h97 hdc) (RS 159 B)
    R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 18 (bs5 h97 hb9 h7d hff h3c) R0 (RS 223 A) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 18 (bs5 hf9 hf9 h7d hff h3c) (RS 126 D) R0 R0 (RS 127 C)) (DPNode (MkDag 5 (bs5 haf hcf h2f h3f
    h3c) R0 R0 (RS 12 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 he7 hcf h3c hf7 h2f) R0 R0 R0 (RS 255 B))
    DPEmpty DPEmpty)))).

Definition dagSub_2_4 : DagPTree :=
  DPNode (MkDag 8 (bs5 h3e h79 he7 hf7 h3f) R0 R0 R0 (RS 174 B)) (DPNode (MkDag 3 (bs5 h9e h7e he7 hf7 h3f) R0 R0
    R0 (RS 214 A)) (DPNode (MkDag 20 (bs5 hbf hfc hbe h7f h3d) R0 R0 (RS 34 E) R0) (DPNode (MkDag 20 (bs5 h7d hcf
    hf9 hff hcf) (RS 66 D) R0 R0 R0) (DPNode (MkDag 2 (bs5 haf hb9 he5 hf2 hf3) R0 R0 (RS 130 E) R0) (DPNode (MkDag
    18 (bs5 h3f hb9 h7d hff h3c) R0 R0 R0 (RS 258 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 18 (bs5 he7 hb9 h7d
    hff h3c) R0 R0 R0 (RS 194 B)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs5 h97 hf2 hfc hbe he7) R0 (RS 8 A) R0 R0)
    (DPNode (MkDag 46 (bs5 h7e h5e he7 he7 he7) R0 R0 R0 (RS 160 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h97 hb9
    he5 hf2 hf3) R0 R0 R0 (RS 226 A)) DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs5 hfb h9f hcb hf2 hfb) (RS 49 D) R0
    R0 (RS 50 A)) (DPNode (MkDag 33 (bs5 h3e h79 h79 hff h2f) R0 R0 R0 (RS 82 B)) (DPNode (MkDag 20 (bs5 haf hfc
    hfc hbf h3f) R0 R0 (RS 146 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 46 (bs5 h9e h5e he7 he7 he7) R0 (RS 210 A) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 39 (bs5 h79 hf3 hfc hbf h3f) R0 R0 R0 (RS 114 B)) (DPNode (MkDag 11 (bs5
    hbe h7f he7 h9f hcf) R0 R0 (RS 178 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 47 (bs5 hbe h7f h3c hbf h3f) R0 R0
    (RS 242 E) R0) DPEmpty DPEmpty)))) (DPNode (MkDag 16 (bs5 hbf hfc hbe h79 hfc) R0 (RS 26 C) R0 R0) (DPNode
    (MkDag 8 (bs5 hee h7f he5 hf3 hcf) (RS 41 D) R0 R0 (RS 42 B)) (DPNode (MkDag 32 (bs5 h7c hf3 hcf hff h3f) (RS
    74 C) R0 R0 R0) (DPNode (MkDag 18 (bs5 hfe h5f h3c hf9 hfc) R0 (RS 229 C) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 12 (bs5 h72 hf9 he5 hf9 hfc) R0 R0 R0 (RS 16 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 haf hfe he7 hf7
    h3f) R0 R0 (RS 106 E) R0) (DPNode (MkDag 47 (bs5 h7e h7f h3c hbf h3f) (RS 170 C) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 44 (bs5 h3c hf3 hdc hfe hff) R0 R0 R0 (RS 234 C)) DPEmpty DPEmpty))) (DPNode (MkDag 27 (bs5 h9f
    h3f h3f h9f h2f) R0 (RS 58 A) R0 R0) (DPNode (MkDag 34 (bs5 h9f hcf he5 hf3 he7) R0 (RS 90 A) R0 R0) (DPNode
    (MkDag 44 (bs5 hfc hf3 hfc hfe hff) R0 (RS 154 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs5 h9e h7e he5
    hf3 hfb) R0 (RS 218 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbf hcf h3c hf7 h2f) R0 (RS 122 C) R0 R0)
    (DPNode (MkDag 33 (bs5 h7e h5f h2f hbf h2f) (RS 11 C) R0 R0 (RS 186 B)) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs5
    h3e h7e he5 hf3 hfb) R0 R0 R0 (RS 250 B)) DPEmpty DPEmpty)))).

Definition dagSub_2_5 : DagPTree :=
  DPNode (MkDag 10 (bs5 hf9 hf9 he5 hf2 hf9) R0 R0 R0 (RS 198 A)) (DPNode (MkDag 14 (bs5 h9e h7c hbe h79 hff) R0
    (RS 22 A) R0 R0) (DPNode (MkDag 21 (bs5 hfe h5f he7 hf3 hcf) R0 R0 (RS 38 E) (RS 39 C)) (DPNode (MkDag 31 (bs5
    hef hf7 h2f h3e he7) R0 R0 R0 (RS 70 B)) (DPNode (MkDag 41 (bs5 he5 hf2 hf9 hf9 hfc) (RS 133 D) R0 R0 (RS 134
    A)) DPEmpty DPEmpty) (DPNode (MkDag 10 (bs5 h79 hf9 he5 hf2 hf9) R0 R0 R0 (RS 13 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 36 (bs5 hfc hbf h3c hff h3c) (RS 101 D) R0 R0 (RS 102 B)) (DPNode (MkDag 1 (bs5 hfe h7f hf9 hff he7) R0
    R0 R0 (RS 166 C)) DPEmpty DPEmpty) (DPNode (MkDag 43 (bs5 hbe h5f h3f hb9 he5) R0 (RS 141 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 13 (bs5 h7c hfc hfc hbe hf9) (RS 54 D) R0 R0 R0) (DPNode (MkDag 17 (bs5 h9f hcf h7c
    hbf h3c) R0 (RS 86 A) R0 R0) (DPNode (MkDag 39 (bs5 hef h97 he7 h97 hff) (RS 149 D) R0 R0 (RS 150 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 47 (bs5 h9e h7f h3c hbf h3f) R0 (RS 17 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 38
    (bs5 hf3 hf3 he5 hf3 hcf) R0 R0 (RS 118 E) (RS 119 C)) (DPNode (MkDag 22 (bs5 hfe h7e he5 hf3 hfb) R0 R0 R0 (RS
    182 C)) DPEmpty DPEmpty) (DPNode (MkDag 39 (bs5 h3e h5f h7c hbf h3f) R0 R0 R0 (RS 246 B)) DPEmpty DPEmpty))))
    (DPNode (MkDag 19 (bs5 h97 hdc hbe h79 he7) R0 (RS 30 A) R0 R0) (DPNode (MkDag 23 (bs5 hb9 h79 hf9 h7d hcf) R0
    (RS 46 C) R0 R0) (DPNode (MkDag 22 (bs5 h7e h79 he7 hf3 hfb) (RS 78 C) R0 R0 R0) (DPNode (MkDag 43 (bs5 hfe h5f
    h3f hb9 he5) R0 (RS 142 C) R0 (RS 142 C)) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs5 h73 hfe h7f hf9 he7) R0 R0 R0
    (RS 204 B)) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5 he7 hb9 he7 hf7 h3f) R0 R0 R0 (RS 110 B)) (DPNode (MkDag 8
    (bs5 hfe h79 he7 hf7 h3f) R0 R0 (RS 243 E) (RS 244 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 h3c hbe h7f h97
    h9f) R0 R0 R0 (RS 238 A)) DPEmpty DPEmpty))) (DPNode (MkDag 5 (bs5 hff h9f he7 hf7 h3c) (RS 61 D) R0 R0 (RS 62
    C)) (DPNode (MkDag 20 (bs5 h9f hcf h3f hbf hcf) R0 (RS 94 A) R0 R0) (DPNode (MkDag 4 (bs5 h7c hfe h7f h97 h9f)
    (RS 158 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs5 h97 hcf h2f h3f h3c) R0 (RS 18 A) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 18 (bs5 h79 hf9 h7d hff h3c) R0 R0 R0 (RS 126 B)) (DPNode (MkDag 5 (bs5 h3d hcf h2f
    h3f h3c) R0 R0 R0 (RS 190 C)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5 h3e h79 h7f hf7 h2f) R0 R0 R0 (RS 254 B))
    DPEmpty DPEmpty)))).

Definition dagSub_2_6 : DagPTree :=
  DPNode (MkDag 6 (bs5 hfe h79 h7f hf7 h2f) R0 R0 (RS 187 E) (RS 188 C)) (DPNode (MkDag 13 (bs5 hf2 hfc hbf h9e
    h79) R0 R0 (RS 20 E) (RS 21 A)) (DPNode (MkDag 11 (bs5 hee h5f hcf h2f hcf) (RS 35 D) R0 R0 (RS 36 B)) (DPNode
    (MkDag 30 (bs5 hbf hbf h2f h9e he7) R0 R0 (RS 68 E) R0) (DPNode (MkDag 2 (bs5 hbf hb9 he5 hf2 hf3) R0 R0 (RS
    132 E) R0) (DPNode (MkDag 28 (bs5 h7f hf9 h7b h97 he7) R0 R0 R0 (RS 260 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 28 (bs5 h7c hf9 h7b h97 he7) R0 R0 R0 (RS 196 B)) DPEmpty DPEmpty)) (DPNode (MkDag 36 (bs5 hdc hbf h3c
    hff h3c) R0 R0 R0 (RS 100 A)) (DPNode (MkDag 7 (bs5 h3e h7f hdc hfe he7) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 27 (bs5 h79 he5 he7 hb9 hfb) R0 R0 R0 (RS 228 B)) DPEmpty DPEmpty))) (DPNode (MkDag 26 (bs5 h7c
    hfe h7c hf3 hcf) R0 R0 R0 (RS 52 B)) (DPNode (MkDag 16 (bs5 h9e h79 h7d hff h3c) R0 (RS 84 A) R0 R0) (DPNode
    (MkDag 20 (bs5 hbf hfc hfc hbf h3f) R0 R0 (RS 148 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h9e h7f hf9 hff
    he7) R0 (RS 212 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 h9f h3e he7 h9e h79) R0 (RS 116 C) R0 R0)
    (DPNode (MkDag 22 (bs5 hee h7e he5 hf3 hfb) R0 R0 R0 (RS 180 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs5 h7e h79
    he7 hf7 h3f) R0 R0 R0 (RS 173 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 17 (bs5 hf2 hfc hbe h79 hfc) R0 (RS 28 A)
    R0 R0) (DPNode (MkDag 22 (bs5 hfe h7e he5 he7 hff) R0 R0 (RS 44 E) (RS 45 A)) (DPNode (MkDag 2 (bs5 h3e h79 he7
    h9f hcb) R0 R0 R0 (RS 76 B)) (DPNode (MkDag 43 (bs5 hee h5f h3f hb9 he5) R0 R0 R0 (RS 140 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 43 (bs5 h72 hf7 h3f hb9 he5) R0 R0 R0 (RS 202 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 hbf
    hfe he7 hf7 h3f) R0 R0 (RS 108 E) R0) (DPNode (MkDag 3 (bs5 h7e h7e he7 hf7 h3f) (RS 173 C) R0 R0 (RS 170 B))
    DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 h3c hbe h7b h97 h9f) R0 R0 R0 (RS 236 C)) DPEmpty DPEmpty))) (DPNode
    (MkDag 5 (bs5 h9f h9e he7 hf7 h3c) R0 (RS 60 B) R0 R0) (DPNode (MkDag 28 (bs5 h9f hcf he5 he7 he7) R0 (RS 92 A)
    R0 R0) (DPNode (MkDag 4 (bs5 hdc hfe h7f h97 h9f) R0 R0 R0 (RS 206 A)) DPEmpty DPEmpty) (DPNode (MkDag 33 (bs5
    h9e h5f h2f hbf h2f) R0 (RS 6 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 40 (bs5 hbc hf9 he7 h9f h3c) R0 (RS
    124 C) R0 R0) (DPNode (MkDag 6 (bs5 h7e h79 h7f hf7 h2f) R0 R0 R0 (RS 11 B)) DPEmpty DPEmpty) (DPNode (MkDag 4
    (bs5 h7e h5f h3c hf3 hfb) (RS 186 C) R0 R0 R0) DPEmpty DPEmpty)))).

Definition dagSub_2_7 : DagPTree :=
  DPNode (MkDag 11 (bs5 hfe h7f he7 h9f hcf) R0 R0 (RS 247 E) (RS 248 C)) (DPNode (MkDag 15 (bs5 h9f hdc hbe h79
    h7b) R0 (RS 24 C) R0 R0) (DPNode (MkDag 11 (bs5 hbe h5e he7 h97 hcb) R0 R0 (RS 40 E) R0) (DPNode (MkDag 4 (bs5
    h7f hf7 h3f h9f h3c) R0 R0 R0 (RS 7 B)) (DPNode (MkDag 42 (bs5 hfe h79 h7f hf9 hfc) (RS 135 D) (RS 136 C) R0
    (RS 136 C)) DPEmpty DPEmpty) (DPNode (MkDag 27 (bs5 hff he5 he7 hb9 hfb) (RS 199 D) R0 R0 (RS 200 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 3 (bs5 hbd hfe he7 hf7 h3f) R0 R0 (RS 104 E) R0) (DPNode (MkDag 4 (bs5 h3e h7f h2f hff
    h3c) R0 R0 R0 (RS 168 B)) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs5 hf9 hf2 hff hcf hcf) (RS 231 D) R0 R0 (RS 232
    C)) DPEmpty DPEmpty))) (DPNode (MkDag 27 (bs5 hb9 hf7 h3f h9f h2f) R0 (RS 56 C) R0 R0) (DPNode (MkDag 17 (bs5
    h9f hcf hfc hbf h3c) R0 (RS 88 A) R0 R0) (DPNode (MkDag 44 (bs5 hdc hf3 hfc hfe hff) R0 R0 R0 (RS 152 A))
    DPEmpty DPEmpty) (DPNode (MkDag 39 (bs5 h9e h5f h7c hbf h3f) R0 R0 R0 (RS 216 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 4 (bs5 hfc hbf h3c hf3 hfb) R0 R0 (RS 120 E) (RS 121 A)) (DPNode (MkDag 4 (bs5 h3e h5f h3c hf3 hfb) R0
    R0 R0 (RS 184 B)) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs5 h7e h7f he7 h9f hcf) R0 R0 R0 (RS 15 B)) DPEmpty
    DPEmpty)))) (DPNode (MkDag 20 (bs5 hf7 hfc hbe h7f h3d) R0 R0 (RS 32 E) (RS 33 C)) (DPNode (MkDag 24 (bs5 hff
    h9e hff h9f h9f) R0 (RS 48 B) R0 R0) (DPNode (MkDag 4 (bs5 h7e h79 h7c hf3 hfb) R0 R0 R0 (RS 78 B)) (DPNode
    (MkDag 19 (bs5 hfe h5e h7f hf9 he7) R0 (RS 230 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hfc hfe h7f h97
    h9f) R0 (RS 208 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 38 (bs5 h7c hf9 hfd hff h3f) R0 R0 R0 (RS 112 B))
    (DPNode (MkDag 39 (bs5 h7e h5f h7c hbf h3f) (RS 10 C) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs5 hff hfb
    hfc hf9 hfd) (RS 239 D) R0 R0 (RS 160 C)) DPEmpty DPEmpty))) (DPNode (MkDag 28 (bs5 h3f hcb he7 he7 he7) R0 R0
    R0 (RS 64 B)) (DPNode (MkDag 35 (bs5 h9f h9f h97 hfe h7b) R0 (RS 96 A) R0 R0) (DPNode (MkDag 45 (bs5 h7e h5f
    hfb h97 hdc) (RS 160 C) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 18 (bs5 h9f hb9 h7d hff h3c) R0 R0 R0 (RS 224
    A)) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 hbc hf9 he5 hf2 hf9) R0 R0 (RS 128 E) R0) (DPNode (MkDag 5 (bs5
    hbf hcf h2f h3f h3c) R0 R0 (RS 192 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs5 h7d hcf h2f h3f h3c) (RS 5 D)
    R0 R0 R0) DPEmpty DPEmpty)))).

Definition dagTree_2 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h9f hcf h3c hf7 h2f) R0 R0 R0 (RS 221 A)) (DPNode (MkDag 1 (bs5 hee h7f hf9 hff he7) R0
    R0 R0 (RS 164 B)) (DPNode (MkDag 2 (bs5 he5 hf9 he5 hf2 hf3) R0 R0 R0 (RS 198 A)) (DPNode (MkDag 4 (bs5 hfe h7f
    h2f hff h3c) R0 R0 (RS 240 E) (RS 241 C)) dagSub_2_0 dagSub_2_1) (DPNode (MkDag 6 (bs5 h9e h79 h7f hf7 h2f) R0
    R0 R0 (RS 220 A)) dagSub_2_2 dagSub_2_3)) (DPNode (MkDag 3 (bs5 hee h7e he7 hf7 h3f) R0 R0 R0 (RS 171 B))
    (DPNode (MkDag 5 (bs5 hcf hcf h2f h3f h3c) R0 R0 R0 (RS 256 C)) dagSub_2_4 dagSub_2_5) (DPNode (MkDag 4 (bs5
    hff hf7 h3f h9f h3c) R0 R0 (RS 71 E) (RS 72 B)) dagSub_2_6 dagSub_2_7))).

Definition dagTree_3 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h9e h7f he7 hf3 hfb) R0 R0 R0 (RS 110 A)) (DPNode (MkDag 1 (bs5 h9f hdf h3c hff he5) R0
    R0 R0 (RS 111 A)) (DPNode (MkDag 2 (bs5 he7 h9f hcb hf3 hf9) R0 R0 R0 (RS 109 A)) (DPNode (MkDag 4 (bs5 h7f hcb
    hff h97 he7) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 6 (bs5 hee h5e he7 hf3 hcf) (RS 8 D) R0 R0 (RS 77 B)) (DPNode
    (MkDag 8 (bs5 h3c hff hff h9e h5f) R0 R0 R0 (RS 17 C)) (DPNode (MkDag 4 (bs5 hff hcb hff h97 he7) R0 R0 R0 (RS
    33 C)) (DPNode (MkDag 15 (bs5 hf3 hff h3f h3e he7) R0 (RS 65 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5
    hcf h9f h3f h9e he7) R0 R0 R0 (RS 97 A)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hf9 hff hcb hf3 hf9) R0 R0 R0
    (RS 49 C)) (DPNode (MkDag 1 (bs5 hbc hff h3c hff he5) R0 R0 (RS 81 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 12 (bs5 h3c hfe h7f h73 hf7) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 18 (bs5 haf hf3 hf9 he7 hff) R0 R0 (RS
    41 E) R0) (DPNode (MkDag 5 (bs5 hbf h9f hff hf3 hff) R0 R0 (RS 7 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5
    h79 hf7 h3f h9f he7) (RS 105 B) R0 R0 (RS 98 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 h7d hcf h3c hff he5)
    (RS 6 D) R0 R0 R0) (DPNode (MkDag 3 (bs5 h3f h3f h3f h9f he7) R0 R0 R0 (RS 89 B)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 7 (bs5 he5 hfc hbf h97 hcf) (RS 12 D) R0 R0 (RS 13 C)) (DPNode (MkDag 10 (bs5 h3c hf3 hf3 hff
    h9f) R0 R0 R0 (RS 21 C)) (DPNode (MkDag 16 (bs5 hfe h7f he7 hf3 he7) R0 R0 (RS 37 E) (RS 38 C)) (DPNode (MkDag
    15 (bs5 hbc hff h3f h3e he7) R0 R0 (RS 69 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs5 h97 h9f hff hf3 hff) R0
    (RS 101 A) R0 (RS 101 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h2f hcb he7 hf3 hfb) R0 R0 R0 (RS 53 C))
    (DPNode (MkDag 3 (bs5 hbf h9f h3f h9e he7) R0 R0 (RS 9 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs5
    h2f h9f he5 hf3 hfb) R0 R0 R0 (RS 29 C)) (DPNode (MkDag 3 (bs5 he7 hcf h3f h9e he7) R0 R0 R0 (RS 45 B)) (DPNode
    (MkDag 2 (bs5 h3f h9f hcb hf3 hf9) R0 R0 R0 (RS 8 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h67 h9f hcb hf3
    hf9) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbc hff he7 hf3 hfb) R0 R0 (RS 61 E) R0)
    (DPNode (MkDag 0 (bs5 hbe h7f he7 hf3 hfb) R0 R0 (RS 93 E) R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 1
    (bs5 hcf hcf h3c hff he5) R0 R0 R0 (RS 57 C)) (DPNode (MkDag 6 (bs5 hfe h5e he7 hf3 hcf) (RS 10 D) R0 (RS 77 E)
    (RS 92 C)) (DPNode (MkDag 9 (bs5 h3c hf3 hf9 he7 hcf) R0 R0 R0 (RS 19 C)) (DPNode (MkDag 15 (bs5 h3e h5f he5
    hff he7) R0 R0 R0 (RS 5 B)) (DPNode (MkDag 15 (bs5 hbc hf7 h3f h3e he7) R0 R0 (RS 67 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 3 (bs5 hf9 hf7 h3f h9f he7) R0 (RS 99 A) R0 (RS 99 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5
    h3d hcb he7 hf3 hfb) R0 R0 R0 (RS 51 C)) (DPNode (MkDag 3 (bs5 haf h9f h3f h9e he7) R0 R0 (RS 83 E) R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 13 (bs5 h3c hfc hff hf2 hf9) R0 R0 R0 (RS 27 C)) (DPNode (MkDag 18 (bs5 hbf
    hf3 hf9 he7 hff) R0 R0 (RS 43 E) R0) (DPNode (MkDag 2 (bs5 h2f h9f hcb hf3 hf9) R0 R0 R0 (RS 75 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 hee h7f he7 hf3 hfb) R0 R0 R0 (RS 79 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5
    h3f hcf h3f h9f he7) R0 R0 R0 (RS 59 B)) (DPNode (MkDag 6 (bs5 hbe h5e he7 hf3 hcf) R0 (RS 10 C) (RS 91 E) R0)
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs5 h3c hf7 hff h9e h5f) R0 R0 R0 (RS 15 C)) (DPNode (MkDag 11
    (bs5 h3c hfe h79 hf3 hfb) R0 R0 R0 (RS 23 C)) (DPNode (MkDag 17 (bs5 hbe h7e hff h9e h7f) R0 R0 (RS 39 E) R0)
    (DPNode (MkDag 5 (bs5 haf h9f hff hf3 hff) R0 R0 (RS 71 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h7f h9f
    hcb hf3 hf9) (RS 10 C) R0 R0 (RS 103 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h3f hcb he7 hf3 hfb) R0 R0 R0
    (RS 55 B)) (DPNode (MkDag 3 (bs5 h2f h3f h3f h9f he7) R0 R0 R0 (RS 87 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 14 (bs5 h3f h9f he5 hf3 hfb) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 15 (bs5 hfd hcf h3f h3e he7) R0 R0 R0
    (RS 47 B)) (DPNode (MkDag 0 (bs5 hfe h7f he7 hf3 hfb) R0 R0 (RS 79 E) (RS 80 C)) DPEmpty DPEmpty) (DPNode
    (MkDag 1 (bs5 h97 hdf h3c hff he5) R0 (RS 1 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 hb2 hf7 h3f h9f
    he7) R0 (RS 63 C) R0 R0) (DPNode (MkDag 1 (bs5 he7 hdf h3c hff he5) R0 R0 R0 (RS 95 B)) DPEmpty DPEmpty)
    DPEmpty))))) (DPNode (MkDag 3 (bs5 h9f h9f h3f h9e he7) R0 R0 R0 (RS 107 B)) (DPNode (MkDag 2 (bs5 hee h5e he7
    h9f hf9) (RS 5 D) R0 R0 (RS 35 B)) (DPNode (MkDag 3 (bs5 h3f h9f h3f h9e he7) R0 R0 R0 (RS 85 C)) (DPNode
    (MkDag 9 (bs5 hbc hf3 hf9 he7 hcf) R0 R0 (RS 18 E) R0) (DPNode (MkDag 15 (bs5 hbe h5f he5 hff he7) R0 R0 (RS 34
    E) R0) (DPNode (MkDag 3 (bs5 he5 hff h3f h9e he7) R0 R0 R0 (RS 66 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5
    hb9 hf7 h3f h9f he7) R0 (RS 98 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbd hcb he7 hf3 hfb) R0 R0 (RS
    50 E) R0) (DPNode (MkDag 1 (bs5 h3c hff h3c hff he5) R0 R0 R0 (RS 82 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 13 (bs5 hbc hfc hff hf2 hf9) R0 R0 (RS 26 E) R0) (DPNode (MkDag 18 (bs5 h2f hf3 hf9 he7 hff) R0 R0 R0
    (RS 42 C)) (DPNode (MkDag 2 (bs5 haf h9f hcb hf3 hf9) R0 R0 (RS 74 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3
    (bs5 h5f h3f h3f h9f he7) (RS 107 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 hbf hcf h3f h9f he7) R0
    R0 (RS 58 E) R0) (DPNode (MkDag 5 (bs5 he7 h9f hff hf3 hff) (RS 89 D) R0 R0 (RS 90 A)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 8 (bs5 hbc hf7 hff h9e h5f) R0 R0 (RS 14 E) R0) (DPNode (MkDag 11 (bs5 hbc hfe h79
    hf3 hfb) R0 R0 (RS 22 E) R0) (DPNode (MkDag 16 (bs5 h7e h7f he7 hf3 he7) R0 R0 R0 (RS 36 B)) (DPNode (MkDag 15
    (bs5 h3c hff h3f h3e he7) R0 R0 R0 (RS 70 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs5 h9f h9f hff hf3 hff) R0
    (RS 102 B) R0 (RS 102 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbf hcb he7 hf3 hfb) R0 R0 (RS 54 E) R0)
    (DPNode (MkDag 3 (bs5 haf h3f h3f h9f he7) R0 R0 (RS 86 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14
    (bs5 hbf h9f he5 hf3 hfb) R0 R0 (RS 30 E) R0) (DPNode (MkDag 15 (bs5 h7d hcf h3f h3e he7) R0 R0 R0 (RS 46 B))
    (DPNode (MkDag 6 (bs5 h7e h5e he7 hf3 hcf) (RS 78 C) R0 R0 (RS 10 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5
    h9e h5e he7 hf3 hcf) R0 (RS 0 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h3c hff he7 hf3 hfb) R0 R0 R0
    (RS 62 A)) (DPNode (MkDag 0 (bs5 h3e h7f he7 hf3 hfb) R0 R0 R0 (RS 94 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 5 (bs5 h3f h9f hff hf3 hff) R0 R0 R0 (RS 73 C)) (DPNode (MkDag 1 (bs5 hfc hff h3c hff he5) R0 R0 (RS 95
    E) (RS 104 B)) (DPNode (MkDag 10 (bs5 hbc hf3 hf3 hff h9f) R0 R0 (RS 20 E) R0) (DPNode (MkDag 2 (bs5 h7e h5e
    he7 h9f hf9) (RS 36 C) R0 R0 R0) (DPNode (MkDag 15 (bs5 h3c hf7 h3f h3e he7) R0 R0 R0 (RS 68 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs5 h9f h3f h3f h9f he7) R0 (RS 100 A) R0 (RS 100 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 haf hcb he7 hf3 hfb) R0 R0 (RS 52 E) R0) (DPNode (MkDag 3 (bs5 h2f h9f h3f h9e he7) R0 R0 R0 (RS
    84 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs5 haf h9f he5 hf3 hfb) R0 R0 (RS 28 E) R0) (DPNode
    (MkDag 18 (bs5 h3f hf3 hf9 he7 hff) R0 R0 R0 (RS 44 B)) (DPNode (MkDag 2 (bs5 hbf h9f hcb hf3 hf9) R0 R0 (RS 76
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 h7f h3f h3f h9f he7) (RS 108 E) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 5 (bs5 he7 hcf hff hf3 hff) R0 R0 R0 (RS 60 C)) (DPNode (MkDag 6 (bs5 h3e h5e he7 hf3 hcf) R0 R0
    R0 (RS 106 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs5 hbc hff hff h9e h5f) R0 R0 (RS 16 E) R0)
    (DPNode (MkDag 12 (bs5 hbc hfe h7f h73 hf7) R0 R0 (RS 24 E) R0) (DPNode (MkDag 17 (bs5 h3e h7e hff h9e h7f) R0
    R0 R0 (RS 40 C)) (DPNode (MkDag 5 (bs5 h2f h9f hff hf3 hff) R0 R0 R0 (RS 72 C)) DPEmpty DPEmpty) (DPNode (MkDag
    2 (bs5 hff h9f hcb hf3 hf9) (RS 103 D) R0 R0 (RS 90 C)) DPEmpty DPEmpty)) (DPNode (MkDag 18 (bs5 he7 hcb he7
    he7 hff) (RS 55 D) R0 R0 (RS 56 B)) (DPNode (MkDag 3 (bs5 hbf h3f h3f h9f he7) R0 R0 (RS 88 E) R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 4 (bs5 hef hcb hff h97 he7) R0 R0 R0 (RS 4 B)) (DPNode (MkDag 2 (bs5 h79 hff
    hcb hf3 hf9) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 0 (bs5 h7e h7f he7 hf3 hfb) (RS 11 C) R0 R0 (RS 78 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs5 h97 h9f h3f h9e he7) R0 (RS 3 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5
    hf2 hf7 h3f h9f he7) R0 (RS 64 C) R0 R0) (DPNode (MkDag 1 (bs5 h7c hff h3c hff he5) (RS 96 D) R0 R0 (RS 11 B))
    DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_4 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 hcb he5 he7 hff) (RS 0 D) R0 R0 (RS 1 D)) (DPNode (MkDag 1 (bs4 hcf h3c hbe hff) R0 R0
    R0 (RS 2 D)) (DPNode (MkDag 2 (bs4 hcf he7 hbe h5f) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 1 (bs4 hcf he7 hf2 hfb)
    R0 R0 R0 (RS 5 D)) (DPNode (MkDag 2 (bs4 hcf he7 he7 hff) R0 R0 R0 (RS 9 D)) (DPNode (MkDag 1 (bs4 hcf he7 hfe
    h5f) R0 R0 R0 (RS 17 D)) (DPNode (MkDag 10 (bs4 h7f h3e h79 h7b) (RS 33 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 3 (bs4 hcb he5 hf3 hcf) R0 R0 R0 (RS 25 D)) (DPNode (MkDag 0 (bs4 h97 hdf h9e h5f) R0 R0 R0 (RS
    41 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs4 hcb he5 hf3 hfb) R0 R0 R0 (RS 13 D)) (DPNode (MkDag 0
    (bs4 hcf he7 hf3 hfb) R0 R0 R0 (RS 21 D)) (DPNode (MkDag 2 (bs4 h7f hf9 hff h9f) R0 R0 R0 (RS 35 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs4 h9e h79 he7 hcf) R0 (RS 29 A) R0 R0) (DPNode (MkDag 3 (bs4 hff hcb hf3
    hfb) R0 (RS 0 D) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 1 (bs4 hcf he7 hf3 hcf) R0 R0 R0 (RS 7 D))
    (DPNode (MkDag 1 (bs4 hcb he7 h97 hff) R0 R0 R0 (RS 11 D)) (DPNode (MkDag 3 (bs4 hcf he7 h9e h5f) R0 R0 R0 (RS
    19 D)) (DPNode (MkDag 11 (bs4 h7e h7e h7f h3f) (RS 35 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4
    (bs4 h9f hcb hee h79) R0 (RS 27 A) R0 R0) (DPNode (MkDag 3 (bs4 hf7 hcb hf3 hfb) R0 (RS 43 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs4 hcf h3c hbe hff) R0 R0 R0 (RS 15 D)) (DPNode (MkDag 3 (bs4 hcf hdc hbe
    hff) R0 R0 R0 (RS 23 D)) (DPNode (MkDag 2 (bs4 h9e h79 hfe h5f) R0 R0 R0 (RS 39 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 8 (bs4 h9e h5e he5 hf3) R0 (RS 31 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs4 hcf he7
    hfe h5f) R0 R0 R0 (RS 4 D)) (DPNode (MkDag 0 (bs4 hcf he7 h9e h5f) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 0 (bs4 hcf
    hdc hbe hff) R0 R0 R0 (RS 10 D)) (DPNode (MkDag 2 (bs4 hcf he7 hf2 hfb) R0 R0 R0 (RS 18 D)) (DPNode (MkDag 11
    (bs4 h5e h7e h7f h3f) (RS 34 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs4 hcb he5 hf3 hfb) R0
    R0 R0 (RS 0 D)) (DPNode (MkDag 0 (bs4 h9f hdf h9e h5f) R0 (RS 42 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 3 (bs4 hcb he5 he7 hff) R0 R0 R0 (RS 14 D)) (DPNode (MkDag 1 (bs4 hcf he7 he7 hff) R0 R0 R0 (RS 22 D))
    (DPNode (MkDag 3 (bs4 h9f hf9 hf3 hcf) R0 (RS 38 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs4 h9e
    h5f h7c hbf) R0 R0 R0 (RS 30 A)) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs4 hcf he7 hf3 hfb) R0 R0 R0 (RS 8 D))
    (DPNode (MkDag 0 (bs4 hcb he5 hf3 hcf) R0 R0 R0 (RS 12 D)) (DPNode (MkDag 2 (bs4 hcf he7 hf3 hcf) R0 R0 R0 (RS
    20 D)) (DPNode (MkDag 2 (bs4 hff hf9 hff h9f) R0 R0 (RS 36 E) (RS 37 A)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 5 (bs4 h9e h5f hfd hcf) R0 R0 R0 (RS 28 A)) (DPNode (MkDag 3 (bs4 hbf hcb hf3 hfb) R0 (RS 44 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs4 hcf he7 hbe h5f) R0 R0 R0 (RS 16 D)) (DPNode (MkDag 2 (bs4 hcb
    he7 h97 hff) R0 R0 R0 (RS 24 D)) (DPNode (MkDag 1 (bs4 h9e h7f h72 hfb) R0 (RS 40 A) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 9 (bs4 h9e h7f he7 hff) R0 R0 R0 (RS 32 B)) DPEmpty DPEmpty))))).

Definition dagTree_5 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 R0 R0 (RS 0 D)) DPEmpty.

Definition dagSub_6_8 : DagPTree :=
  DPNode (MkDag 0 (bs6 h2f h3f hfc hf2 hff h2f) R0 R0 R0 (RS 242 C)) (DPNode (MkDag 0 (bs6 hee h5f h3c hf3 hcb hff)
    (RS 16 D) R0 R0 (RS 146 B)) (DPNode (MkDag 0 (bs6 hfc hf7 hfc hf2 hf3 hff) R0 R0 (RS 273 E) (RS 274 B)) (DPNode
    (MkDag 0 (bs6 h9e h79 h7c hfe h79 he7) R0 (RS 65 A) R0 R0) (DPNode (MkDag 0 (bs6 hcf hfe h7c hf3 hdf h2f) R0 R0
    R0 (RS 129 C)) (DPNode (MkDag 0 (bs6 h3c hbf h3c hbe h5f h7f) R0 R0 R0 (RS 257 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 h3f hcf hfc hf3 hff h2f) R0 R0 R0 (RS 385 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 haf hf2 hfc
    hf2 hf9 he7) R0 R0 (RS 29 E) R0) (DPNode (MkDag 0 (bs6 h3e h7f h3c hf2 hf3 hff) R0 R0 R0 (RS 321 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hf9 h7c hf3 hf3 hff) R0 (RS 20 C) (RS 98 E) (RS 20 C)) (DPNode
    (MkDag 0 (bs6 hbd hcf hfc hf3 hcb hff) R0 R0 (RS 18 E) R0) (DPNode (MkDag 0 (bs6 h3f hb9 h7c hf2 hf9 hfd) R0 R0
    R0 (RS 289 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf7 hfc hf2 hf9 he7) (RS 224 D) R0 R0 (RS
    225 B)) (DPNode (MkDag 0 (bs6 h3e h79 h7c hf2 hf3 hff) R0 R0 R0 (RS 353 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 0 (bs6 he5 hf3 hdc hf3 hf9 he7) (RS 48 D) R0 R0 (RS 390 B)) (DPNode (MkDag 0 (bs6 hff h73 hfc hf3 hf9
    he7) (RS 80 D) R0 R0 (RS 81 B)) (DPNode (MkDag 0 (bs6 hbe h5f h3c hbe h5f h7f) R0 R0 (RS 145 E) R0) (DPNode
    (MkDag 0 (bs6 h79 hfc hfc hfe h79 he7) (RS 32 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c
    hf2 hfc hfe h79 he7) (RS 209 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3e h5f h3c hf2 hf9 he7) R0 R0 R0 (RS 337 B))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hfe h7f hfc hf3 hdf h2f) R0 (RS 172 C) R0 (RS 172 C)) (DPNode
    (MkDag 0 (bs6 hfc hf2 hfc hf2 hf9 he7) (RS 176 D) R0 R0 (RS 177 B)) (DPNode (MkDag 0 (bs6 h7f hcf hdc hf2 hf9
    he7) R0 R0 R0 (RS 50 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3f h9f hdc hbe h5f h7f) R0 R0 R0 (RS
    241 C)) (DPNode (MkDag 0 (bs6 he5 hf9 h7c hf2 hf9 hfd) R0 R0 R0 (RS 369 C)) DPEmpty DPEmpty) DPEmpty))))
    (DPNode (MkDag 0 (bs6 h7e h5f h3c hf3 hff h2f) (RS 142 C) R0 R0 (RS 36 B)) (DPNode (MkDag 0 (bs6 h7e h7f h3f
    h9e h79 he7) R0 R0 R0 (RS 322 B)) (DPNode (MkDag 0 (bs6 h9f hcf hdc hf3 hf9 hfd) R0 (RS 73 A) R0 R0) (DPNode
    (MkDag 0 (bs6 hee h5f h3c hf2 hf9 he7) R0 R0 R0 (RS 137 B)) (DPNode (MkDag 0 (bs6 hf3 hcf hdc hf3 hf9 hfd) (RS
    264 D) R0 (RS 265 E) (RS 266 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbb h9f hcf h9e h79 he7) R0 (RS 393 C)
    R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hbf h3c hf3 hcf h2f) R0 R0 R0 (RS 201 B)) (DPNode (MkDag 0
    (bs6 hbe h7f h3c hf2 hf9 hfd) R0 R0 (RS 329 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c
    hf2 hf9 he7) R0 R0 R0 (RS 102 B)) (DPNode (MkDag 0 (bs6 h7f hfc hfc hf2 hf9 he7) R0 R0 R0 (RS 169 B)) (DPNode
    (MkDag 0 (bs6 hbf hcf h3c hbe h79 he7) R0 R0 (RS 297 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he7
    hfe h7c hf3 hf3 hff) R0 R0 R0 (RS 30 B)) (DPNode (MkDag 0 (bs6 hcb hf3 hfc hf3 hf9 he7) R0 R0 R0 (RS 31 B))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hee h5f h3f hb9 h7d) (RS 56 D) R0 R0 (RS 57 B)) (DPNode
    (MkDag 0 (bs6 hfc hf2 hfc hf2 hf9 hfd) (RS 88 D) (RS 89 C) R0 (RS 89 C)) (DPNode (MkDag 0 (bs6 hfe h79 h7c hfe
    h79 he7) R0 R0 R0 (RS 153 C)) (DPNode (MkDag 0 (bs6 h3c hf9 h7c hbe h79 he7) R0 R0 R0 (RS 361 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c hff h3c hf2 hf9 hfd) (RS 217 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hee
    h79 h7c hf3 hdf h2f) (RS 344 D) R0 R0 (RS 54 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 haf h9f hcf
    h9e h79 he7) R0 R0 (RS 121 E) R0) (DPNode (MkDag 0 (bs6 h2f h3f h3c hf2 hf9 hfd) R0 R0 R0 (RS 185 C)) (DPNode
    (MkDag 0 (bs6 h3e h79 hfc hf2 hf9 hfd) R0 R0 R0 (RS 313 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he5
    hf7 h2f h9e h79 he7) R0 R0 R0 (RS 249 C)) (DPNode (MkDag 0 (bs6 hbe h79 hfc hf2 hff h2f) R0 R0 (RS 377 E) R0)
    DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_9 : DagPTree :=
  DPNode (MkDag 0 (bs6 h73 hf7 h3c hf3 hff h2f) R0 R0 R0 (RS 90 B)) (DPNode (MkDag 0 (bs6 hf3 hf9 h7c hfe h79 he7)
    (RS 20 D) (RS 45 C) (RS 99 E) (RS 45 C)) (DPNode (MkDag 0 (bs6 hfe h5f h3c hf3 hff h2f) R0 R0 (RS 24 E) (RS 339
    C)) (DPNode (MkDag 0 (bs6 h9f hcf h7c hf3 hff h2f) R0 (RS 69 A) R0 R0) (DPNode (MkDag 0 (bs6 h7d hf2 hfc hf2
    hf9 hfd) (RS 15 D) R0 R0 (RS 133 B)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hfe h5f h7f) R0 (RS 261 A) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hff hcf hfc hf3 hcb hff) (RS 388 D) R0 (RS 389 E) (RS 48 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 h2f h97 hcf h9e h79 he7) R0 R0 R0 (RS 197 C)) (DPNode (MkDag 0 (bs6 h3e h7f h3c
    hf3 hcf h2f) R0 R0 R0 (RS 325 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hf9 h7c hf2 hf9 h7d) R0
    (RS 102 C) (RS 103 E) (RS 102 C)) (DPNode (MkDag 0 (bs6 he7 h9f hfc hf3 hdf h2f) (RS 164 D) R0 R0 (RS 23 B))
    (DPNode (MkDag 0 (bs6 hbd hcf h3c hbe h79 he7) R0 R0 (RS 293 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 haf hfe h7c hf3 hdf h2f) R0 R0 (RS 229 E) R0) (DPNode (MkDag 0 (bs6 he7 hcb hdc hf2 hff h2f) R0 R0 R0 (RS
    357 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h9f h9f hcf h9e h79 he7) R0 R0 R0 (RS 394 B)) (DPNode
    (MkDag 0 (bs6 h7e h5e h7c hf2 hf9 h7d) R0 R0 R0 (RS 82 B)) (DPNode (MkDag 0 (bs6 hbe h79 h7c hf3 hf9 he7) R0 R0
    (RS 149 E) R0) (DPNode (MkDag 0 (bs6 hb9 hf9 h7c hf3 hcf h2f) R0 (RS 277 C) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h9f h9f hdc hf2 hf9 h7d) R0 R0 R0 (RS 213 B)) (DPNode (MkDag 0 (bs6 h3e h5f h3c hf3 hf9
    hfd) R0 R0 R0 (RS 6 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 haf h9e h7c hf2 hf3 hff) R0 R0 (RS 117
    E) R0) (DPNode (MkDag 0 (bs6 hcf h3f h3c hf3 hcf h2f) R0 R0 R0 (RS 181 C)) (DPNode (MkDag 0 (bs6 h7e h79 hfc
    hbe h79 he7) (RS 9 C) R0 R0 (RS 309 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf hff h3c hf3 hf9
    h7d) R0 (RS 245 C) R0 R0) (DPNode (MkDag 0 (bs6 h2f hcf h3c hf3 hf9 he7) R0 R0 R0 (RS 373 C)) DPEmpty DPEmpty)
    DPEmpty)))) (DPNode (MkDag 0 (bs6 h3c hbc hfc hf3 hf9 h7d) R0 R0 R0 (RS 188 B)) (DPNode (MkDag 0 (bs6 h3e h5f
    h3c hf3 hcb hff) R0 R0 R0 (RS 344 B)) (DPNode (MkDag 0 (bs6 h9f hcf hfc hf3 hcb hff) R0 (RS 77 A) R0 R0)
    (DPNode (MkDag 0 (bs6 h3e h5f h2f h9e h79 he7) R0 R0 R0 (RS 141 B)) (DPNode (MkDag 0 (bs6 hf3 hfb hfc hf3 hdf
    h2f) R0 R0 (RS 269 E) (RS 270 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hcf hff h3c hf2 hf9 hfd) R0
    R0 R0 (RS 205 A)) (DPNode (MkDag 0 (bs6 hfe h7e h7c hf3 hdf h2f) R0 R0 R0 (RS 333 C)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs6 hfe h7b hfc hf3 hdf h2f) R0 (RS 171 C) R0 R0) (DPNode (MkDag 0 (bs6 hfc hbf hfc
    hfe h5f h7f) (RS 172 D) (RS 173 B) (RS 174 E) (RS 173 B)) (DPNode (MkDag 0 (bs6 hbf hcf hdc hf3 hf9 h7d) R0 R0
    (RS 301 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3f h9e h7c hbe h79 he7) R0 R0 R0 (RS 237 C))
    (DPNode (MkDag 0 (bs6 h3f hb9 h7c hbe h5f h7f) R0 R0 R0 (RS 365 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    0 (bs6 h9e h5f h3c hbe h5f h7f) R0 (RS 61 A) R0 R0) (DPNode (MkDag 0 (bs6 hf2 hf7 h3c hf3 hcb hff) R0 (RS 26 C)
    (RS 93 E) (RS 26 C)) (DPNode (MkDag 0 (bs6 h7d hcf hfc hf3 hff h2f) (RS 158 D) R0 R0 (RS 17 B)) (DPNode (MkDag
    0 (bs6 h3c hf9 h7c hf3 hcb hff) R0 R0 R0 (RS 285 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h9f h9f
    hdc hf3 hf9 h7d) R0 R0 R0 (RS 221 B)) (DPNode (MkDag 0 (bs6 hee h79 h7c hf2 hf9 h7d) (RS 348 D) R0 R0 (RS 349
    B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h2f h3f h3c hf3 hcf h2f) R0 R0 R0 (RS 125 C)) (DPNode
    (MkDag 0 (bs6 he7 h9e h7c hf3 hf3 hff) (RS 188 D) R0 R0 (RS 189 B)) (DPNode (MkDag 0 (bs6 h3e h7f h3c hf3 hf9
    he7) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h2f hff h3c hf3 hff h2f) R0 R0 R0 (RS
    253 C)) (DPNode (MkDag 0 (bs6 hbd hcf hfc hf3 hff h2f) R0 R0 (RS 381 E) R0) DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_10 : DagPTree :=
  DPNode (MkDag 0 (bs6 hf3 hcf hdc hf2 hff h2f) (RS 10 D) (RS 106 C) (RS 107 E) (RS 106 C)) (DPNode (MkDag 0 (bs6
    h3d hcf hfc hf3 hcb hff) R0 R0 R0 (RS 161 C)) (DPNode (MkDag 0 (bs6 hfe h7f h3c hf2 hff h2f) R0 R0 (RS 327 E)
    (RS 328 C)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf2 hf3 hff) R0 (RS 67 A) R0 R0) (DPNode (MkDag 0 (bs6 h3f hfe
    h7c hf3 hf3 hff) R0 R0 R0 (RS 5 B)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf3 hf9 h7d) R0 (RS 259 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 h7d hcb hdc hf2 hff h2f) R0 R0 R0 (RS 387 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 h3f hf2 hfc hf2 hf9 he7) R0 R0 R0 (RS 195 C)) (DPNode (MkDag 0 (bs6 hfe h7f h3f h9e h79 he7) R0 R0 R0 (RS
    323 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hf3 hf3 hff) R0 R0 R0 (RS 96 B)) (DPNode
    (MkDag 0 (bs6 h2f hcf hfc hf3 hcb hff) R0 R0 R0 (RS 163 C)) (DPNode (MkDag 0 (bs6 h7f hcf h3c hf2 hf9 h7d) R0
    R0 R0 (RS 291 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbd hfe h7c hf3 hdf h2f) R0 R0 (RS 227 E) R0)
    (DPNode (MkDag 0 (bs6 hbf hcf hdc hf3 hf9 hfd) R0 R0 (RS 355 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    0 (bs6 hff hcf hdc hf2 hf9 he7) (RS 50 D) R0 (RS 304 E) (RS 305 C)) (DPNode (MkDag 0 (bs6 hfe h5e h7c hf2 hf9
    h7d) R0 (RS 83 C) (RS 84 E) (RS 83 C)) (DPNode (MkDag 0 (bs6 h7e h5f h3c hf3 hcb hff) (RS 147 C) R0 R0 R0)
    (DPNode (MkDag 0 (bs6 h7c hff hfc hf2 hf3 hff) (RS 275 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 hbb h9f hdc hf2 hf9 h7d) R0 (RS 211 C) R0 R0) (DPNode (MkDag 0 (bs6 h7e h5f h2f h9e h79 he7) (RS 36 C) R0
    R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hbf hfc hfe h5f h7f) R0 R0 R0 (RS 115 C)) (DPNode
    (MkDag 0 (bs6 h5f h9f hcf h9e h79 he7) (RS 179 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3e h79 hfc hf3 hcf h2f) R0
    R0 R0 (RS 307 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf h3f hfc hf2 hff h2f) R0 R0 (RS 243 E) R0)
    (DPNode (MkDag 0 (bs6 h3d hcf h3c hf3 hf9 he7) R0 R0 R0 (RS 371 C)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag
    0 (bs6 hf3 hf9 h7c hf3 hf9 h7d) (RS 26 D) (RS 94 C) (RS 95 E) (RS 94 C)) (DPNode (MkDag 0 (bs6 hff h9f hfc hf3
    hdf h2f) (RS 42 D) R0 (RS 359 E) (RS 360 D)) (DPNode (MkDag 0 (bs6 h9f hcb hdc hf2 hff h2f) R0 (RS 75 A) R0 R0)
    (DPNode (MkDag 0 (bs6 hfe h5f h3c hf2 hf9 he7) R0 R0 R0 (RS 139 C)) (DPNode (MkDag 0 (bs6 hf3 hcf hfc hf3 hcb
    hff) R0 R0 (RS 267 E) (RS 268 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7f h3f h3c hf3 hcf h2f) (RS 395 E) R0
    R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he7 hf7 h3c hf2 hff h2f) (RS 202 D) R0 R0 (RS 203 B)) (DPNode
    (MkDag 0 (bs6 hee h7e h7c hf3 hdf h2f) R0 R0 R0 (RS 331 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6
    hbe h7b hfc hf3 hdf h2f) R0 (RS 108 C) (RS 109 E) R0) (DPNode (MkDag 0 (bs6 hbc hf2 hfc hf2 hf9 hfd) R0 (RS 88
    C) R0 R0) (DPNode (MkDag 0 (bs6 he7 hcf h3c hf2 hf9 hfd) (RS 298 D) R0 R0 (RS 299 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hcf h3f hfc hf3 hff h2f) R0 R0 R0 (RS 235 C)) (DPNode (MkDag 0 (bs6 h2f hb9 h7c hbe h5f
    h7f) R0 R0 R0 (RS 363 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h9e h5f h3c hf3 hff h2f) R0 (RS 59
    A) R0 R0) (DPNode (MkDag 0 (bs6 hf3 hf7 h3c hf3 hff h2f) (RS 90 D) (RS 92 C) (RS 12 E) (RS 92 C)) (DPNode
    (MkDag 0 (bs6 h3e h79 h7c hf2 hf9 h7d) R0 R0 R0 (RS 22 B)) (DPNode (MkDag 0 (bs6 hf9 hf9 h7c hbe h5f h7f) (RS
    282 D) R0 R0 (RS 283 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbb h9f hdc hf3 hf9 h7d) R0 (RS 219 C)
    R0 R0) (DPNode (MkDag 0 (bs6 hbe h79 h7c hfe h79 he7) R0 R0 (RS 347 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 hbf h9f hcf h9e h79 he7) R0 R0 (RS 51 E) R0) (DPNode (MkDag 0 (bs6 h3f h3f h3c hf2 hf9 hfd) R0 R0
    R0 (RS 187 C)) (DPNode (MkDag 0 (bs6 hfe h7f h3c hf3 hdf h2f) R0 R0 (RS 46 E) (RS 315 C)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs6 h3d hff h3c hf3 hff h2f) R0 R0 R0 (RS 251 C)) (DPNode (MkDag 0 (bs6 hee h79 hfc
    hf2 hf9 hfd) (RS 378 D) R0 R0 (RS 379 B)) DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_11 : DagPTree :=
  DPNode (MkDag 0 (bs6 hee h7f hfc hf3 hdf h2f) (RS 14 D) R0 R0 (RS 110 B)) (DPNode (MkDag 0 (bs6 hee h79 h7c hf2
    hf3 hff) (RS 22 D) R0 R0 (RS 155 B)) (DPNode (MkDag 0 (bs6 h3f hcf h3c hf3 hf9 he7) R0 R0 R0 (RS 374 B))
    (DPNode (MkDag 0 (bs6 h9f hcf hfc hf3 hff h2f) R0 (RS 71 A) R0 R0) (DPNode (MkDag 0 (bs6 hbe h5f h3c hfe h5f
    h7f) R0 R0 (RS 135 E) R0) (DPNode (MkDag 0 (bs6 hf3 hcf h7c hf3 hff h2f) R0 R0 (RS 263 E) (RS 264 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 he5 hf3 hfc hf3 hf9 he7) (RS 390 D) R0 R0 (RS 7 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 h3f h97 hcf h9e h79 he7) R0 R0 R0 (RS 199 C)) (DPNode (MkDag 0 (bs6 h7e h7f h3c hbe h79 he7) (RS
    34 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hf9 h7c hf2 hf9 he7) (RS 102 D) (RS 13 C)
    (RS 104 E) (RS 13 C)) (DPNode (MkDag 0 (bs6 he7 he7 hdc hfe h79 he7) (RS 166 D) R0 R0 (RS 167 A)) (DPNode
    (MkDag 0 (bs6 haf hcf h3c hbe h79 he7) R0 R0 (RS 295 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf
    hfe h7c hf3 hdf h2f) R0 R0 (RS 231 E) R0) (DPNode (MkDag 0 (bs6 hfd hcf hfc hf3 hcb hff) R0 R0 R0 (RS 42 C))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h7e h79 h7c hf3 hdf h2f) (RS 37 C) R0 R0 (RS 147 B)) (DPNode
    (MkDag 0 (bs6 h7c hbf hfc hf2 hff h2f) (RS 87 D) R0 R0 (RS 83 B)) (DPNode (MkDag 0 (bs6 hee h79 h7c hfe h79
    he7) R0 R0 R0 (RS 151 B)) (DPNode (MkDag 0 (bs6 hbc hf9 h7c hbe h79 he7) R0 (RS 279 C) (RS 280 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf7 h3c hf2 hf9 hfd) R0 R0 (RS 215 E) (RS 216 B)) (DPNode (MkDag 0
    (bs6 hfe h5f h3c hbe h5f h7f) R0 R0 R0 (RS 343 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hbf h9e h7c
    hf2 hf3 hff) R0 R0 (RS 119 E) R0) (DPNode (MkDag 0 (bs6 h3f h9f h3c hf2 hff h2f) R0 R0 R0 (RS 183 C)) (DPNode
    (MkDag 0 (bs6 h7e h79 hfc hf2 hff h2f) R0 R0 R0 (RS 9 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c
    hbf h3c hfe h5f h7f) (RS 247 E) R0 R0 R0) (DPNode (MkDag 0 (bs6 he7 hcf h3c hf2 hf9 h7d) (RS 374 D) R0 R0 (RS
    43 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 h7d hfe h7c hf2 hf9 h7d) R0 R0 R0 (RS 233 B)) (DPNode
    (MkDag 0 (bs6 h7e h7f h3c hf3 hdf h2f) R0 R0 R0 (RS 314 B)) (DPNode (MkDag 0 (bs6 h9f h9f hfc hf3 hdf h2f) R0
    (RS 79 B) R0 R0) (DPNode (MkDag 0 (bs6 hfe h5f h3c hf3 hf9 hfd) R0 R0 (RS 143 E) (RS 144 C)) (DPNode (MkDag 0
    (bs6 hf3 hf3 hdc hf3 hf9 he7) (RS 270 D) R0 (RS 271 E) (RS 31 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 hfb h97 hdc hf3 hf9 h7d) R0 (RS 207 A) R0 R0) (DPNode (MkDag 0 (bs6 hfe h5f h3c hfe h5f h7f) (RS 334 D) R0
    (RS 47 E) (RS 335 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h7e h7f hfc hf3 hdf h2f) (RS 111 D) R0
    R0 (RS 112 B)) (DPNode (MkDag 0 (bs6 h7c hbf hfc hfe h5f h7f) R0 R0 R0 (RS 172 B)) (DPNode (MkDag 0 (bs6 he7
    hcb hdc hfe h79 he7) R0 R0 R0 (RS 303 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h2f h9f hdc hbe h5f
    h7f) R0 R0 R0 (RS 239 C)) (DPNode (MkDag 0 (bs6 h7f hf9 h7c hf2 hff h2f) R0 R0 R0 (RS 367 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf3 hdf h2f) R0 (RS 63 A) R0 R0) (DPNode (MkDag 0 (bs6 hf3 hf9 h7c
    hf3 hf9 he7) (RS 94 D) (RS 96 C) (RS 97 E) (RS 96 C)) (DPNode (MkDag 0 (bs6 hcf hcf hfc hf3 hff h2f) R0 R0 R0
    (RS 354 C)) (DPNode (MkDag 0 (bs6 h2f hb9 h7c hf2 hf9 hfd) R0 R0 R0 (RS 287 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h67 h9f hdc hf2 hf9 h7d) R0 R0 R0 (RS 223 B)) (DPNode (MkDag 0 (bs6 hfe h79 h7c hf2 hf9
    h7d) R0 R0 R0 (RS 351 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h3f h3f h3c hf3 hcf h2f) R0 R0 R0
    (RS 35 B)) (DPNode (MkDag 0 (bs6 hbd hf2 hfc hf2 hf9 he7) R0 R0 (RS 191 E) R0) (DPNode (MkDag 0 (bs6 h7e h7f
    h3c hf2 hf9 h7d) R0 R0 R0 (RS 33 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3f hff h3c hf3 hff h2f)
    R0 R0 R0 (RS 255 C)) (DPNode (MkDag 0 (bs6 haf hcf hfc hf3 hff h2f) R0 R0 (RS 53 E) R0) DPEmpty DPEmpty)
    DPEmpty)))).

Definition dagSub_6_12 : DagPTree :=
  DPNode (MkDag 0 (bs6 hfe h79 hfc hf2 hff h2f) R0 R0 (RS 310 E) (RS 311 C)) (DPNode (MkDag 0 (bs6 hfd hcf hfc hf3
    hff h2f) R0 R0 (RS 156 E) (RS 157 C)) (DPNode (MkDag 0 (bs6 hfe h7f h3c hf2 hf9 h7d) R0 R0 (RS 318 E) (RS 319
    C)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf2 hf9 h7d) R0 R0 R0 (RS 66 A)) (DPNode (MkDag 0 (bs6 hbf hfe h7c hf3
    hf3 hff) R0 R0 (RS 130 E) R0) (DPNode (MkDag 0 (bs6 he7 h9f h3c hf3 hcb hff) (RS 257 D) R0 R0 (RS 258 A))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 386 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 hbf hf2 hfc hf2 hf9 he7) R0 R0 (RS 194 E) R0) (DPNode (MkDag 0 (bs6 hee h7f h3f h9e h79 he7) R0
    R0 R0 (RS 40 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hf3 hf9 he7) R0 R0 R0 (RS 94 B))
    (DPNode (MkDag 0 (bs6 haf hcf hfc hf3 hcb hff) R0 R0 (RS 162 E) R0) (DPNode (MkDag 0 (bs6 hef hcf h3c hf2 hf9
    h7d) R0 R0 R0 (RS 290 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he5 hf7 h3c hf2 hf9 hfd) (RS 225 D)
    R0 R0 (RS 226 C)) (DPNode (MkDag 0 (bs6 he7 hcf h7c hf3 hff h2f) (RS 353 D) R0 R0 (RS 156 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 h73 hcb hdc hf3 hf9 hfd) R0 R0 R0 (RS 27 B)) (DPNode (MkDag 0 (bs6 h7f he7 hdc
    hfe h79 he7) (RS 82 C) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3e h5f h3c hbe h5f h7f) R0 R0 R0 (RS 16 B)) (DPNode
    (MkDag 0 (bs6 h7c hf7 hfc hf2 hf3 hff) R0 R0 R0 (RS 32 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hcf
    h9e h7c hfe h5f h7f) R0 R0 R0 (RS 210 A)) (DPNode (MkDag 0 (bs6 hee h5f h2f h9e h79 he7) R0 R0 R0 (RS 338 B))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hbf hfc hfe h5f h7f) R0 R0 (RS 114 E) R0) (DPNode (MkDag 0
    (bs6 h7b h9f hcf h9e h79 he7) (RS 178 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbe h79 hfc hf3 hcf h2f) R0 R0 (RS 306
    E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 haf h3f hfc hf2 hff h2f) R0 R0 (RS 8 E) R0) (DPNode
    (MkDag 0 (bs6 hbd hcf h3c hf3 hf9 he7) R0 R0 (RS 370 E) R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6
    h3f hcf hfc hf3 hcb hff) R0 R0 R0 (RS 164 B)) (DPNode (MkDag 0 (bs6 h3f h97 hdc hfe h79 he7) R0 R0 R0 (RS 113
    C)) (DPNode (MkDag 0 (bs6 h97 hcb hdc hf2 hff h2f) R0 R0 R0 (RS 74 A)) (DPNode (MkDag 0 (bs6 h7e h5f h3c hf2
    hf9 he7) R0 R0 R0 (RS 138 B)) (DPNode (MkDag 0 (bs6 h73 hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 264 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 hfb h9f hcf h9e h79 he7) R0 (RS 52 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 he7 h9f h3c hbe h79 he7) (RS 201 D) R0 R0 (RS 202 B)) (DPNode (MkDag 0 (bs6 h3e h7f h3c hf2 hf9 hfd) R0 R0
    R0 (RS 330 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hf2 hf3 hff) R0 R0 R0 (RS 13 B))
    (DPNode (MkDag 0 (bs6 hff hfc hfc hf2 hf9 he7) (RS 169 D) R0 R0 (RS 86 B)) (DPNode (MkDag 0 (bs6 h3f hcf h3c
    hbe h79 he7) R0 R0 R0 (RS 298 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfd hfe h7c hf2 hf9 h7d) R0
    R0 R0 (RS 234 D)) (DPNode (MkDag 0 (bs6 haf hb9 h7c hbe h5f h7f) R0 R0 (RS 362 E) R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 he7 hfe h5e h7f hcf h2f) (RS 57 D) R0 R0 (RS 58 A)) (DPNode (MkDag 0 (bs6 hf2
    hf7 h3c hfe h5f h7f) (RS 89 D) (RS 19 C) (RS 11 E) (RS 19 C)) (DPNode (MkDag 0 (bs6 hbe h79 h7c hf2 hf9 h7d) R0
    R0 (RS 154 E) R0) (DPNode (MkDag 0 (bs6 h79 hf9 h7c hbe h5f h7f) R0 R0 R0 (RS 282 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hcf h9e h7c hf3 hdf h2f) R0 R0 R0 (RS 218 A)) (DPNode (MkDag 0 (bs6 h7e h79 h7c hf3 hf9
    he7) R0 R0 R0 (RS 37 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h2f h9f hcf h9e h79 he7) R0 R0 R0 (RS
    122 C)) (DPNode (MkDag 0 (bs6 hbf h3f h3c hf2 hf9 hfd) R0 R0 (RS 186 E) R0) (DPNode (MkDag 0 (bs6 hee h7f h3c
    hf3 hdf h2f) R0 R0 R0 (RS 46 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbd hff h3c hf3 hff h2f) R0 R0
    (RS 250 E) R0) (DPNode (MkDag 0 (bs6 h3e h79 hfc hf2 hff h2f) R0 R0 R0 (RS 378 B)) DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_13 : DagPTree :=
  DPNode (MkDag 0 (bs6 hf3 hf9 h7c hf2 hf3 hff) (RS 13 D) (RS 27 C) (RS 105 E) (RS 27 C)) (DPNode (MkDag 0 (bs6 he7
    hf7 h3c hf2 hf9 hfd) (RS 21 D) R0 R0 (RS 127 B)) (DPNode (MkDag 0 (bs6 hfe h79 h7c hf3 hf9 he7) R0 R0 (RS 345
    E) (RS 346 C)) (DPNode (MkDag 0 (bs6 h97 hcf hfc hf3 hff h2f) R0 R0 R0 (RS 70 A)) (DPNode (MkDag 0 (bs6 hfd hf2
    hfc hf2 hf9 hfd) R0 R0 R0 (RS 334 C)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf2 hf9 he7) R0 R0 R0 (RS 262 C))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7f hcf hfc hf3 hcb hff) R0 R0 R0 (RS 388 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 hbf h97 hcf h9e h79 he7) R0 R0 (RS 198 E) R0) (DPNode (MkDag 0 (bs6 hee h7f h3c hbe h79 he7) (RS
    325 D) R0 R0 (RS 326 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hfe h5f h7f) R0 R0 R0 (RS
    45 B)) (DPNode (MkDag 0 (bs6 he7 hf3 hfc hf3 hf9 he7) (RS 165 D) R0 R0 (RS 166 B)) (DPNode (MkDag 0 (bs6 h3d
    hcf h3c hbe h79 he7) R0 R0 R0 (RS 294 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h2f hfe h7c hf3 hdf
    h2f) R0 R0 R0 (RS 230 C)) (DPNode (MkDag 0 (bs6 h7d hcf hfc hf3 hcb hff) R0 R0 R0 (RS 358 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 h2f hcf hfc hf3 hff h2f) R0 R0 R0 (RS 383 C)) (DPNode (MkDag 0 (bs6 h7c hf2
    hfc hf2 hf9 hfd) R0 R0 R0 (RS 88 B)) (DPNode (MkDag 0 (bs6 h3e h79 h7c hf3 hf9 he7) R0 R0 R0 (RS 150 B))
    (DPNode (MkDag 0 (bs6 hf9 hf9 h7c hf3 hcf h2f) (RS 277 D) (RS 278 C) R0 (RS 278 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h7f h3f hfc hf2 hf9 he7) (RS 214 C) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7e h5f h3c hbe h5f
    h7f) R0 R0 R0 (RS 342 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h2f h9e h7c hf2 hf3 hff) R0 R0 R0
    (RS 118 C)) (DPNode (MkDag 0 (bs6 hbf h9f h3c hf2 hff h2f) R0 R0 (RS 182 E) R0) (DPNode (MkDag 0 (bs6 hfe h79
    hfc hbe h79 he7) R0 R0 R0 (RS 376 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hff hff h3c hf3 hf9 h7d)
    (RS 245 D) R0 R0 (RS 246 B)) (DPNode (MkDag 0 (bs6 hbf hcf h3c hf3 hf9 he7) R0 R0 (RS 38 E) R0) DPEmpty
    DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 h2f hf2 hfc hf2 hf9 he7) R0 R0 R0 (RS 193 C)) (DPNode (MkDag 0 (bs6
    hf3 hf9 h7c hfe h5f h7f) (RS 45 D) (RS 100 C) (RS 101 E) (RS 100 C)) (DPNode (MkDag 0 (bs6 h97 h9f hfc hf3 hdf
    h2f) R0 R0 R0 (RS 78 A)) (DPNode (MkDag 0 (bs6 hee h5f h3c hf3 hff h2f) (RS 141 D) R0 R0 (RS 24 B)) (DPNode
    (MkDag 0 (bs6 h73 hfb hfc hf3 hdf h2f) R0 R0 R0 (RS 268 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbb
    h97 hdc hf3 hf9 h7d) R0 (RS 206 C) R0 R0) (DPNode (MkDag 0 (bs6 hbf h97 hdc hfe h79 he7) R0 R0 (RS 41 E) R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h3e h7b hfc hf3 hdf h2f) R0 R0 R0 (RS 14 B)) (DPNode (MkDag 0
    (bs6 h7c hf2 hfc hf2 hf9 he7) (RS 175 D) R0 R0 (RS 176 B)) (DPNode (MkDag 0 (bs6 h3f hcf hdc hf3 hf9 h7d) R0 R0
    R0 (RS 302 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 haf h9f hdc hbe h5f h7f) R0 R0 (RS 238 E) R0)
    (DPNode (MkDag 0 (bs6 hef hf9 h7c hf2 hff h2f) R0 R0 R0 (RS 366 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    0 (bs6 h9e h5f h3c hf3 hcb hff) R0 R0 R0 (RS 62 A)) (DPNode (MkDag 0 (bs6 h72 hf7 h3c hf3 hcb hff) R0 R0 R0 (RS
    92 B)) (DPNode (MkDag 0 (bs6 hff hcf hdc hf3 hf9 hfd) R0 R0 (RS 159 E) (RS 160 C)) (DPNode (MkDag 0 (bs6 haf
    hb9 h7c hf2 hf9 hfd) R0 R0 (RS 286 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7f h3f hfc hf3 hf9
    he7) (RS 222 E) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7e h79 h7c hf2 hf9 h7d) (RS 0 C) R0 R0 (RS 350 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hbf h3f h3c hf3 hcf h2f) R0 R0 (RS 126 E) R0) (DPNode (MkDag 0 (bs6
    he5 hf7 hfc hfe h5f h7f) (RS 189 D) R0 R0 (RS 190 C)) (DPNode (MkDag 0 (bs6 h7e h7f h3c hfe h79 he7) (RS 33 C)
    R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf hff h3c hf3 hff h2f) R0 R0 (RS 254 E) R0) (DPNode
    (MkDag 0 (bs6 h3d hcf hfc hf3 hff h2f) R0 R0 R0 (RS 382 C)) DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_14 : DagPTree :=
  DPNode (MkDag 0 (bs6 h72 hf7 h3c hfe h5f h7f) R0 R0 R0 (RS 89 B)) (DPNode (MkDag 0 (bs6 hf3 hff h3c hf2 hf9 he7)
    R0 (RS 90 C) (RS 91 E) (RS 90 C)) (DPNode (MkDag 0 (bs6 he7 h9f h3c hf2 hff h2f) (RS 35 D) R0 R0 (RS 21 B))
    (DPNode (MkDag 0 (bs6 h97 hcf h7c hf3 hff h2f) R0 R0 R0 (RS 68 A)) (DPNode (MkDag 0 (bs6 he7 h9f hdc hbe h5f
    h7f) (RS 131 D) R0 R0 (RS 1 B)) (DPNode (MkDag 0 (bs6 h9e h79 h7c hf3 hf3 hff) R0 R0 R0 (RS 260 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 hfd hcb hdc hf2 hff h2f) R0 R0 R0 (RS 388 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 haf h97 hcf h9e h79 he7) R0 R0 (RS 196 E) R0) (DPNode (MkDag 0 (bs6 hbe h7f h3c hf3 hcf h2f) R0 R0 (RS 324
    E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hfe h79 he7) R0 R0 R0 (RS 20 B)) (DPNode
    (MkDag 0 (bs6 hbf hcf hfc hf3 hcb hff) R0 R0 (RS 25 E) R0) (DPNode (MkDag 0 (bs6 hff hcf h3c hf2 hf9 h7d) R0 R0
    R0 (RS 292 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3d hfe h7c hf3 hdf h2f) R0 R0 R0 (RS 228 C))
    (DPNode (MkDag 0 (bs6 h3f hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 356 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    0 (bs6 h3f h9f hcf h9e h79 he7) R0 R0 R0 (RS 123 C)) (DPNode (MkDag 0 (bs6 hfc hbf hfc hf2 hff h2f) R0 (RS 85
    B) (RS 86 E) (RS 85 B)) (DPNode (MkDag 0 (bs6 hfe h79 h7c hf3 hdf h2f) R0 R0 (RS 54 E) (RS 148 C)) (DPNode
    (MkDag 0 (bs6 hcf hb9 h7c hf3 hcf h2f) R0 R0 R0 (RS 276 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfb
    h9f hdc hf2 hf9 h7d) R0 (RS 212 A) R0 R0) (DPNode (MkDag 0 (bs6 hbe h5f h3c hf3 hf9 hfd) R0 R0 (RS 340 E) R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hf2 hfc hf2 hf9 he7) R0 R0 (RS 3 E) R0) (DPNode (MkDag 0
    (bs6 h7f h9f hcf h9e h79 he7) (RS 180 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hee h79 hfc hbe h79 he7) R0 R0 R0 (RS
    308 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3f h3f hfc hf2 hff h2f) R0 R0 R0 (RS 244 A)) (DPNode
    (MkDag 0 (bs6 haf hcf h3c hf3 hf9 he7) R0 R0 (RS 372 E) R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6
    hf3 hcb hdc hf3 hf9 hfd) (RS 27 D) (RS 10 C) (RS 49 E) (RS 10 C)) (DPNode (MkDag 0 (bs6 h7d hcf h3f h9e h79
    he7) (RS 375 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h97 hcf hfc hf3 hcb hff) R0 R0 R0 (RS 76 A)) (DPNode (MkDag 0
    (bs6 hbe h5f h2f h9e h79 he7) R0 R0 (RS 140 E) R0) (DPNode (MkDag 0 (bs6 h73 hcf hfc hf3 hcb hff) R0 R0 R0 (RS
    266 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h65 hf7 h3c hf2 hf9 hfd) R0 R0 R0 (RS 225 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h7d hff h3c hf2 hf9 hfd) (RS 204 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7e h7e h7c hf3 hdf
    h2f) R0 R0 R0 (RS 332 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hcf hdc hf2 hff h2f) R0 R0 R0
    (RS 10 B)) (DPNode (MkDag 0 (bs6 hbe h7f hfc hf3 hdf h2f) R0 (RS 112 C) R0 R0) (DPNode (MkDag 0 (bs6 h7d hcf
    he7 h9e h79 he7) (RS 39 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf h9e h7c hbe h79 he7)
    R0 R0 (RS 236 E) R0) (DPNode (MkDag 0 (bs6 hbf hb9 h7c hbe h5f h7f) R0 R0 (RS 364 E) R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 h9e h5f h3c hf3 hf9 hfd) R0 R0 R0 (RS 60 A)) (DPNode (MkDag 0 (bs6 h73 hff h3c
    hf2 hf9 he7) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 0 (bs6 h7e h79 h7c hf2 hf3 hff) (RS 17 C) R0 R0 (RS 0 B))
    (DPNode (MkDag 0 (bs6 hbc hf9 h7c hf3 hcb hff) R0 R0 (RS 284 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 hfb h9f hdc hf3 hf9 h7d) R0 (RS 220 A) R0 R0) (DPNode (MkDag 0 (bs6 h3e h79 h7c hfe h79 he7) R0 R0 R0 (RS
    348 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 haf h3f h3c hf3 hcf h2f) R0 R0 (RS 124 E) R0) (DPNode
    (MkDag 0 (bs6 hbc hbc hfc hf3 hf9 h7d) R0 R0 (RS 28 E) R0) (DPNode (MkDag 0 (bs6 hbe h7f h3c hf3 hf9 he7) R0 R0
    (RS 316 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 haf hff h3c hf3 hff h2f) R0 R0 (RS 252 E) R0)
    (DPNode (MkDag 0 (bs6 h7e h79 hfc hf2 hf9 hfd) (RS 314 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)))).

Definition dagSub_6_15 : DagPTree :=
  DPNode (MkDag 0 (bs6 hcf hf2 hfc hf2 hf9 hfd) R0 R0 R0 (RS 134 C)) (DPNode (MkDag 0 (bs6 he7 hf3 hdc hf3 hf9 he7)
    (RS 23 D) R0 R0 (RS 165 B)) (DPNode (MkDag 0 (bs6 hcf hcf he7 h9e h79 he7) R0 R0 R0 (RS 300 C)) (DPNode (MkDag
    0 (bs6 h97 hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 72 A)) (DPNode (MkDag 0 (bs6 h3e h5f h3c hfe h5f h7f) R0 R0 R0 (RS
    136 B)) (DPNode (MkDag 0 (bs6 h73 hcf h7c hf3 hff h2f) R0 R0 R0 (RS 262 B)) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs6 hbe h5e h7c hf2 hf9 h7d) R0 (RS 82 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hbf h3c hf3 hcf
    h2f) R0 R0 (RS 200 E) R0) (DPNode (MkDag 0 (bs6 h7e h7f h3c hf2 hff h2f) R0 R0 R0 (RS 34 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hf2 hf9 h7d) R0 R0 R0 (RS 100 B)) (DPNode (MkDag 0 (bs6 h9e h5e h7c
    hf2 hf9 h7d) R0 (RS 168 B) R0 R0) (DPNode (MkDag 0 (bs6 h2f hcf h3c hbe h79 he7) R0 R0 R0 (RS 296 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h3f hfe h7c hf3 hdf h2f) R0 R0 R0 (RS 232 B)) (DPNode (MkDag 0 (bs6 h7f
    h9f hfc hf3 hdf h2f) R0 R0 R0 (RS 42 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf9 h7b hfc hf9
    he7) (RS 55 D) R0 R0 (RS 56 B)) (DPNode (MkDag 0 (bs6 hdc hf2 hfc hf2 hf9 hfd) R0 R0 R0 (RS 170 A)) (DPNode
    (MkDag 0 (bs6 h7e h79 h7c hfe h79 he7) R0 R0 R0 (RS 152 B)) (DPNode (MkDag 0 (bs6 hfc hf9 h7c hbe h79 he7) R0
    (RS 281 B) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf7 h3c hf2 hf9 hfd) R0 R0 R0 (RS 214 B))
    (DPNode (MkDag 0 (bs6 hbe h5f h3c hf3 hcb hff) R0 R0 (RS 44 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs6 h3f h9e h7c hf2 hf3 hff) R0 R0 R0 (RS 120 C)) (DPNode (MkDag 0 (bs6 haf h3f h3c hf2 hf9 hfd) R0 R0 (RS 184
    E) R0) (DPNode (MkDag 0 (bs6 hbe h79 hfc hf2 hf9 hfd) R0 R0 (RS 312 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs6 h65 hf7 h2f h9e h79 he7) R0 R0 R0 (RS 248 B)) (DPNode (MkDag 0 (bs6 hcf hcf h3f h9e h79 he7) R0
    R0 R0 (RS 296 C)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 h79 he7 hdc hfe h79 he7) (RS 272 B) R0 R0
    R0) (DPNode (MkDag 0 (bs6 h7e h5f h3c hfe h5f h7f) R0 R0 R0 (RS 334 B)) (DPNode (MkDag 0 (bs6 h7f h73 hfc hf3
    hf9 he7) R0 R0 R0 (RS 80 B)) (DPNode (MkDag 0 (bs6 h7e h5f h3c hf3 hf9 hfd) R0 R0 R0 (RS 142 B)) (DPNode (MkDag
    0 (bs6 h73 hf3 hdc hf3 hf9 he7) R0 R0 R0 (RS 270 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h9f h97
    hdc hf3 hf9 h7d) R0 R0 R0 (RS 208 B)) (DPNode (MkDag 0 (bs6 hbe h5f h3c hf2 hf9 he7) R0 R0 (RS 336 E) R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hcf h97 hdc hfe h79 he7) R0 R0 R0 (RS 113 C)) (DPNode (MkDag 0
    (bs6 hcf h9e h7c hf2 hf3 hff) R0 R0 R0 (RS 392 A)) (DPNode (MkDag 0 (bs6 h7d hcf hfc hfe h5f h7f) R0 R0 R0 (RS
    4 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf h9f hdc hbe h5f h7f) R0 R0 (RS 240 E) R0) (DPNode
    (MkDag 0 (bs6 hff hf9 h7c hf2 hff h2f) R0 R0 R0 (RS 368 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6
    h9e h79 h7c hf3 hf9 he7) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 0 (bs6 h73 hf9 h7c hf3 hf9 h7d) R0 R0 R0 (RS 26 B))
    (DPNode (MkDag 0 (bs6 h7f hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 157 B)) (DPNode (MkDag 0 (bs6 hbf hb9 h7c hf2 hf9
    hfd) R0 R0 (RS 288 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he7 h9f hdc hf2 hf9 h7d) R0 R0 R0 (RS
    224 B)) (DPNode (MkDag 0 (bs6 hbe h79 h7c hf2 hf3 hff) R0 R0 (RS 352 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 h7d hfe h7c hf3 hdf h2f) (RS 128 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3d hf2 hfc hf2 hf9 he7) R0
    R0 R0 (RS 192 C)) (DPNode (MkDag 0 (bs6 hbe h7f h3c hf2 hf3 hff) R0 R0 (RS 320 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hbc hbf h3c hbe h5f h7f) R0 R0 (RS 256 E) R0) (DPNode (MkDag 0 (bs6 hbf hcf hfc hf3 hff
    h2f) R0 R0 (RS 384 E) R0) DPEmpty DPEmpty) DPEmpty)))).

Definition dagTree_6 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hfe h79 h7c hf2 hf3 hff) R0 R0 (RS 155 E) (RS 380 C)) (DPNode (MkDag 0 (bs6 he7 hf7 hfc
    hf2 hff h2f) (RS 1 D) R0 R0 (RS 132 B)) (DPNode (MkDag 0 (bs6 hee h7f h3c hfe h79 he7) (RS 2 D) R0 R0 (RS 317
    B)) (DPNode (MkDag 0 (bs6 hfd hcf hfc hfe h5f h7f) R0 R0 R0 (RS 50 C)) dagSub_6_8 dagSub_6_9) (DPNode (MkDag 0
    (bs6 hee h5f h3c hbe h5f h7f) R0 R0 R0 (RS 341 B)) dagSub_6_10 dagSub_6_11)) (DPNode (MkDag 0 (bs6 h3c hf2 hfc
    hf2 hf9 he7) R0 R0 R0 (RS 116 C)) (DPNode (MkDag 0 (bs6 he7 hfe h7c hf2 hf9 h7d) R0 R0 R0 (RS 131 B))
    dagSub_6_12 dagSub_6_13) (DPNode (MkDag 0 (bs6 he5 he7 hdc hfe h79 he7) (RS 7 D) R0 R0 (RS 391 A)) dagSub_6_14
    dagSub_6_15))).

Definition dagSub_7_16 : DagPTree :=
  DPNode (MkDag 7 (bs6 hfc hbe h7e h5f h73 hcb) (RS 8 D) R0 R0 (RS 105 B)) (DPNode (MkDag 13 (bs6 h5f h72 hfe h5f
    hf3 hcb) (RS 17 B) R0 R0 R0) (DPNode (MkDag 20 (bs6 h73 hf3 he7 hee h5f hf9) R0 R0 R0 (RS 31 B)) (DPNode (MkDag
    29 (bs6 hf3 hf3 he7 hf2 hfc hbf) R0 R0 (RS 65 E) (RS 66 C)) (DPNode (MkDag 12 (bs6 h9f he5 he7 hf3 hcb hcf) R0
    (RS 129 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs6 hb9 hfc hbe h79 h7c hf7) R0 (RS 193 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 hf9 hee h5f h3c hf2 hf9) R0 R0 R0 (RS 97 A)) (DPNode (MkDag 10 (bs6 h79 hff hcf
    he7 hfc hff) (RS 161 B) R0 R0 (RS 12 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 24 (bs6 he7 hf9 he5 hf9 h7e
    h7e) (RS 48 D) R0 R0 (RS 49 B)) (DPNode (MkDag 38 (bs6 hb9 hff hfc hff he5 hf7) R0 R0 R0 (RS 81 C)) (DPNode
    (MkDag 51 (bs6 h9e he7 hf7 h3c hff hcf) R0 (RS 145 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hff h97 hcb
    hcf h9e h79) R0 R0 R0 (RS 209 A)) DPEmpty DPEmpty)) (DPNode (MkDag 21 (bs6 hf9 hfd hf2 hfc hfd hcb) R0 (RS 113
    A) R0 R0) (DPNode (MkDag 51 (bs6 h9f h9f hcf hfc hff hcf) R0 (RS 177 B) R0 R0) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 17 (bs6 hbf h3c hbf h3c hf2 hfb) R0 (RS 25 C) R0 R0) (DPNode (MkDag 23 (bs6 h7e h5f h73 hcb hdc
    hfe) (RS 41 C) R0 R0 R0) (DPNode (MkDag 33 (bs6 hf9 he7 h97 hcf hf2 hfb) R0 R0 R0 (RS 73 A)) (DPNode (MkDag 1
    (bs6 hb9 hfd hcf hdc hbe h79) R0 R0 R0 (RS 137 C)) DPEmpty DPEmpty) (DPNode (MkDag 50 (bs6 h7f h97 hcb hdc hff
    hf3) R0 R0 R0 (RS 199 B)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 h7c hbe h7e h5f h73 hcb) R0 R0 R0 (RS 8 B))
    (DPNode (MkDag 7 (bs6 h73 hcf hff h2f h73 hcb) R0 R0 R0 (RS 167 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    25 (bs6 hcf h9f hcf hcf h9e h5f) R0 R0 R0 (RS 57 A)) (DPNode (MkDag 42 (bs6 hf7 hcb hf3 hf9 hfc hf3) R0 R0 (RS
    89 E) (RS 90 C)) (DPNode (MkDag 8 (bs6 h79 hfc hbe h79 h7c hf7) (RS 154 E) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 49 (bs6 hcb hf3 hcf he5 hee h7f) (RS 120 D) R0 R0 (RS 121 B)) (DPNode (MkDag 4 (bs6 h7b h9f hff
    h3c hff hb9) R0 R0 R0 (RS 5 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_17 : DagPTree :=
  DPNode (MkDag 10 (bs6 hf9 hff hcf he7 hfc hff) (RS 12 D) R0 R0 (RS 162 A)) (DPNode (MkDag 15 (bs6 hfc hfc hbf h2f
    h9f hcb) R0 R0 (RS 21 E) (RS 22 A)) (DPNode (MkDag 1 (bs6 h73 hcb hcf hfe h7f hcb) R0 R0 R0 (RS 35 B)) (DPNode
    (MkDag 31 (bs6 h7f h2f h73 hfb h9e h7e) R0 R0 R0 (RS 69 B)) (DPNode (MkDag 9 (bs6 hcf he7 hcf hfc hfe h5f) R0
    R0 R0 (RS 133 D)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h7f hcf hff h2f h73 hcb) (RS 197 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 32 (bs6 hf3 hee h79 he5 hf7 h2f) R0 (RS 101 C) R0 R0) (DPNode (MkDag 0 (bs6 h9e he7
    hf7 h3f h72 hfb) R0 (RS 165 A) R0 (RS 165 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 16 (bs6 hfc hff h3f hcf
    h3f hcf) (RS 52 D) R0 R0 (RS 53 B)) (DPNode (MkDag 40 (bs6 hf7 h3f h9f hdf he7 hf9) R0 (RS 85 C) R0 R0) (DPNode
    (MkDag 0 (bs6 hcb he7 hf7 h3f h72 hfb) (RS 148 D) R0 R0 (RS 149 D)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h77
    h2f hff h3c hbe h79) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hb9 h7c hf3 hcf hf2 hfb) R0 (RS
    117 C) R0 R0) (DPNode (MkDag 49 (bs6 hfc hbd hcf he5 hee h7f) R0 R0 (RS 181 E) (RS 182 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 18 (bs6 h9f he7 hf7 h3f h9f hff) R0 R0 R0 (RS 29 C)) (DPNode (MkDag 21 (bs6 h7f hb9
    h7c hbe h7b h9f) R0 R0 R0 (RS 43 B)) (DPNode (MkDag 36 (bs6 hb9 he7 h9e h5f h3f hfb) R0 (RS 77 C) R0 R0)
    (DPNode (MkDag 6 (bs6 hf3 hff hcb hcf h9e h79) (RS 140 D) R0 R0 (RS 141 A)) DPEmpty DPEmpty) (DPNode (MkDag 3
    (bs6 h7f h97 hcb hdc hbd hcf) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty)) (DPNode (MkDag 46 (bs6 h9e h7c hbc hfc hfe
    h79) R0 (RS 109 B) R0 R0) (DPNode (MkDag 9 (bs6 h9f h9f hcf hfc hfe h5f) R0 (RS 173 B) R0 R0) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 27 (bs6 hf3 hcf h9f hcf h3f hfc) R0 R0 (RS 61 E) (RS 62 C)) (DPNode (MkDag 43 (bs6 hee
    h5f h3e h7b hfe h7e) (RS 92 D) R0 R0 (RS 93 B)) (DPNode (MkDag 3 (bs6 he7 h97 hcb hdc hbd hcf) (RS 156 D) R0 R0
    (RS 157 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs6 hf3 hff h3f h3f h9e h79) R0 R0 (RS 125 E) (RS 126
    C)) (DPNode (MkDag 7 (bs6 hcf hcf hff h2f h73 hcb) R0 R0 R0 (RS 189 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_18 : DagPTree :=
  DPNode (MkDag 8 (bs6 hcb hdc hbe h79 h7c hf7) (RS 10 D) R0 R0 (RS 169 C)) (DPNode (MkDag 14 (bs6 h5e h7f he7 hcf
    h3c hff) (RS 19 B) R0 R0 R0) (DPNode (MkDag 21 (bs6 h73 hcb he7 h9f h3f h9e) R0 R0 R0 (RS 33 B)) (DPNode (MkDag
    30 (bs6 hf3 hcf hef hf9 he5 hf9) R0 R0 (RS 67 E) (RS 68 B)) (DPNode (MkDag 8 (bs6 hf9 h7f hfe h79 h7c hf7) (RS
    130 D) R0 R0 (RS 131 D)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h5e he7 hf7 h3f h72 hfb) (RS 195 B) R0 R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hf9 hfe h5f h3c hf2 hf9) (RS 98 D) R0 R0 (RS 99 A)) (DPNode (MkDag 6
    (bs6 hbf h3c hbf h3f h9e h79) R0 (RS 163 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 16 (bs6 hdc hff
    h3f hcf h3f hcf) R0 R0 R0 (RS 51 A)) (DPNode (MkDag 38 (bs6 h79 hff hfc hff he5 hf7) R0 R0 R0 (RS 81 B))
    (DPNode (MkDag 51 (bs6 h9f he7 hf7 h3c hff hcf) R0 (RS 147 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 10 (bs6
    h7f h7f hcf he7 hfc hff) R0 R0 R0 (RS 211 B)) DPEmpty DPEmpty)) (DPNode (MkDag 47 (bs6 hf9 hfb h97 hdc hbe h5f)
    R0 R0 (RS 115 E) (RS 116 A)) (DPNode (MkDag 1 (bs6 hff h9f hcf hdc hbe h79) R0 R0 R0 (RS 179 D)) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 18 (bs6 h9e he7 hf7 h3f h9f hff) R0 R0 R0 (RS 27 A)) (DPNode (MkDag 20 (bs6
    h7e h5e h7f h3c hbf hf9) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 35 (bs6 h79 he7 hfe h5f h97 hcf) R0 R0 R0 (RS 75
    B)) (DPNode (MkDag 1 (bs6 h79 hfd hcf hdc hbe h79) R0 R0 R0 (RS 137 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6
    hfb h97 hcf hdc hfd hcf) R0 R0 R0 (RS 203 A)) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs6 h5f he7 h9f hf9 hfc hf7)
    (RS 107 B) R0 R0 R0) (DPNode (MkDag 39 (bs6 h7f h9f hcb hfc hbd hcf) R0 R0 R0 (RS 169 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 26 (bs6 hfb h9f hf2 hfc hfc hfc) R0 (RS 59 A) R0 R0) (DPNode (MkDag 42 (bs6 hbf hcb
    hf3 hf9 hfc hf3) R0 R0 (RS 91 E) R0) (DPNode (MkDag 9 (bs6 h67 h97 hcf hfc hfe h5f) R0 R0 R0 (RS 155 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h5f hfc hf7 h3c hfd hcf) (RS 123 B) R0 R0 R0) (DPNode (MkDag 51
    (bs6 hf3 he5 hf7 h3c hff hcf) (RS 186 D) R0 R0 (RS 13 D)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_19 : DagPTree :=
  DPNode (MkDag 11 (bs6 hcb hf2 hf9 hff h97 hcf) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 16 (bs6 h9f h2f hff h2f h97
    hcf) R0 (RS 23 C) R0 R0) (DPNode (MkDag 22 (bs6 h3e h79 he7 hdf hf3 hcf) R0 R0 R0 (RS 39 B)) (DPNode (MkDag 32
    (bs6 h9f h3f he7 hff h9f hcf) R0 (RS 71 B) R0 R0) (DPNode (MkDag 51 (bs6 hb9 he7 hcf hfc hff hcf) R0 (RS 135 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs6 h79 h7c hbe h79 h7c hf7) (RS 199 C) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 32 (bs6 hfe h7e h79 he5 hf7 h2f) R0 (RS 7 C) R0 R0) (DPNode (MkDag 0 (bs6 h9f he7 hf7 h3f h72
    hfb) R0 (RS 167 C) R0 (RS 167 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 22 (bs6 h5f h9f hcf h9f h97 hcf)
    (RS 55 B) R0 R0 R0) (DPNode (MkDag 40 (bs6 hff h3f h9f hdf he7 hf9) R0 (RS 87 A) R0 R0) (DPNode (MkDag 49 (bs6
    h79 hff hf9 h7c hbe h7f) (RS 151 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h3f h2f hff h3c hbe h79)
    R0 R0 R0 (RS 162 A)) DPEmpty DPEmpty)) (DPNode (MkDag 48 (bs6 hb9 h7c hf3 hf3 hf3 hcb) R0 (RS 119 C) R0 R0)
    (DPNode (MkDag 10 (bs6 h7c hff hcf he7 hfc hff) R0 R0 R0 (RS 183 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    19 (bs6 h73 he7 he7 hbe h5f hf9) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 21 (bs6 h3f hf9 h7c hbe h7f h9f) R0 R0 R0
    (RS 47 B)) (DPNode (MkDag 37 (bs6 hb9 he7 hf3 hfc hbe h7b) R0 (RS 79 C) R0 R0) (DPNode (MkDag 2 (bs6 h7f h3c
    hbf h3c hfd hcf) R0 R0 R0 (RS 143 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f h97 hcf hdc hbe h79) R0 (RS
    207 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hf9 he7 hf7 hfc hbd hcf) (RS 110 D) R0 R0 (RS 111 A))
    (DPNode (MkDag 51 (bs6 h7b h9f hcf hfc hff hcf) R0 R0 R0 (RS 175 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    28 (bs6 hf3 hf9 hf7 h2f h9f hff) (RS 62 D) R0 (RS 63 E) (RS 64 C)) (DPNode (MkDag 43 (bs6 hfe h5e h7e h7f hfe
    h7e) R0 R0 (RS 95 E) (RS 6 B)) (DPNode (MkDag 53 (bs6 hbf hff h72 hff hf2 hf7) R0 (RS 159 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs6 hbe he5 hf7 h2f h73 hcb) R0 R0 (RS 9 E) R0) (DPNode (MkDag 49 (bs6 hf9
    hff hf9 h7c hbe h7f) R0 (RS 191 A) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_20 : DagPTree :=
  DPNode (MkDag 7 (bs6 h3e he5 hf7 h2f h73 hcb) R0 R0 R0 (RS 127 B)) (DPNode (MkDag 13 (bs6 h7f h72 hfe h5f hf3
    hcb) (RS 18 B) R0 R0 R0) (DPNode (MkDag 21 (bs6 hf3 hcb he7 h9f h3f h9e) R0 R0 (RS 34 E) (RS 35 C)) (DPNode
    (MkDag 29 (bs6 h73 hf3 he7 hf2 hfc hbf) R0 R0 R0 (RS 64 B)) (DPNode (MkDag 8 (bs6 h79 h7f hfe h79 h7c hf7) R0
    R0 R0 (RS 130 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs6 hf9 hfc hbe h79 h7c hf7) (RS 193 D) (RS 155 B) R0 (RS
    155 B)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hb9 hfe h5f h3c hf2 hf9) R0 (RS 98 C) R0 R0) (DPNode (MkDag 6
    (bs6 h7f h3c hbf h3f h9e h79) (RS 194 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 16 (bs6 h7c hf7
    h3f hcf h3f hcf) (RS 50 D) R0 R0 R0) (DPNode (MkDag 38 (bs6 hf9 hff hfc hff he5 hf7) R0 R0 (RS 82 E) (RS 83 A))
    (DPNode (MkDag 51 (bs6 h97 he7 hf7 h3c hff hcf) R0 R0 R0 (RS 146 A)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h9e
    h7f hf3 hcb hf3 hcb) R0 (RS 210 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 47 (bs6 hb9 hfb h97 hdc hbe h5f) R0
    R0 R0 (RS 114 C)) (DPNode (MkDag 1 (bs6 h7f h9f hcf hdc hbe h79) R0 R0 R0 (RS 178 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 17 (bs6 hff h3c hbf h3c hf2 hfb) R0 (RS 26 A) R0 R0) (DPNode (MkDag 20 (bs6 hfe h5e
    h7f h3c hbf hf9) R0 R0 (RS 42 E) (RS 43 C)) (DPNode (MkDag 34 (bs6 h9f h3c hf3 hcf h9e h5f) R0 (RS 74 B) R0 R0)
    (DPNode (MkDag 1 (bs6 hf9 hfd hcf hdc hbe h79) R0 R0 (RS 138 E) (RS 139 A)) DPEmpty DPEmpty) (DPNode (MkDag 2
    (bs6 h7b h97 hcf hdc hfd hcf) R0 R0 R0 (RS 202 B)) DPEmpty DPEmpty)) (DPNode (MkDag 45 (bs6 h7c hbc hff hfc hf2
    hff) (RS 106 B) R0 R0 R0) (DPNode (MkDag 39 (bs6 hff h9f hcb hfc hbd hcf) R0 R0 (RS 170 E) (RS 171 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 26 (bs6 hbb h9f hf2 hfc hfc hfc) R0 (RS 58 C) R0 R0) (DPNode (MkDag 42 (bs6
    h77 hcb hf3 hf9 hfc hf3) R0 R0 R0 (RS 88 B)) (DPNode (MkDag 52 (bs6 hf9 hfc hbf hf3 he5 hff) R0 R0 (RS 151 E)
    (RS 192 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h7b hfc hf7 h3c hfd hcf) (RS 122 B) R0 R0 R0)
    (DPNode (MkDag 4 (bs6 h9f h9f hff h3c hff hb9) R0 (RS 186 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_21 : DagPTree :=
  DPNode (MkDag 6 (bs6 hcf h3c hbf h3f h9e h79) R0 R0 R0 (RS 187 D)) (DPNode (MkDag 15 (bs6 h7c hfc hbf h2f h9f
    hcb) R0 R0 R0 (RS 20 B)) (DPNode (MkDag 22 (bs6 hbe h79 he7 hdf hf3 hcf) R0 R0 (RS 38 E) R0) (DPNode (MkDag 31
    (bs6 hff h2f h73 hfb h9e h7e) R0 R0 R0 (RS 70 A)) (DPNode (MkDag 2 (bs6 hcf hcf hcf hdc hfd hcf) R0 R0 R0 (RS
    134 A)) DPEmpty DPEmpty) (DPNode (MkDag 52 (bs6 h79 h7c hbf hf3 he5 hff) (RS 198 B) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 32 (bs6 hbe h7e h79 he5 hf7 h2f) R0 (RS 102 C) R0 R0) (DPNode (MkDag 0 (bs6 h97 he7 hf7 h3f h72
    hfb) R0 (RS 166 A) R0 (RS 166 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 22 (bs6 h7b h9f hcf h9f h97 hcf)
    (RS 54 B) R0 R0 R0) (DPNode (MkDag 40 (bs6 hbf h3f h9f hdf he7 hf9) R0 (RS 86 C) R0 R0) (DPNode (MkDag 7 (bs6
    hcb hcf hff h2f h73 hcb) R0 R0 R0 (RS 150 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hbf h2f hff h3c hbe h79)
    R0 R0 (RS 214 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 h7c hf3 hcf hf2 hfb) (RS 117 D) R0 R0 (RS 118
    A)) (DPNode (MkDag 49 (bs6 h7c hbd hcf he5 hee h7f) R0 R0 R0 (RS 180 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 19 (bs6 hf3 he7 he7 hbe h5f hf9) R0 R0 (RS 30 E) (RS 31 C)) (DPNode (MkDag 21 (bs6 hbf hf9 h7c hbe h7f
    h9f) R0 R0 (RS 46 E) R0) (DPNode (MkDag 36 (bs6 hf9 he7 h9e h5f h3f hfb) (RS 77 D) R0 R0 (RS 78 A)) (DPNode
    (MkDag 7 (bs6 h9e h79 hf3 hcb hf3 hcb) R0 (RS 142 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7b h97 hcf
    hdc hbe h79) R0 R0 R0 (RS 3 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 h79 he7 hf7 hfc hbd hcf) R0 R0 R0 (RS
    110 B)) (DPNode (MkDag 2 (bs6 h7f h9f hcf hdc hfd hcf) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 27 (bs6 h73 hcf h9f hcf h3f hfc) R0 R0 R0 (RS 60 B)) (DPNode (MkDag 43 (bs6 h7e h5f h3e h7b hfe h7e) (RS
    94 C) R0 R0 R0) (DPNode (MkDag 1 (bs6 he7 h97 hcf hdc hbe h79) (RS 157 D) R0 R0 (RS 158 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 6 (bs6 h73 hff h3f h3f h9e h79) R0 R0 R0 (RS 124 B)) (DPNode (MkDag 49 (bs6 hb9 hff hf9
    h7c hbe h7f) R0 (RS 190 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_22 : DagPTree :=
  DPNode (MkDag 9 (bs6 hfb h9f hcf hfc hfe h5f) R0 R0 R0 (RS 172 A)) (DPNode (MkDag 14 (bs6 h7e h7f he7 hcf h3c
    hff) (RS 20 C) R0 R0 R0) (DPNode (MkDag 1 (bs6 hf3 hcb hcf hfe h7f hcb) R0 R0 (RS 36 E) (RS 37 C)) (DPNode
    (MkDag 30 (bs6 h73 hcf hef hf9 he5 hf9) R0 R0 R0 (RS 66 B)) (DPNode (MkDag 50 (bs6 hcf h3f hcb hdc hff hf3) R0
    R0 R0 (RS 132 D)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7e he7 hf7 h3f h72 hfb) (RS 196 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 44 (bs6 h9f h3e h79 h7c hf3 hcf) R0 (RS 100 C) R0 R0) (DPNode (MkDag 6 (bs6 hff h3c
    hbf h3f h9e h79) (RS 163 D) (RS 164 A) R0 (RS 164 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 16 (bs6 hbc hff
    h3f hcf h3f hcf) R0 (RS 52 C) R0 R0) (DPNode (MkDag 39 (bs6 h9f h3e h5f h9f hf2 hff) R0 (RS 84 C) R0 R0)
    (DPNode (MkDag 1 (bs6 hf3 hcf hff h3c hbe h79) R0 (RS 148 D) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 10 (bs6 hff
    h7f hcf he7 hfc hff) R0 R0 R0 (RS 1 C)) DPEmpty DPEmpty)) (DPNode (MkDag 47 (bs6 h79 hfb h97 hdc hbe h5f) R0 R0
    R0 (RS 114 B)) (DPNode (MkDag 7 (bs6 hcb hdf hf3 hcb hf3 hcb) R0 R0 R0 (RS 180 C)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 18 (bs6 h97 he7 hf7 h3f h9f hff) R0 (RS 28 A) R0 R0) (DPNode (MkDag 21 (bs6 hff hb9 h7c hbe h7b
    h9f) R0 R0 (RS 44 E) (RS 45 C)) (DPNode (MkDag 35 (bs6 hf9 he7 hfe h5f h97 hcf) R0 R0 R0 (RS 76 A)) (DPNode
    (MkDag 6 (bs6 h9f h7f hcb hcf h9e h79) R0 (RS 140 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h9f h97 hcf
    hdc hfd hcf) R0 (RS 204 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs6 h7f he7 h9f hf9 hfc hf7) (RS 108 A)
    R0 R0 R0) (DPNode (MkDag 9 (bs6 h7b h9f hcf hfc hfe h5f) R0 R0 R0 (RS 11 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 26 (bs6 h9f h9f hf2 hfc hfc hfc) R0 R0 R0 (RS 60 C)) (DPNode (MkDag 42 (bs6 h3f hcb hf3 hf9 hfc hf3) R0
    R0 R0 (RS 92 B)) (DPNode (MkDag 9 (bs6 he7 h97 hcf hfc hfe h5f) (RS 155 D) R0 R0 (RS 156 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 2 (bs6 h7f hfc hf7 h3c hfd hcf) (RS 124 C) R0 R0 R0) (DPNode (MkDag 54 (bs6 hcf he7 h9f
    h3f h9e h5e) R0 R0 R0 (RS 0 D)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_7_23 : DagPTree :=
  DPNode (MkDag 12 (bs6 h79 hf2 hf9 hfb h97 h9f) (RS 16 B) R0 R0 R0) (DPNode (MkDag 17 (bs6 hf7 h3c hbf h3c hf2
    hfb) R0 (RS 24 C) R0 R0) (DPNode (MkDag 23 (bs6 hee h5f h73 hcb hdc hfe) R0 R0 R0 (RS 40 B)) (DPNode (MkDag 33
    (bs6 h79 he7 h97 hcf hf2 hfb) R0 R0 R0 (RS 72 B)) (DPNode (MkDag 51 (bs6 hf9 he7 hcf hfc hff hcf) R0 (RS 136 A)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 50 (bs6 hff h97 hcb hdc hff hf3) R0 R0 (RS 200 E) (RS 201 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs6 hfc hbe h79 hff h9e h79) R0 (RS 104 B) R0 R0) (DPNode (MkDag 7 (bs6 hf3 hcf hff
    h2f h73 hcb) R0 (RS 10 D) (RS 168 E) (RS 10 D)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 22 (bs6 h7f h9f hcf
    h9f h97 hcf) (RS 56 D) R0 R0 R0) (DPNode (MkDag 41 (bs6 h9f h3f h3f hff he7 hcf) R0 R0 R0 (RS 88 C)) (DPNode
    (MkDag 52 (bs6 h79 hfc hbf hf3 he5 hff) (RS 152 B) R0 R0 (RS 153 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    48 (bs6 hf9 h7c hf3 hf3 hf3 hcb) R0 (RS 120 D) R0 R0) (DPNode (MkDag 10 (bs6 hfc hff hcf he7 hfc hff) R0 R0 R0
    (RS 184 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 20 (bs6 hf3 hf3 he7 hee h5f hf9) R0 R0 (RS 32 E) (RS 33
    C)) (DPNode (MkDag 24 (bs6 he7 hb9 he5 hf9 h7e h7e) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 37 (bs6 hf9 he7 hf3 hfc
    hbe h7b) R0 (RS 80 A) R0 R0) (DPNode (MkDag 2 (bs6 hff h3c hbf h3c hfd hcf) (RS 143 D) R0 R0 (RS 144 A))
    DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h7f h97 hcb hcf h9e h79) R0 R0 R0 (RS 208 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 21 (bs6 hb9 hfd hf2 hfc hfd hcb) R0 (RS 112 C) R0 R0) (DPNode (MkDag 51 (bs6 hfb h9f hcf hfc hff hcf) R0
    R0 R0 (RS 176 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs6 h73 hf9 hf7 h2f h9f hff) R0 R0 R0 (RS 62
    B)) (DPNode (MkDag 43 (bs6 h7e h5e h7e h7f hfe h7e) R0 R0 R0 (RS 94 B)) (DPNode (MkDag 53 (bs6 hff hff h72 hff
    hf2 hf7) (RS 159 D) (RS 160 B) R0 (RS 160 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs6 he7 he5 hf7 h2f
    h73 hcb) (RS 127 D) R0 R0 (RS 128 A)) (DPNode (MkDag 52 (bs6 hb9 hfc hbf hf3 he5 hff) R0 R0 R0 (RS 153 C))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_7 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hcf he7 hf7 h3f h72 hfb) R0 R0 R0 (RS 188 D)) (DPNode (MkDag 1 (bs6 hf7 h2f hff h3c hbe
    h79) (RS 1 D) R0 (RS 212 E) (RS 213 C)) (DPNode (MkDag 2 (bs6 hff h9f hcf hdc hfd hcf) R0 R0 R0 (RS 174 B))
    (DPNode (MkDag 3 (bs6 hff h97 hcb hdc hbd hcf) R0 R0 R0 (RS 205 B)) dagSub_7_16 dagSub_7_17) (DPNode (MkDag 5
    (bs6 h79 hee h5f h3c hf2 hf9) R0 R0 R0 (RS 96 B)) dagSub_7_18 dagSub_7_19)) (DPNode (MkDag 1 (bs6 hfb h97 hcf
    hdc hbe h79) R0 R0 R0 (RS 206 A)) (DPNode (MkDag 4 (bs6 hfb h9f hff h3c hff hb9) R0 R0 R0 (RS 185 A))
    dagSub_7_20 dagSub_7_21) (DPNode (MkDag 6 (bs6 hbc hbe h79 hff h9e h79) R0 (RS 103 C) R0 R0) dagSub_7_22
    dagSub_7_23))).

Definition dagTree_8 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hb9 h7f h97 hf3 hcb hff) R0 R0 R0 (RS 31 C)) (DPNode (MkDag 1 (bs6 h79 h7f h9e h5f h3c
    hf3) (RS 23 B) R0 R0 R0) (DPNode (MkDag 2 (bs6 h3f hf9 h7c hf9 hfc hf9) R0 R0 R0 (RS 35 A)) (DPNode (MkDag 4
    (bs6 hf9 h7f h73 hf9 hfc hf9) R0 (RS 3 A) (RS 34 E) (RS 3 A)) (DPNode (MkDag 6 (bs6 hcf h2f hcf h3f hfc hf9) R0
    R0 R0 (RS 9 A)) (DPNode (MkDag 10 (bs6 hf3 hcf h2f h97 hcb hf7) R0 R0 (RS 17 E) (RS 18 C)) (DPNode (MkDag 4
    (bs6 hb9 h7f h73 hf9 hfc hf9) R0 (RS 4 C) R0 (RS 4 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs6 hff hf3
    hf9 hf9 h7c hff) R0 (RS 32 A) (RS 33 E) (RS 32 A)) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs6 hf9 hfd hcf hcf hfe
    h7f) R0 R0 (RS 13 E) (RS 14 A)) (DPNode (MkDag 1 (bs6 hb9 h7f h9e h5f h3c hf3) R0 (RS 6 C) R0 R0) (DPNode
    (MkDag 13 (bs6 hff hcf h3f hff h3f h3d) R0 (RS 0 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs6 h79
    h7f hf3 hf9 hf9 hf9) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 hf9 h7f h9e h5f h3c hf3) (RS
    6 D) (RS 21 A) R0 (RS 21 A)) (DPNode (MkDag 7 (bs6 hf9 he7 hcf hee h5e h7c) R0 (RS 11 A) R0 R0) (DPNode (MkDag
    11 (bs6 hff hf2 hf7 h2f h97 hb9) (RS 18 D) R0 (RS 19 E) (RS 20 A)) (DPNode (MkDag 4 (bs6 h79 h7f h73 hf9 hfc
    hf9) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs6 hf9 h7f hf3 hf9 hf9 hf9) R0 (RS 27 C)
    (RS 28 E) (RS 27 C)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 h9f h7f hb9 h7c hff hff) R0 (RS 15 C) R0 R0)
    (DPNode (MkDag 12 (bs6 hbf hf3 hf9 hf9 h7c hff) R0 (RS 24 C) (RS 25 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs6 h79 h7f h97 hf3 hcb hff) (RS 1 B) R0 R0 (RS 31 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 3 (bs6 hb9 h7f hf3
    hf9 hf9 hf9) R0 (RS 26 C) R0 (RS 26 C)) (DPNode (MkDag 5 (bs6 hf9 h7b h9e h7f h3f hb9) R0 (RS 22 C) (RS 23 E)
    (RS 22 C)) (DPNode (MkDag 7 (bs6 hb9 he7 hcf hee h5e h7c) R0 (RS 10 C) R0 R0) (DPNode (MkDag 10 (bs6 h73 hcf
    h2f h97 hcb hf7) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 12 (bs6 h7f hf3 hf9 hf9 h7c hff) R0 R0 R0 (RS 24 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs6 h3f hf3 hf9 hf9 h7c hff) R0 R0 R0 (RS 3 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 8 (bs6 h79 hfd hcf hcf hfe h7f) R0 R0 R0 (RS 12 B)) (DPNode (MkDag 5 (bs6 hb9 h7b h9e h7f h3f
    hb9) R0 (RS 5 C) R0 (RS 5 C)) DPEmpty DPEmpty) (DPNode (MkDag 13 (bs6 h9f hcf h3f hff h3f h3d) R0 R0 R0 (RS 30
    B)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hff hf9 h7c hf9 hfc hf9) R0 (RS 29 A) R0 R0) (DPNode (MkDag 8 (bs6
    hb9 hfd hcf hcf hfe h7f) R0 R0 R0 (RS 12 C)) (DPNode (MkDag 11 (bs6 h7f hf2 hf7 h2f h97 hb9) R0 R0 R0 (RS 18
    B)) (DPNode (MkDag 13 (bs6 hbf hcf h3f hff h3f h3d) R0 (RS 36 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 2 (bs6 hbf hf9 h7c hf9 hfc hf9) R0 (RS 7 C) (RS 2 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 hf3 hff
    hb9 h7c hff hff) (RS 15 D) R0 R0 (RS 16 C)) (DPNode (MkDag 5 (bs6 h79 h7b h9e h7f h3f hb9) (RS 24 C) R0 R0 (RS
    5 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf9 h7f h97 hf3 hcb hff) R0 R0 (RS 30 E) (RS 20 A)) DPEmpty
    DPEmpty))))).

Definition dagSub_9_24 : DagPTree :=
  DPNode (MkDag 0 (bs6 h7f h9f hcf h3e he5 hff) (RS 81 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h9f hcf h2f h3e he5 hff)
    R0 (RS 7 A) R0 (RS 7 A)) (DPNode (MkDag 6 (bs6 hfc hbd hcf hee h79 hfc) (RS 32 D) R0 R0 (RS 33 B)) (DPNode
    (MkDag 6 (bs6 hfc hbe he7 h9f hf9 hfc) R0 R0 (RS 65 E) (RS 66 B)) (DPNode (MkDag 4 (bs6 h7b h97 hfe h7c hfe
    he7) R0 R0 R0 (RS 129 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h3d hff h3c hfd hf9 hfc) R0 R0 R0 (RS 193 C))
    DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hfc hfc hbc hf3 he5 hff) R0 R0 R0 (RS 9 B)) (DPNode (MkDag 2 (bs6 h7c
    hfe h7f h9f hf7 h2f) R0 R0 R0 (RS 161 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f hcb hdc hbe he5 hfe) (RS
    206 C) R0 R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 4 (bs6 h7d hcf he7 hf2 hfe he7) R0 R0 R0 (RS 49 B)) (DPNode
    (MkDag 0 (bs6 h5f h9f hcf h3e he5 hff) (RS 8 B) R0 R0 R0) (DPNode (MkDag 5 (bs6 h7d hcf he5 hf3 hf9 hf9) R0 R0
    R0 (RS 12 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hbd hcf he5 hf3 hf9 hf9) R0 (RS 12 C) (RS 17 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 haf h3c hf9 hf7 he5 hff) R0 R0 (RS 113 E) R0) (DPNode (MkDag 3 (bs6 hfb
    hfc hf9 hf7 he5 hff) (RS 176 D) R0 R0 (RS 240 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h9f hfc hf9 hf7 he5
    hff) R0 (RS 241 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs6 hff hcf h2f h3e he5 hff) (RS 24 D) R0 (RS
    233 E) (RS 234 C)) (DPNode (MkDag 5 (bs6 he5 hf3 hf9 hf2 hf9 hf9) R0 R0 R0 (RS 41 C)) (DPNode (MkDag 6 (bs6 h9e
    h5f h3f h2f hf9 hfc) R0 (RS 73 A) R0 R0) (DPNode (MkDag 4 (bs6 hff hcf he5 hf2 hfe he7) (RS 136 D) R0 (RS 137
    E) (RS 138 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hbc hbc hf9 hf7 he5 hff) R0 (RS 201 C) (RS 202 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hfe h5f h2f h9e he5 hfe) (RS 104 D) R0 R0 (RS 105 C)) (DPNode (MkDag 5
    (bs6 h73 hcf he5 hf3 hf9 hf9) R0 R0 R0 (RS 166 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h3c hfe h7b h9f hf7
    h2f) R0 R0 R0 (RS 236 C)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6 hbf hcf he7 hf3 hf9 hfc) R0 R0 (RS 57 E) R0)
    (DPNode (MkDag 3 (bs6 hbc hbe he7 hf7 he5 hff) R0 R0 (RS 89 E) R0) (DPNode (MkDag 0 (bs6 hbf hcf h2f h3e he5
    hff) R0 R0 (RS 153 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h9f hcf he5 hf2 hfe he7) R0 (RS 22 A) R0 (RS
    22 A)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 he7 he7 he5 hf2 hff hdc) (RS 120 D) R0 R0 (RS 121 B)) (DPNode
    (MkDag 6 (bs6 haf hcf he5 hf3 hf9 hfc) R0 R0 (RS 185 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_25 : DagPTree :=
  DPNode (MkDag 5 (bs6 hfd hcf he5 hf3 hf9 hf9) R0 (RS 145 C) R0 (RS 145 C)) (DPNode (MkDag 2 (bs6 h7c hbe h7f h9f
    hf7 h2f) (RS 213 D) R0 R0 (RS 214 B)) (DPNode (MkDag 2 (bs6 hf9 hf9 he7 hef hf7 h2f) R0 (RS 37 C) R0 R0)
    (DPNode (MkDag 2 (bs6 he5 hf2 hf3 hf2 hf7 h2f) (RS 68 D) R0 R0 (RS 69 B)) (DPNode (MkDag 2 (bs6 he5 hee h7f h9f
    hf7 h2f) R0 R0 R0 (RS 133 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h3f hff h3c hfd hf9 hfc) R0 R0 R0 (RS 197
    C)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 hfc hbe he5 hf3 hf9 hfc) R0 R0 (RS 101 E) (RS 102 B)) (DPNode
    (MkDag 4 (bs6 hf3 hcf he5 hf2 hfe he7) (RS 164 D) (RS 13 C) (RS 165 E) (RS 13 C)) DPEmpty DPEmpty) (DPNode
    (MkDag 1 (bs6 he7 hcf he5 he7 he5 hfe) (RS 228 D) R0 R0 (RS 229 B)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6
    hbd hcf he7 hf3 hf9 hfc) R0 R0 (RS 53 E) R0) (DPNode (MkDag 7 (bs6 h9f h9f hcf hcf hbf hdc) R0 R0 R0 (RS 85 B))
    (DPNode (MkDag 0 (bs6 hfd hcf h2f h3e he5 hff) R0 (RS 210 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hfc
    hbe h7b h9f hf7 h2f) (RS 212 D) R0 R0 (RS 20 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hbf h3f h9f h3f he5
    hff) R0 (RS 117 C) R0 R0) (DPNode (MkDag 7 (bs6 hff hcf he5 hf2 hff hdc) (RS 180 D) R0 (RS 181 E) (RS 182 C))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 1 (bs6 hfd hcf h2f h9e he5 hfe) R0 R0 R0 (RS 24 C)) (DPNode (MkDag 6
    (bs6 h2f hcf h3f h2f hf9 hfc) R0 R0 R0 (RS 45 C)) (DPNode (MkDag 0 (bs6 h9e h5e h7c hf3 he5 hff) R0 (RS 77 B)
    R0 R0) (DPNode (MkDag 2 (bs6 haf hcf he5 hf2 hf7 h2f) R0 R0 (RS 11 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs6 hff hcb hdc hbe he5 hfe) R0 (RS 205 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hfe h7f hfb hfc hf9
    hf9) R0 R0 (RS 109 E) (RS 110 C)) (DPNode (MkDag 6 (bs6 h73 hff h3c hfd hf9 hfc) R0 R0 R0 (RS 169 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 hbc hfe h7f h9f hf7 h2f) R0 R0 (RS 237 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag
    1 (bs6 hfd hcf he7 he7 he5 hfe) R0 R0 R0 (RS 61 C)) (DPNode (MkDag 2 (bs6 h9f he5 hf3 hf2 hf7 h2f) R0 (RS 93 B)
    R0 R0) (DPNode (MkDag 2 (bs6 hdc hfe h7b h9f hf7 h2f) R0 R0 R0 (RS 231 A)) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs6 h97 hcf h2f h9e he5 hfe) R0 (RS 221 A) R0 (RS 221 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hfc hfe he5
    hf3 hf9 hf9) (RS 124 D) R0 R0 (RS 125 B)) (DPNode (MkDag 5 (bs6 he7 hcf he5 hf3 hf9 hf9) R0 R0 R0 (RS 189 B))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_26 : DagPTree :=
  DPNode (MkDag 0 (bs6 hee h5f h2f h3e he5 hff) R0 R0 R0 (RS 107 B)) (DPNode (MkDag 1 (bs6 h7f hcf h2f h9e he5 hfe)
    R0 R0 R0 (RS 14 B)) (DPNode (MkDag 2 (bs6 hcf hb9 he7 hef hf7 h2f) R0 R0 R0 (RS 35 A)) (DPNode (MkDag 3 (bs6
    he5 hff he7 hf7 he5 hff) (RS 66 D) R0 R0 (RS 67 B)) (DPNode (MkDag 4 (bs6 h9f h97 hfe h7c hfe he7) R0 (RS 131
    B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h2f hff h3c hfd hf9 hfc) R0 R0 R0 (RS 195 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs6 h9f h73 hff h2f hf9 hfc) R0 (RS 99 C) R0 R0) (DPNode (MkDag 3 (bs6 h7c hfc hf9
    hf7 he5 hff) (RS 13 C) R0 R0 (RS 163 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hbf hcf he5 hf3 hf9 hf9) R0 R0
    (RS 227 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs6 hff hcf he7 hf2 hff hdc) (RS 50 D) R0 (RS 51 E) (RS 52
    C)) (DPNode (MkDag 7 (bs6 hbb h9f hcf hcf hbf hdc) R0 (RS 83 C) R0 R0) (DPNode (MkDag 0 (bs6 hbd hcf h2f h3e
    he5 hff) R0 (RS 148 C) (RS 149 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hff hff h3c hfd hf9 hfc) R0 (RS
    211 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hbf h3c hf9 hf7 he5 hff) R0 R0 (RS 115 E) R0) (DPNode
    (MkDag 4 (bs6 hfd hcf he5 hf2 hfe he7) R0 R0 (RS 179 E) (RS 180 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    1 (bs6 hf3 hcf h2f h9e he5 hfe) (RS 26 D) (RS 169 C) (RS 170 E) (RS 169 C)) (DPNode (MkDag 6 (bs6 h3d hcf h3f
    h2f hf9 hfc) R0 R0 R0 (RS 43 C)) (DPNode (MkDag 7 (bs6 h9e h7f he7 hf2 hff hdc) R0 (RS 75 A) R0 R0) (DPNode
    (MkDag 2 (bs6 hbd hcf he5 hf2 hf7 h2f) R0 R0 (RS 139 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h3c hbc hf9
    hf7 he5 hff) R0 R0 R0 (RS 203 A)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 h3e h5f h2f h9f he5 hfe) R0 R0 R0 (RS
    10 B)) (DPNode (MkDag 1 (bs6 h73 hcf h2f h9e he5 hfe) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs6 hbc hf3 hff h97 he5 hff) R0 R0 (RS 235 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 5 (bs6 he7 hcf he7 hf3 hf9
    hf9) R0 R0 R0 (RS 59 B)) (DPNode (MkDag 4 (bs6 he7 hbf hcf hf2 hfe he7) R0 R0 R0 (RS 91 B)) (DPNode (MkDag 6
    (bs6 he7 hff h3c hfd hf9 hfc) R0 R0 R0 (RS 155 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h9f hcf he5 hf2 hf7
    h2f) R0 (RS 6 A) R0 (RS 6 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hdc hfe he5 hf3 hf9 hf9) R0 R0 R0 (RS 123
    A)) (DPNode (MkDag 6 (bs6 hbf hcf he5 hf3 hf9 hfc) R0 R0 (RS 187 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_27 : DagPTree :=
  DPNode (MkDag 1 (bs6 hff hcf h2f h9e he5 hfe) (RS 14 D) R0 (RS 18 E) (RS 191 C)) (DPNode (MkDag 7 (bs6 h97 hcf
    he5 hf2 hff hdc) R0 (RS 217 A) R0 (RS 217 A)) (DPNode (MkDag 4 (bs6 hfd hcf h3f hf2 hfe he7) R0 (RS 39 C) R0
    R0) (DPNode (MkDag 2 (bs6 he7 hf3 hcf h73 hf7 h2f) (RS 70 D) R0 R0 (RS 71 B)) (DPNode (MkDag 1 (bs6 h7d hcb hdc
    hbe he5 hfe) R0 R0 R0 (RS 135 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbc hbe h7f h9f hf7 h2f) R0 R0 (RS 199
    E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 he5 hff he5 hf3 hf9 hf9) R0 R0 R0 (RS 103 A)) (DPNode (MkDag 5
    (bs6 hf3 hcf he5 hf3 hf9 hf9) R0 (RS 26 C) (RS 168 E) (RS 26 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hcf hcf
    h2f h9e he5 hfe) R0 R0 R0 (RS 152 C)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6 haf hcf he7 hf3 hf9 hfc) R0 R0
    (RS 55 E) R0) (DPNode (MkDag 5 (bs6 hcf h3e he7 hfc hf9 hf9) R0 R0 R0 (RS 87 D)) (DPNode (MkDag 0 (bs6 haf hcf
    h2f h3e he5 hff) R0 R0 (RS 151 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hfc hbe h7f h9f hf7 h2f) (RS 214
    D) R0 R0 (RS 23 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 he7 h9f he5 hff he5 hff) (RS 118 D) R0 R0 (RS 119
    B)) (DPNode (MkDag 6 (bs6 hbd hcf he5 hf3 hf9 hfc) R0 R0 (RS 183 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 6 (bs6 hdc hbd hcf hee h79 hfc) R0 R0 R0 (RS 31 A)) (DPNode (MkDag 6 (bs6 h3f hcf h3f h2f hf9 hfc) R0 R0
    R0 (RS 47 B)) (DPNode (MkDag 7 (bs6 hff hfc hfc hf3 hff hdc) (RS 78 D) R0 R0 (RS 79 B)) (DPNode (MkDag 2 (bs6
    h3f hcf he5 hf2 hf7 h2f) R0 R0 R0 (RS 143 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hfd hcf he5 hf2 hff hdc)
    R0 (RS 25 C) (RS 207 E) (RS 25 C)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbe h7e h7b h9f hf7 h2f) R0 R0 (RS
    111 E) R0) (DPNode (MkDag 0 (bs6 h73 hf3 hff h97 he5 hff) R0 R0 R0 (RS 171 B)) DPEmpty DPEmpty) (DPNode (MkDag
    3 (bs6 hbc hfc hf9 hf7 he5 hff) R0 R0 (RS 3 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs6 h7f hcf hdc hf3 hff
    hdc) R0 R0 R0 (RS 61 B)) (DPNode (MkDag 2 (bs6 hfc hbd hcf hf3 hf7 h2f) R0 R0 R0 (RS 95 B)) (DPNode (MkDag 2
    (bs6 h7c hfe h7b h9f hf7 h2f) R0 R0 R0 (RS 159 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h9f hff h3c hfd hf9
    hfc) R0 (RS 20 B) R0 (RS 20 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hfd hff h2f h9f he5 hfe) R0 R0 (RS 127
    E) (RS 128 B)) (DPNode (MkDag 1 (bs6 hfd hcf he5 he7 he5 hfe) R0 R0 R0 (RS 14 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_28 : DagPTree :=
  DPNode (MkDag 6 (bs6 h79 hf3 hdf h2f hf9 hfc) R0 R0 R0 (RS 97 B)) (DPNode (MkDag 5 (bs6 h3d hcf he5 hf3 hf9 hf9)
    R0 R0 R0 (RS 225 C)) (DPNode (MkDag 1 (bs6 h7c hff hcf hcf he5 hfe) (RS 34 D) R0 R0 R0) (DPNode (MkDag 6 (bs6
    h7c hbe he7 h9f hf9 hfc) R0 R0 R0 (RS 64 B)) (DPNode (MkDag 4 (bs6 hfb h97 hfe h7c hfe he7) R0 R0 R0 (RS 130
    A)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 haf hff h3c hfd hf9 hfc) R0 R0 (RS 194 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 6 (bs6 hf9 hf3 hdf h2f hf9 hfc) R0 R0 R0 (RS 98 A)) (DPNode (MkDag 2 (bs6 hfc hfe h7f h9f hf7
    h2f) (RS 161 D) R0 R0 (RS 162 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 haf hcf he5 hf3 hf9 hf9) R0 R0 (RS 5
    E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 4 (bs6 hfd hcf he7 hf2 hfe he7) R0 R0 R0 (RS 50 C)) (DPNode (MkDag 0
    (bs6 hcf h9f hcf he7 he5 hff) R0 R0 R0 (RS 82 A)) (DPNode (MkDag 1 (bs6 hff hcf he5 he7 he5 hfe) (RS 145 D) (RS
    146 C) (RS 147 E) (RS 146 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7f hcf he5 hf2 hf7 h2f) R0 R0 R0 (RS 25
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 h2f h3c hf9 hf7 he5 hff) R0 R0 R0 (RS 114 C)) (DPNode (MkDag 3 (bs6
    h7f hfc hf9 hf7 he5 hff) (RS 178 C) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h97 hcb hdc hbe he5 hfe)
    R0 R0 R0 (RS 215 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs6 hff hcf he5 hf2 hf7 h2f) (RS 25 D) (RS 208 C)
    (RS 209 E) (RS 208 C)) (DPNode (MkDag 6 (bs6 hbd hcf h3f h2f hf9 hfc) R0 R0 (RS 42 E) R0) (DPNode (MkDag 4 (bs6
    h9e h5e he7 hf2 hfe he7) R0 R0 R0 (RS 74 A)) (DPNode (MkDag 4 (bs6 h7f hcf he5 hf2 hfe he7) R0 R0 R0 (RS 136
    B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hfc hbc hf9 hf7 he5 hff) (RS 201 D) (RS 215 A) R0 (RS 215 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hbe h5f h2f h9f he5 hfe) R0 R0 (RS 106 E) R0) (DPNode (MkDag 6 (bs6 hf3
    hff h3c hfd hf9 hfc) R0 (RS 171 C) (RS 172 E) (RS 171 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7f hcf h2f
    h3e he5 hff) R0 R0 R0 (RS 24 B)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6 h3f hcf he7 hf3 hf9 hfc) R0 R0 R0 (RS
    58 B)) (DPNode (MkDag 3 (bs6 h3c hbe he7 hf7 he5 hff) R0 R0 R0 (RS 90 B)) (DPNode (MkDag 0 (bs6 h3f hcf h2f h3e
    he5 hff) R0 R0 R0 (RS 154 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h9f hcf he5 hf2 hff hdc) R0 (RS 2 A) R0
    (RS 2 A)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 h7c hf3 he5 hf3 hf9 hfc) (RS 122 D) R0 R0 R0) (DPNode (MkDag
    6 (bs6 h2f hcf he5 hf3 hf9 hfc) R0 R0 R0 (RS 186 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_29 : DagPTree :=
  DPNode (MkDag 2 (bs6 hf3 hcf he5 hf2 hf7 h2f) R0 (RS 166 C) (RS 167 E) (RS 166 C)) (DPNode (MkDag 5 (bs6 h9f hcf
    he5 hf3 hf9 hf9) R0 (RS 1 A) R0 (RS 1 A)) (DPNode (MkDag 4 (bs6 hbd hcf h3f hf2 hfe he7) R0 (RS 38 C) R0 R0)
    (DPNode (MkDag 1 (bs6 he7 h9e h7f h3e he5 hfe) (RS 69 D) R0 R0 (RS 70 B)) (DPNode (MkDag 3 (bs6 he7 hfc hf9 hf7
    he5 hff) R0 R0 R0 (RS 134 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbc hbe h7b h9f hf7 h2f) R0 R0 (RS 19 E)
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 h7c hbe he5 hf3 hf9 hfc) R0 R0 R0 (RS 100 B)) (DPNode (MkDag 4 (bs6
    h73 hcf he5 hf2 hfe he7) R0 R0 R0 (RS 164 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7d hcf h2f h9e he5 hfe)
    (RS 230 D) R0 R0 (RS 28 B)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6 h3d hcf he7 hf3 hf9 hfc) R0 R0 R0 (RS 54
    C)) (DPNode (MkDag 3 (bs6 h7f h9f hff hcf he5 hff) (RS 86 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3d hcf h2f h3e
    he5 hff) R0 R0 R0 (RS 150 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hdc hbc hf9 hf7 he5 hff) R0 R0 R0 (RS 200
    A)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hff h3f h9f h3f he5 hff) (RS 117 D) R0 R0 (RS 118 B)) (DPNode
    (MkDag 7 (bs6 h7f hcf he5 hf2 hff hdc) R0 R0 R0 (RS 180 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 7 (bs6
    h7c hbe h79 h7e h79 hfc) (RS 30 D) R0 R0 R0) (DPNode (MkDag 6 (bs6 hbf hcf h3f h2f hf9 hfc) R0 R0 (RS 46 E) R0)
    (DPNode (MkDag 7 (bs6 h7f hfc hfc hf3 hff hdc) R0 R0 R0 (RS 78 B)) (DPNode (MkDag 2 (bs6 hbf hcf he5 hf2 hf7
    h2f) R0 R0 (RS 142 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hbd hcf he5 hf2 hff hdc) R0 (RS 206 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h7e h7f hfb hfc hf9 hf9) R0 R0 R0 (RS 108 B)) (DPNode (MkDag 3 (bs6 h7b
    hfc hf9 hf7 he5 hff) (RS 175 B) R0 R0 (RS 176 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h3c hfe h7f h9f hf7
    h2f) R0 R0 R0 (RS 238 C)) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs6 hff hcf hdc hf3 hff hdc) (RS 61 D) R0 (RS 62
    E) (RS 63 D)) (DPNode (MkDag 2 (bs6 h7c hbd hcf hf3 hf7 h2f) R0 R0 R0 (RS 94 B)) (DPNode (MkDag 0 (bs6 hfc hf3
    hff h97 he5 hff) R0 R0 R0 (RS 158 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f hcf h2f h9e he5 hfe) R0 (RS 0
    A) R0 (RS 0 A)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 h79 hff he5 he7 he5 hfe) (RS 126 C) R0 R0 R0) (DPNode
    (MkDag 1 (bs6 h7d hcf he5 he7 he5 hfe) R0 R0 R0 (RS 190 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_30 : DagPTree :=
  DPNode (MkDag 2 (bs6 h2f hcf he5 hf2 hf7 h2f) R0 R0 R0 (RS 141 C)) (DPNode (MkDag 2 (bs6 h3c hbe h7b h9f hf7 h2f)
    R0 R0 R0 (RS 198 C)) (DPNode (MkDag 2 (bs6 hb9 hf9 he7 hef hf7 h2f) R0 (RS 36 C) R0 R0) (DPNode (MkDag 7 (bs6
    he5 hf2 hf9 hf2 hff hdc) (RS 67 D) R0 R0 (RS 68 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hff h97 he5 hff) R0 R0 R0 (RS
    132 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hbf hff h3c hfd hf9 hfc) R0 R0 (RS 196 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 6 (bs6 hf3 hf3 hff h2f hf9 hfc) (RS 99 D) R0 R0 (RS 100 C)) (DPNode (MkDag 3 (bs6 hfc hfc hf9
    hf7 he5 hff) R0 R0 R0 (RS 164 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h3f hcf he5 hf3 hf9 hf9) R0 R0 R0 (RS
    228 B)) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs6 h7f hcf he7 hf2 hff hdc) R0 R0 R0 (RS 50 B)) (DPNode (MkDag 7
    (bs6 hfb h9f hcf hcf hbf hdc) R0 (RS 84 A) R0 R0) (DPNode (MkDag 1 (bs6 h7f hcf he5 he7 he5 hfe) R0 R0 R0 (RS
    145 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7c hbe h7b h9f hf7 h2f) R0 R0 R0 (RS 212 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 3 (bs6 h3f h3c hf9 hf7 he5 hff) R0 R0 R0 (RS 116 A)) (DPNode (MkDag 4 (bs6 h7d hcf he5 hf2 hfe
    he7) R0 R0 R0 (RS 178 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs6 h97 hcf he5 hf3 hf9 hf9) R0 (RS 21
    A) R0 (RS 21 A)) (DPNode (MkDag 6 (bs6 haf hcf h3f h2f hf9 hfc) R0 R0 (RS 44 E) R0) (DPNode (MkDag 6 (bs6 h9e
    h7e he7 hf3 hf9 hfc) R0 R0 R0 (RS 76 A)) (DPNode (MkDag 2 (bs6 h3d hcf he5 hf2 hf7 h2f) R0 R0 R0 (RS 140 C))
    DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hbf hcb hdc hbe he5 hfe) R0 (RS 204 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 h7e h5f h2f h3e he5 hff) (RS 108 C) R0 R0 R0) (DPNode (MkDag 0 (bs6 hf3 hf3 hff h97 he5 hff) (RS
    171 D) (RS 173 B) (RS 174 E) (RS 173 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3c hf3 hff h97 he5 hff) R0 R0
    R0 (RS 231 C)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 h7d hcf he7 he7 he5 hfe) R0 R0 R0 (RS 60 B)) (DPNode
    (MkDag 4 (bs6 he7 hff hcf hf2 hfe he7) R0 R0 R0 (RS 92 A)) (DPNode (MkDag 0 (bs6 h7c hf3 hff h97 he5 hff) (RS
    156 D) R0 R0 (RS 157 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h9f hcf he5 hf3 hf9 hfc) R0 (RS 27 A) R0 (RS 27
    A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hbc hfe he5 hf3 hf9 hf9) R0 (RS 124 C) R0 R0) (DPNode (MkDag 6 (bs6
    h3f hcf he5 hf3 hf9 hfc) R0 R0 R0 (RS 188 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_9_31 : DagPTree :=
  DPNode (MkDag 1 (bs6 h9f hcf he5 he7 he5 hfe) R0 (RS 220 A) R0 (RS 220 A)) (DPNode (MkDag 3 (bs6 h7c hbc hf9 hf7
    he5 hff) (RS 223 B) R0 R0 R0) (DPNode (MkDag 1 (bs6 hff hcf h2f h3e he5 hfe) R0 (RS 40 B) R0 R0) (DPNode (MkDag
    5 (bs6 he7 hf2 hf9 hf2 hf9 hf9) (RS 71 D) R0 R0 (RS 72 A)) (DPNode (MkDag 1 (bs6 hfd hcb hdc hbe he5 hfe) R0 R0
    R0 (RS 136 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h3c hbe h7f h9f hf7 h2f) R0 R0 R0 (RS 200 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 1 (bs6 hbe h5f h2f h9e he5 hfe) R0 (RS 104 C) R0 R0) (DPNode (MkDag 2 (bs6 h73 hcf he5
    hf2 hf7 h2f) R0 R0 R0 (RS 13 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbc hfe h7b h9f hf7 h2f) R0 (RS 159 C)
    (RS 232 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs6 h2f hcf he7 hf3 hf9 hfc) R0 R0 R0 (RS 56 C)) (DPNode
    (MkDag 5 (bs6 hcf he7 he7 hfc hf9 hf9) R0 R0 R0 (RS 88 C)) (DPNode (MkDag 0 (bs6 h2f hcf h2f h3e he5 hff) R0 R0
    R0 (RS 152 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f hcb hdc hbe he5 hfe) R0 (RS 4 A) R0 (RS 4 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 4 (bs6 he7 hf3 he5 hf2 hfe he7) (RS 119 D) R0 R0 (RS 120 B)) (DPNode (MkDag 6 (bs6 h3d
    hcf he5 hf3 hf9 hfc) R0 R0 R0 (RS 184 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 6 (bs6 hbc hbd hcf hee h79
    hfc) R0 (RS 32 C) R0 R0) (DPNode (MkDag 3 (bs6 he7 hcf he7 hff he5 hff) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 0
    (bs6 h7b h9f hcf h3e he5 hff) (RS 80 B) R0 R0 R0) (DPNode (MkDag 6 (bs6 he7 hcf he5 hf3 hf9 hfc) R0 R0 R0 (RS
    144 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h7d hcf he5 hf2 hff hdc) R0 R0 R0 (RS 206 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs6 h3e h7e h7b h9f hf7 h2f) R0 R0 R0 (RS 112 C)) (DPNode (MkDag 3 (bs6 h5f hfc hf9 hf7 he5
    hff) (RS 177 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hb3 hcf he5 hf2 hfe he7) R0 (RS 164 C) R0 R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hcb he7 he5 hef hf7 h2f) R0 R0 R0 (RS 64 C)) (DPNode (MkDag 3 (bs6 h7c
    hfc hbc hf3 he5 hff) R0 R0 R0 (RS 96 B)) (DPNode (MkDag 2 (bs6 hfc hfe h7b h9f hf7 h2f) R0 (RS 160 B) R0 (RS
    160 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h5f hcb hdc hbe he5 hfe) (RS 224 B) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 1 (bs6 h7d hff h2f h9f he5 hfe) R0 R0 R0 (RS 126 B)) (DPNode (MkDag 6 (bs6 hbd hff h3c hfd hf9
    hfc) R0 R0 (RS 192 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_9 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h97 hcf h2f h3e he5 hff) R0 (RS 16 A) R0 (RS 16 A)) (DPNode (MkDag 1 (bs6 h97 hcf he5
    he7 he5 hfe) R0 (RS 15 A) R0 (RS 15 A)) (DPNode (MkDag 2 (bs6 h97 hcf he5 hf2 hf7 h2f) R0 (RS 218 A) R0 (RS 218
    A)) (DPNode (MkDag 4 (bs6 h97 hcf he5 hf2 hfe he7) R0 (RS 216 A) R0 (RS 216 A)) dagSub_9_24 dagSub_9_25)
    (DPNode (MkDag 6 (bs6 h97 hcf he5 hf3 hf9 hfc) R0 (RS 219 A) R0 (RS 219 A)) dagSub_9_26 dagSub_9_27)) (DPNode
    (MkDag 3 (bs6 h3c hfc hf9 hf7 he5 hff) R0 R0 R0 (RS 239 A)) (DPNode (MkDag 5 (bs6 h2f hcf he5 hf3 hf9 hf9) R0
    R0 R0 (RS 226 C)) dagSub_9_28 dagSub_9_29) (DPNode (MkDag 6 (bs6 h97 hff h3c hfd hf9 hfc) R0 (RS 222 A) R0 (RS
    222 A)) dagSub_9_30 dagSub_9_31))).

Definition dagSub_10_32 : DagPTree :=
  DPNode (MkDag 1 (bs6 h2f h73 hcf h2f hff h3f) R0 R0 R0 (RS 115 C)) (DPNode (MkDag 3 (bs6 he7 hf2 hf9 he7 h9f hcf)
    R0 R0 R0 (RS 209 B)) (DPNode (MkDag 10 (bs6 hb9 h7c hfb h9f he7 he5) R0 (RS 33 C) R0 R0) (DPNode (MkDag 3 (bs6
    h97 hbf hcf hcf h3f hcf) R0 (RS 65 A) R0 R0) (DPNode (MkDag 3 (bs6 hf9 hf3 hf9 he7 h9f hcf) R0 R0 R0 (RS 136
    A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hbf h73 hcf hcf hff h3f) R0 R0 (RS 193 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 he5 hf3 hcf h7c hbf h3f) (RS 96 D) R0 R0 (RS 9 B)) (DPNode (MkDag 1 (bs6 h3c hf3 hcf hcf
    hff h3f) R0 R0 R0 (RS 161 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hfc hf3 hcb he7 h9f hcf) R0 R0 R0 (RS 225
    B)) DPEmpty DPEmpty))) (DPNode (MkDag 17 (bs6 h9f h9f h2f h9f hbe h5f) R0 (RS 49 C) R0 R0) (DPNode (MkDag 4
    (bs6 h79 hf3 hcb hcf hff h3f) (RS 81 B) R0 R0 R0) (DPNode (MkDag 4 (bs6 h3f hf3 hcb hcf hff h3f) R0 R0 R0 (RS
    204 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 he7 hf2 hf9 he7 h9f h3f) R0 R0 R0 (RS 16 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 3 (bs6 hbf h72 hf9 he7 h9f hcf) R0 R0 (RS 11 E) R0) (DPNode (MkDag 4 (bs6 h3c hf2 hf9 h7d hff
    h3f) R0 R0 R0 (RS 177 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf9 hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 241 A))
    DPEmpty DPEmpty)))) (DPNode (MkDag 8 (bs6 h3c hf9 hee h79 hff hee) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 13 (bs6
    hf9 hf9 hf3 hdc hf3 hff) R0 (RS 41 A) R0 R0) (DPNode (MkDag 26 (bs6 hff hcf hcf he5 hf7 h3c) R0 (RS 73 A) R0
    R0) (DPNode (MkDag 4 (bs6 h9f h73 hf9 h7d hff h3f) R0 (RS 137 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6
    h3f h73 hf9 h7d hff h3f) R0 R0 R0 (RS 131 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h2f hf3 hcf hfc hbf h3f)
    R0 R0 R0 (RS 105 C)) (DPNode (MkDag 6 (bs6 h3c hbe h79 he7 h9f h3f) R0 R0 R0 (RS 169 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 7 (bs6 hfc hf2 hf9 he7 h9f h3f) R0 R0 R0 (RS 233 B)) DPEmpty DPEmpty))) (DPNode (MkDag 23 (bs6
    hdc hbd hcf h3f h9e h5e) R0 R0 R0 (RS 57 A)) (DPNode (MkDag 27 (bs6 hfc hf3 hcf he7 hf7 h3f) (RS 88 D) R0 R0
    (RS 133 B)) (DPNode (MkDag 1 (bs6 he5 hf3 hcf h2f hff h3f) (RS 152 D) R0 R0 (RS 153 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 26 (bs6 h7c hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 217 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6
    hff hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 252 D)) (DPNode (MkDag 5 (bs6 haf h73 hcf he7 h97 hcf) R0 R0 (RS 185 E)
    R0) DPEmpty DPEmpty) (DPNode (MkDag 27 (bs6 h79 hf3 hcb he5 hf7 h3f) (RS 249 B) R0 R0 R0) DPEmpty DPEmpty)))).

Definition dagSub_10_33 : DagPTree :=
  DPNode (MkDag 0 (bs6 h7f hf3 hcf h7c hbf h3f) (RS 119 D) R0 R0 (RS 120 B)) (DPNode (MkDag 7 (bs6 h7f h73 hcb he7
    h9f h3f) (RS 250 D) R0 R0 R0) (DPNode (MkDag 12 (bs6 hb9 hff h9f hcf h97 hb9) R0 R0 R0 (RS 37 C)) (DPNode
    (MkDag 0 (bs6 h7e h7d hcf hfc hbf h3f) (RS 69 E) R0 R0 R0) (DPNode (MkDag 27 (bs6 h3f hf3 hcb he5 hf7 h3f) R0
    R0 R0 (RS 201 C)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h3f hf3 hf9 he7 h9f h3f) R0 R0 R0 (RS 197 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 27 (bs6 he5 hf3 hcb he5 hf7 h3f) (RS 100 D) R0 R0 (RS 101 B)) (DPNode (MkDag 27 (bs6
    h3c hf3 hcb he5 hf7 h3f) R0 R0 R0 (RS 165 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hcf hfc hbf h3f)
    R0 R0 R0 (RS 229 B)) DPEmpty DPEmpty))) (DPNode (MkDag 20 (bs6 hf2 hf7 h3f he7 h9f hfe) R0 (RS 53 B) R0 R0)
    (DPNode (MkDag 24 (bs6 hbc hf3 hcf he7 h9f hf3) R0 (RS 85 C) R0 R0) (DPNode (MkDag 7 (bs6 he5 hf2 hf9 he7 h9f
    h3f) (RS 148 D) R0 R0 (RS 149 B)) DPEmpty DPEmpty) (DPNode (MkDag 28 (bs6 he7 hf3 hcb he7 h97 hb9) R0 R0 R0 (RS
    213 B)) DPEmpty DPEmpty)) (DPNode (MkDag 28 (bs6 hbf hf3 hcb he7 h97 hb9) R0 R0 (RS 117 E) R0) (DPNode (MkDag
    26 (bs6 h3c hf3 hcb he7 hf7 h3c) R0 R0 R0 (RS 181 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h5f h73 hcf hcf
    hff h3f) (RS 245 B) R0 R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 8 (bs6 h3f hb9 hfe h79 hff hee) R0 R0 R0 (RS
    29 B)) (DPNode (MkDag 15 (bs6 h79 hff hb9 h7c hff h2f) R0 R0 R0 (RS 45 B)) (DPNode (MkDag 1 (bs6 hcb hff hcf
    hcf hff h3f) R0 R0 R0 (RS 5 D)) (DPNode (MkDag 3 (bs6 h7f h73 hcb he7 h9f hcf) (RS 141 D) R0 R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf3 hcf hfc hbf h3f) R0 R0 R0 (RS 205 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2
    (bs6 hbf h73 hcf h3c hbf h3f) R0 R0 (RS 2 E) R0) (DPNode (MkDag 2 (bs6 h3c hf3 hcf h3c hbf h3f) R0 R0 R0 (RS
    173 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hfc hf3 hcf h2f hff h3f) R0 R0 R0 (RS 237 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs6 hcf h9f h3c hf2 hf7 h3f) R0 R0 R0 (RS 61 A)) (DPNode (MkDag 2 (bs6 hfc hf3 hcb hfc hbf
    h3f) (RS 92 D) (RS 93 B) R0 (RS 93 B)) (DPNode (MkDag 0 (bs6 h3c hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 157 C))
    DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h7c hf3 hf9 he7 h9f hcf) R0 R0 R0 (RS 221 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 1 (bs6 hf3 hf3 hcf hcf hff h3f) R0 R0 (RS 125 E) (RS 126 B)) (DPNode (MkDag 26 (bs6 hbf hf3 hcf he5 hf7
    h3c) R0 R0 (RS 189 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 26 (bs6 hcb hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 243 B))
    DPEmpty DPEmpty)))).

Definition dagSub_10_34 : DagPTree :=
  DPNode (MkDag 6 (bs6 he5 hf3 hcf he7 h9f h3f) (RS 10 D) R0 R0 (RS 98 B)) (DPNode (MkDag 4 (bs6 he5 hf3 hf9 h7d
    hff h3f) (RS 18 D) R0 R0 (RS 100 B)) (DPNode (MkDag 11 (bs6 hb9 h7b h9e h7f h97 hcf) R0 (RS 35 C) R0 R0)
    (DPNode (MkDag 1 (bs6 h7f h3e h79 h7d hff h3f) (RS 67 B) R0 R0 R0) (DPNode (MkDag 27 (bs6 hdf hf3 hcb he5 hf7
    h3f) R0 R0 R0 (RS 131 A)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hbf hf3 hf9 he7 h9f h3f) R0 (RS 195 C) (RS 196
    E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 he5 hf3 hcf hcf hff h3f) (RS 98 D) R0 R0 (RS 99 B)) (DPNode
    (MkDag 3 (bs6 h3c hf3 hf9 he7 h9f hcf) R0 R0 R0 (RS 163 C)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hfc hbe h79
    he7 h9f h3f) R0 R0 R0 (RS 227 B)) DPEmpty DPEmpty))) (DPNode (MkDag 19 (bs6 hf2 hf9 hee h5f h3f h9f) R0 (RS 51
    C) R0 R0) (DPNode (MkDag 6 (bs6 h7f h3e h79 he7 h9f h3f) (RS 83 D) R0 R0 R0) (DPNode (MkDag 2 (bs6 he5 hf3 hcf
    h3c hbf h3f) (RS 146 D) R0 R0 (RS 147 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 he7 hf3 hcb hfc hbf h3f) R0 R0
    R0 (RS 211 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 haf h73 hcf h2f hff h3f) R0 R0 (RS 8 E) R0) (DPNode
    (MkDag 1 (bs6 h3c hf3 hcf h2f hff h3f) R0 R0 R0 (RS 179 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hf3 hf3 hcf
    he7 h97 hcf) (RS 242 D) R0 R0 (RS 243 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 8 (bs6 h2f hb9 hfe h79 hff hee) R0
    R0 R0 (RS 27 C)) (DPNode (MkDag 14 (bs6 hfe h5f hfc hfb h9f hf3) R0 R0 (RS 43 E) (RS 44 B)) (DPNode (MkDag 27
    (bs6 hf9 h7d hcf he7 hf7 h3f) R0 R0 (RS 75 E) (RS 76 D)) (DPNode (MkDag 7 (bs6 h79 hf3 hcb he7 h9f h3f) (RS 139
    B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h2f h73 hcb he7 h9f hcf) R0 R0 R0 (RS 203 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 haf h73 hcf h3c hbf h3f) R0 R0 (RS 107 E) R0) (DPNode (MkDag 0 (bs6 h3c hf3 hcf
    hfc hbf h3f) R0 R0 R0 (RS 171 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hfc hf2 hf9 h7d hff h3f) R0 R0 R0 (RS
    235 B)) DPEmpty DPEmpty))) (DPNode (MkDag 23 (bs6 hfc hbd hcf h3f h9e h5e) (RS 58 D) R0 R0 (RS 59 B)) (DPNode
    (MkDag 3 (bs6 hfc hf2 hf9 he7 h9f hcf) R0 (RS 91 B) R0 R0) (DPNode (MkDag 26 (bs6 he5 hf3 hcb he7 hf7 h3c) (RS
    154 D) R0 R0 (RS 155 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7c hf3 hcf hcf hff h3f) R0 R0 R0 (RS 219 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 hb9 hf3 hcf he7 h9f h3f) R0 (RS 123 C) R0 R0) (DPNode (MkDag 5 (bs6 hbf
    h73 hcf he7 h97 hcf) R0 R0 (RS 187 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hdf hf3 hcb he7 h9f hcf) R0 R0
    R0 (RS 251 A)) DPEmpty DPEmpty)))).

Definition dagSub_10_35 : DagPTree :=
  DPNode (MkDag 6 (bs6 h2f h9e h79 he7 h9f h3f) R0 R0 R0 (RS 182 C)) (DPNode (MkDag 4 (bs6 he5 hf3 hcb hcf hff h3f)
    (RS 22 D) R0 R0 (RS 102 C)) (DPNode (MkDag 12 (bs6 h79 hff h9f hcf h97 hb9) R0 R0 R0 (RS 37 B)) (DPNode (MkDag
    24 (bs6 he5 he7 hcf he7 h9f hf3) R0 R0 R0 (RS 71 A)) (DPNode (MkDag 2 (bs6 hdc hf3 hcb hfc hbf h3f) R0 R0 R0
    (RS 135 A)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h2f h73 hf9 h7d hff h3f) R0 R0 R0 (RS 199 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 hbd hf3 hcf hfc hbf h3f) R0 R0 (RS 0 E) R0) (DPNode (MkDag 3 (bs6 h3c hf3 hcb
    he7 h9f hcf) R0 R0 R0 (RS 167 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hfc hf3 hcf h3c hbf h3f) R0 R0 R0 (RS
    231 B)) DPEmpty DPEmpty))) (DPNode (MkDag 21 (bs6 hff h3c hff he7 hf7 h2f) (RS 54 D) R0 R0 (RS 55 B)) (DPNode
    (MkDag 27 (bs6 h7c hf3 hcf he7 hf7 h3f) (RS 87 D) R0 R0 (RS 88 B)) (DPNode (MkDag 4 (bs6 he5 hf2 hf9 h7d hff
    h3f) (RS 150 D) R0 R0 (RS 151 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf3 hcf h7c hbf h3f) R0 R0 R0 (RS
    215 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hef hf3 hcf h7c hbf h3f) (RS 118 D) R0 R0 (RS 12 B)) (DPNode
    (MkDag 6 (bs6 hbf h9e h79 he7 h9f h3f) R0 R0 (RS 183 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hdf hf3 hf9
    he7 h9f h3f) R0 R0 R0 (RS 194 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 h7f hf3 he7 hdf he7 hb9) R0 R0 R0
    (RS 31 B)) (DPNode (MkDag 16 (bs6 h9f h3f hf9 h79 hf7 h2f) R0 (RS 47 A) R0 R0) (DPNode (MkDag 27 (bs6 h7f hf3
    hcb he5 hf7 h3f) R0 R0 R0 (RS 77 B)) (DPNode (MkDag 4 (bs6 hbf hf3 hcb hcf hff h3f) R0 (RS 143 C) (RS 144 E)
    R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 he7 hf3 hcf h3c hbf h3f) R0 R0 R0 (RS 207 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 27 (bs6 h3f hf3 hcf he7 hf7 h3f) R0 R0 R0 (RS 111 C)) (DPNode (MkDag 7 (bs6 h3c hf2 hf9 he7 h9f
    h3f) R0 R0 R0 (RS 175 C)) DPEmpty DPEmpty) (DPNode (MkDag 26 (bs6 hfc hf3 hcb he7 hf7 h3c) R0 R0 R0 (RS 239 B))
    DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs6 hf9 hf7 h3c hbe h7f hcb) R0 (RS 63 A) R0 R0) (DPNode (MkDag 0 (bs6
    h65 hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 96 B)) (DPNode (MkDag 26 (bs6 h3c hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 159
    C)) DPEmpty DPEmpty) (DPNode (MkDag 27 (bs6 h7c hf3 hcb he5 hf7 h3f) R0 R0 R0 (RS 223 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 3 (bs6 h79 hf3 hf9 he7 h9f hcf) (RS 127 B) R0 R0 (RS 128 B)) (DPNode (MkDag 1 (bs6 haf h73 hcf
    hcf hff h3f) R0 R0 (RS 191 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_10_36 : DagPTree :=
  DPNode (MkDag 5 (bs6 he5 hf3 hcf he7 h97 hcf) (RS 9 D) R0 R0 (RS 97 B)) (DPNode (MkDag 3 (bs6 h7c hf3 hcb he7 h9f
    hcf) R0 R0 R0 (RS 224 B)) (DPNode (MkDag 10 (bs6 hf9 h7c hfb h9f he7 he5) (RS 33 D) R0 R0 (RS 34 A)) (DPNode
    (MkDag 3 (bs6 h9f hbf hcf hcf h3f hcf) R0 R0 R0 (RS 66 B)) (DPNode (MkDag 4 (bs6 h7f h73 hf9 h7d hff h3f) (RS
    130 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h3f h73 hcf hcf hff h3f) R0 R0 R0 (RS 194 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 26 (bs6 he5 hf3 hcf he5 hf7 h3c) (RS 97 D) R0 R0 (RS 10 B)) (DPNode (MkDag 3 (bs6 hbc
    hf3 hf9 he7 h9f hcf) R0 R0 (RS 162 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h7c hbe h79 he7 h9f h3f) R0 R0
    R0 (RS 226 B)) DPEmpty DPEmpty))) (DPNode (MkDag 18 (bs6 hf3 hcf h7e h79 hee h7f) R0 (RS 50 C) R0 R0) (DPNode
    (MkDag 6 (bs6 h5f h3e h79 he7 h9f h3f) (RS 82 B) R0 R0 R0) (DPNode (MkDag 24 (bs6 he5 hf3 hcf he7 h9f hf3) (RS
    145 D) R0 R0 (RS 146 B)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 he7 hf2 hf9 h7d hff h3f) R0 R0 R0 (RS 210 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 hbf hf2 hf9 h7d hff h3f) R0 R0 (RS 4 E) R0) (DPNode (MkDag 1 (bs6 hbc
    hf3 hcf h2f hff h3f) R0 R0 (RS 178 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h9f h73 hcf he7 h97 hcf) R0
    (RS 242 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 8 (bs6 haf hb9 hfe h79 hff hee) R0 R0 (RS 26 E) R0)
    (DPNode (MkDag 14 (bs6 hbe h5f hfc hfb h9f hf3) R0 R0 R0 (RS 42 C)) (DPNode (MkDag 27 (bs6 hb9 h7d hcf he7 hf7
    h3f) R0 R0 R0 (RS 74 C)) (DPNode (MkDag 4 (bs6 hf3 hf3 hf9 h7d hff h3f) (RS 137 D) R0 R0 (RS 138 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs6 haf h73 hcb he7 h9f hcf) R0 R0 (RS 202 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 hbf hf3 hcf hfc hbf h3f) R0 R0 (RS 19 E) R0) (DPNode (MkDag 0 (bs6 hbc hf3 hcf hfc hbf h3f) R0 R0 (RS 170
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h7c hf2 hf9 h7d hff h3f) R0 R0 R0 (RS 234 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 23 (bs6 hbc hbd hcf h3f h9e h5e) R0 (RS 58 C) R0 R0) (DPNode (MkDag 3 (bs6 hbc hf2 hf9 he7 h9f
    hcf) R0 (RS 90 C) R0 R0) (DPNode (MkDag 28 (bs6 he5 hf3 hcb he7 h97 hb9) (RS 153 D) R0 R0 (RS 154 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 26 (bs6 hfc hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 218 B)) DPEmpty DPEmpty)) (DPNode (MkDag
    26 (bs6 hcf hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 122 A)) (DPNode (MkDag 5 (bs6 h2f h73 hcf he7 h97 hcf) R0 R0 R0
    (RS 186 C)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h5f h73 hcb he7 h9f h3f) (RS 20 B) R0 R0 R0) DPEmpty
    DPEmpty)))).

Definition dagSub_10_37 : DagPTree :=
  DPNode (MkDag 1 (bs6 h9f h73 hcf hcf hff h3f) R0 R0 R0 (RS 124 C)) (DPNode (MkDag 3 (bs6 hff hf3 hcb he7 h9f hcf)
    R0 (RS 85 C) R0 R0) (DPNode (MkDag 12 (bs6 hf9 hff h9f hcf h97 hb9) R0 R0 (RS 38 E) (RS 39 A)) (DPNode (MkDag
    24 (bs6 h65 he7 hcf he7 h9f hf3) R0 R0 R0 (RS 70 B)) (DPNode (MkDag 3 (bs6 h7c hf2 hf9 he7 h9f hcf) (RS 134 D)
    R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 haf h73 hf9 h7d hff h3f) R0 R0 (RS 198 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 7 (bs6 he5 hf3 hcb he7 h9f h3f) (RS 101 D) R0 R0 (RS 7 B)) (DPNode (MkDag 3 (bs6 hbc
    hf3 hcb he7 h9f hcf) R0 R0 (RS 166 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7c hf3 hcf h3c hbf h3f) R0 R0
    R0 (RS 230 B)) DPEmpty DPEmpty))) (DPNode (MkDag 21 (bs6 h7f h3c hff he7 hf7 h2f) R0 R0 R0 (RS 54 B)) (DPNode
    (MkDag 24 (bs6 hfc hf3 hcf he7 h9f hf3) (RS 85 D) (RS 86 B) R0 (RS 86 B)) (DPNode (MkDag 3 (bs6 he5 hf2 hf9 he7
    h9f hcf) (RS 149 D) R0 R0 (RS 150 B)) DPEmpty DPEmpty) (DPNode (MkDag 26 (bs6 he7 hf3 hcb he7 hf7 h3c) R0 R0 R0
    (RS 214 B)) DPEmpty DPEmpty)) (DPNode (MkDag 28 (bs6 h3f hf3 hcb he7 h97 hb9) R0 R0 R0 (RS 118 B)) (DPNode
    (MkDag 6 (bs6 haf h9e h79 he7 h9f h3f) R0 R0 (RS 14 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f h73 hcf
    hcf hff h3f) (RS 246 D) R0 R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 hef hf3 he7 hdf he7 hb9) R0 R0 R0
    (RS 30 B)) (DPNode (MkDag 15 (bs6 hf9 hff hb9 h7c hff h2f) R0 R0 R0 (RS 46 A)) (DPNode (MkDag 27 (bs6 hff hf3
    hcb he5 hf7 h3f) (RS 77 D) R0 (RS 78 E) (RS 79 D)) (DPNode (MkDag 4 (bs6 hdf hf3 hcb hcf hff h3f) R0 R0 R0 (RS
    142 A)) DPEmpty DPEmpty) (DPNode (MkDag 24 (bs6 he7 hf3 hcf he7 h9f hf3) R0 R0 R0 (RS 206 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 27 (bs6 hbf hf3 hcf he7 hf7 h3f) R0 R0 (RS 110 E) R0) (DPNode (MkDag 7 (bs6 hbc hf2 hf9 he7 h9f
    h3f) R0 R0 (RS 174 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 26 (bs6 h7c hf3 hcb he7 hf7 h3c) R0 R0 R0 (RS 238 B))
    DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs6 hb9 hf7 h3c hbe h7f hcb) R0 (RS 62 C) R0 R0) (DPNode (MkDag 28 (bs6
    h7c hf3 hcb he7 h97 hb9) (RS 94 E) R0 R0 (RS 95 B)) (DPNode (MkDag 26 (bs6 hbc hf3 hcf he5 hf7 h3c) R0 R0 (RS
    158 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hfc hf3 hf9 he7 h9f hcf) R0 R0 R0 (RS 222 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 1 (bs6 h73 hf3 hcf hcf hff h3f) R0 R0 R0 (RS 124 B)) (DPNode (MkDag 26 (bs6 h3f hf3
    hcf he5 hf7 h3c) R0 R0 R0 (RS 190 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_10_38 : DagPTree :=
  DPNode (MkDag 3 (bs6 h3f h72 hf9 he7 h9f hcf) R0 R0 R0 (RS 113 C)) (DPNode (MkDag 0 (bs6 h3f hf3 hcf hfc hbf h3f)
    R0 R0 R0 (RS 106 C)) (DPNode (MkDag 11 (bs6 hf9 h7b h9e h7f h97 hcf) R0 (RS 36 A) R0 R0) (DPNode (MkDag 0 (bs6
    h5e h7d hcf hfc hbf h3f) (RS 68 B) R0 R0 R0) (DPNode (MkDag 27 (bs6 hbf hf3 hcb he5 hf7 h3f) R0 (RS 77 C) (RS
    132 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hff hf3 hf9 he7 h9f h3f) (RS 195 D) R0 R0 (RS 247 D)) DPEmpty
    DPEmpty)) (DPNode (MkDag 7 (bs6 he5 hf3 hf9 he7 h9f h3f) (RS 99 D) R0 R0 (RS 6 B)) (DPNode (MkDag 27 (bs6 hbc
    hf3 hcb he5 hf7 h3f) R0 R0 (RS 164 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf3 hcf hfc hbf h3f) R0 R0
    R0 (RS 228 B)) DPEmpty DPEmpty))) (DPNode (MkDag 19 (bs6 hf2 hf9 hfe h5f h3f h9f) R0 (RS 52 C) R0 R0) (DPNode
    (MkDag 24 (bs6 hdc hf3 hcf he7 h9f hf3) R0 R0 R0 (RS 84 A)) (DPNode (MkDag 27 (bs6 he5 hf3 hcf he7 hf7 h3f) (RS
    147 D) R0 R0 (RS 148 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 he7 hf3 hcf h2f hff h3f) R0 R0 R0 (RS 212 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hbf h73 hcf h2f hff h3f) R0 R0 (RS 1 E) R0) (DPNode (MkDag 26 (bs6 hbc
    hf3 hcb he7 hf7 h3c) R0 R0 (RS 180 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h79 hf3 hcf he7 h9f h3f) (RS
    244 B) R0 R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 8 (bs6 hbf hb9 hfe h79 hff hee) R0 R0 (RS 28 E) R0) (DPNode
    (MkDag 14 (bs6 h7e h5f hfc hfb h9f hf3) R0 R0 R0 (RS 42 B)) (DPNode (MkDag 27 (bs6 h79 h7d hcf he7 hf7 h3f) R0
    R0 R0 (RS 74 B)) (DPNode (MkDag 3 (bs6 h5f h73 hcb he7 h9f hcf) (RS 140 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 3 (bs6 hbf h73 hcb he7 h9f hcf) R0 R0 (RS 15 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h2f h73 hcf
    h3c hbf h3f) R0 R0 R0 (RS 108 C)) (DPNode (MkDag 2 (bs6 hbc hf3 hcf h3c hbf h3f) R0 R0 (RS 172 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs6 h7c hf3 hcf h2f hff h3f) R0 R0 R0 (RS 236 B)) DPEmpty DPEmpty))) (DPNode (MkDag
    24 (bs6 h7c hff hcf h3f h3f hf3) (RS 60 D) R0 R0 R0) (DPNode (MkDag 2 (bs6 h7c hf3 hcb hfc hbf h3f) R0 R0 R0
    (RS 92 B)) (DPNode (MkDag 0 (bs6 hbc hf3 hcf h7c hbf h3f) R0 R0 (RS 156 E) R0) DPEmpty DPEmpty) (DPNode (MkDag
    1 (bs6 hfc hf3 hcf hcf hff h3f) R0 R0 R0 (RS 220 B)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 hf9 hf3 hcf he7
    h9f h3f) R0 (RS 13 A) R0 R0) (DPNode (MkDag 5 (bs6 h3f h73 hcf he7 h97 hcf) R0 R0 R0 (RS 188 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs6 hbf hf3 hcb he7 h9f hcf) R0 (RS 21 C) R0 R0) DPEmpty DPEmpty)))).

Definition dagSub_10_39 : DagPTree :=
  DPNode (MkDag 3 (bs6 h3f h73 hcb he7 h9f hcf) R0 R0 R0 (RS 142 C)) (DPNode (MkDag 8 (bs6 hbc hf9 hee h79 hff hee)
    R0 R0 (RS 24 E) R0) (DPNode (MkDag 13 (bs6 hb9 hf9 hf3 hdc hf3 hff) R0 (RS 40 C) R0 R0) (DPNode (MkDag 26 (bs6
    hbf hcf hcf he5 hf7 h3c) R0 (RS 72 C) R0 R0) (DPNode (MkDag 2 (bs6 hbc hf3 hcb hfc hbf h3f) R0 (RS 92 C) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hbf h73 hf9 h7d hff h3f) R0 R0 (RS 200 E) R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 haf hf3 hcf hfc hbf h3f) R0 R0 (RS 104 E) R0) (DPNode (MkDag 6 (bs6 hbc hbe h79 he7 h9f h3f) R0
    R0 (RS 168 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h7c hf2 hf9 he7 h9f h3f) R0 R0 R0 (RS 232 B)) DPEmpty
    DPEmpty))) (DPNode (MkDag 22 (bs6 h7c hbf hcf h2f h9f hcf) (RS 56 D) R0 R0 R0) (DPNode (MkDag 3 (bs6 hdc hf2
    hf9 he7 h9f hcf) R0 R0 R0 (RS 89 A)) (DPNode (MkDag 2 (bs6 he5 hf3 hcb hfc hbf h3f) (RS 151 D) R0 R0 (RS 152
    B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 216 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 26 (bs6 hcf h73 hcf he5 hf7 h3c) R0 R0 R0 (RS 121 D)) (DPNode (MkDag 6 (bs6 h3f h9e h79 he7 h9f
    h3f) R0 R0 R0 (RS 184 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hcb hf3 hf9 h7d hff h3f) R0 R0 R0 (RS 248 B))
    DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 hff hf3 he7 hdf he7 hb9) R0 R0 R0 (RS 32 A)) (DPNode (MkDag 17 (bs6
    h97 h9f h2f h9f hbe h5f) R0 R0 R0 (RS 48 A)) (DPNode (MkDag 3 (bs6 hcb hf3 hcb he7 h9f hcf) R0 R0 R0 (RS 80 B))
    (DPNode (MkDag 4 (bs6 hff hf3 hcb hcf hff h3f) (RS 143 D) R0 R0 (RS 145 B)) DPEmpty DPEmpty) (DPNode (MkDag 27
    (bs6 he7 hf3 hcf he7 hf7 h3f) R0 R0 R0 (RS 208 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 haf h72 hf9 he7 h9f
    hcf) R0 R0 (RS 3 E) R0) (DPNode (MkDag 4 (bs6 hbc hf2 hf9 h7d hff h3f) R0 R0 (RS 176 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs6 h79 hf3 hcf h7c hbf h3f) R0 R0 R0 (RS 240 B)) DPEmpty DPEmpty))) (DPNode (MkDag 25 (bs6
    h9f h3f h3c hbe h7f hcb) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 28 (bs6 hfc hf3 hcb he7 h97 hb9) (RS 95 D) R0 R0
    (RS 96 B)) (DPNode (MkDag 1 (bs6 hbc hf3 hcf hcf hff h3f) R0 R0 (RS 160 E) R0) DPEmpty DPEmpty) (DPNode (MkDag
    27 (bs6 hfc hf3 hcb he5 hf7 h3f) R0 R0 R0 (RS 17 B)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h5f h73 hf9 h7d
    hff h3f) (RS 129 B) R0 R0 R0) (DPNode (MkDag 1 (bs6 h2f h73 hcf hcf hff h3f) R0 R0 R0 (RS 192 C)) DPEmpty
    DPEmpty) DPEmpty))).

Definition dagTree_10 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h3d hf3 hcf hfc hbf h3f) R0 R0 R0 (RS 103 C)) (DPNode (MkDag 1 (bs6 h3f h73 hcf h2f hff
    h3f) R0 R0 R0 (RS 116 C)) (DPNode (MkDag 2 (bs6 h3f h73 hcf h3c hbf h3f) R0 R0 R0 (RS 109 C)) (DPNode (MkDag 4
    (bs6 h3f hf2 hf9 h7d hff h3f) R0 R0 R0 (RS 114 C)) dagSub_10_32 dagSub_10_33) (DPNode (MkDag 3 (bs6 he5 hf3 hf9
    he7 h9f hcf) (RS 6 D) R0 R0 (RS 18 B)) dagSub_10_34 dagSub_10_35)) (DPNode (MkDag 3 (bs6 h2f h72 hf9 he7 h9f
    hcf) R0 R0 R0 (RS 112 C)) (DPNode (MkDag 3 (bs6 hcb he5 hf9 he7 h9f hcf) R0 R0 R0 (RS 77 C)) dagSub_10_36
    dagSub_10_37) (DPNode (MkDag 3 (bs6 he5 hf3 hcb he7 h9f hcf) (RS 7 D) R0 R0 (RS 22 B)) dagSub_10_38
    dagSub_10_39))).

Definition dagSub_11_40 : DagPTree :=
  DPNode (MkDag 3 (bs6 hcf h3c hf9 h7c hbe h7f) R0 R0 R0 (RS 209 D)) (DPNode (MkDag 8 (bs6 hdf hf3 hf9 he7 h9f hcf)
    R0 R0 R0 (RS 17 A)) (DPNode (MkDag 13 (bs6 hb9 hf9 hff h9f hf9 hff) R0 (RS 33 C) R0 R0) (DPNode (MkDag 19 (bs6
    hf9 he7 hb9 h7c hbe h7f) (RS 64 D) R0 R0 (RS 65 A)) (DPNode (MkDag 0 (bs6 hbf h97 h9e h7f hee h7f) R0 R0 (RS
    129 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 hff h97 hb9 h7c hbe h7f) (RS 192 D) R0 R0 (RS 193 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 h9f h3c hf9 h7c hbe h7f) R0 (RS 97 C) R0 R0) (DPNode (MkDag 3 (bs6 h9e
    he7 h9f hb9 hfe h7f) R0 R0 R0 (RS 161 A)) DPEmpty DPEmpty) (DPNode (MkDag 21 (bs6 hf7 h2f h3f h97 h9f h3c) R0
    (RS 225 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs6 hf9 he7 hcf he7 hee h7f) (RS 48 D) R0 R0 (RS 49 A))
    (DPNode (MkDag 4 (bs6 hf9 hff hf9 h7c hbe h7f) R0 R0 (RS 81 E) (RS 82 A)) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he5
    hee h7f) R0 R0 (RS 145 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7e h7f hf9 h7c hbe h7f) (RS 8 D) R0 R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs6 hbf h97 hb9 h7c hbe h7f) R0 R0 (RS 113 E) R0) (DPNode (MkDag 0
    (bs6 h9f h97 hb9 he5 hee h7f) R0 (RS 177 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbf h2f h9f hff h3e
    h7f) R0 (RS 241 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 h3f hcf he7 h9f h3f h9e) R0 R0 R0 (RS 25
    B)) (DPNode (MkDag 1 (bs6 hff hf9 he5 hf3 hf3 hff) (RS 40 D) R0 R0 (RS 41 B)) (DPNode (MkDag 3 (bs6 h7b hfe h79
    he7 hee h7f) (RS 73 B) R0 R0 R0) (DPNode (MkDag 2 (bs6 hfb he5 hf9 h7c hbe h7f) R0 (RS 137 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 h7f hff hb9 he5 hee h7f) (RS 201 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    18 (bs6 hbf h2f h3e hff h7e h79) R0 R0 (RS 105 E) R0) (DPNode (MkDag 3 (bs6 hf9 hef hf9 h7c hbe h7f) (RS 168 D)
    R0 R0 (RS 169 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbf h2f hfd hcf hee h7f) R0 (RS 10 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 2 (bs6 hff h3c hbe hff h3e h7f) (RS 56 D) R0 R0 (RS 57 A)) (DPNode (MkDag 1 (bs6 h79
    he7 h9f hf3 hee h7f) R0 R0 R0 (RS 87 B)) (DPNode (MkDag 3 (bs6 hf9 h7f hf9 h7c hbe h7f) R0 (RS 153 A) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 h73 hcf hf9 h7c hf9 hee) R0 R0 R0 (RS 215 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 4 (bs6 hbf h9f hb9 h7c hbe h7f) R0 R0 (RS 121 E) R0) (DPNode (MkDag 1 (bs6 hcf h3f hb9 h7c hbe h7f) R0
    R0 R0 (RS 185 D)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hbf hdc hfe h79 h79 hee) R0 (RS 249 C) R0 R0) DPEmpty
    DPEmpty)))).

Definition dagSub_11_41 : DagPTree :=
  DPNode (MkDag 5 (bs6 hcb hf2 hf3 hee h7f h7f) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 9 (bs6 h3d hcf he7 h9f h3f h9e)
    R0 R0 R0 (RS 21 C)) (DPNode (MkDag 16 (bs6 he5 hf3 hff h3c hfe h79) (RS 36 D) R0 R0 (RS 37 B)) (DPNode (MkDag 3
    (bs6 hf9 h79 hf9 h7c hbe h7f) (RS 68 D) R0 R0 (RS 69 D)) (DPNode (MkDag 2 (bs6 hcf h3c hbd hcf hee h7f) R0 R0
    R0 (RS 133 D)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbb h97 h9e h7f hee h7f) R0 (RS 197 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 h3f h2f h9e hff h3e h7f) R0 R0 R0 (RS 240 A)) (DPNode (MkDag 3 (bs6 hcf h9f hf9
    he7 hee h7f) R0 R0 R0 (RS 165 D)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hf9 he7 hff hff h3e h7f) R0 R0 (RS 229
    E) (RS 230 C)) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs6 hf7 h3c hbf hfc hbe h7f) (RS 52 D) R0 R0 (RS 53 C))
    (DPNode (MkDag 1 (bs6 hb9 he7 hf3 hff h3e h7f) R0 (RS 85 C) R0 R0) (DPNode (MkDag 22 (bs6 hf2 hf9 hf9 h7c hbe
    h79) R0 (RS 149 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f hfc hff hff h3e h7f) (RS 213 C) R0 R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbf h9f hf9 h7c hbe h7f) R0 R0 (RS 117 E) R0) (DPNode (MkDag 20 (bs6
    h72 hfc hfe h79 h79 hee) R0 R0 R0 (RS 179 B)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hbe h7e h79 h79 hf9 hfe)
    R0 (RS 245 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 11 (bs6 h79 he7 hcf hdc hbe h5f) R0 R0 R0 (RS 29 B))
    (DPNode (MkDag 3 (bs6 hcf h3f hcf hdc hbe h7f) (RS 44 D) R0 R0 (RS 45 D)) (DPNode (MkDag 20 (bs6 h7e h5f h3e
    h79 h79 hee) R0 R0 R0 (RS 75 B)) (DPNode (MkDag 4 (bs6 hbf h2f hb9 h7c hbe h7f) R0 R0 (RS 141 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 20 (bs6 h7f h3c hfe h79 h79 hee) (RS 205 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    1 (bs6 h3f h3f h9f hf3 hee h7f) R0 R0 R0 (RS 244 A)) (DPNode (MkDag 0 (bs6 hcf he7 h9e h7f hee h7f) R0 R0 R0
    (RS 173 D)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hb9 hfc hf9 h7c hbe h7f) R0 (RS 237 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 3 (bs6 hf3 he7 h97 hb9 hfe h7f) R0 (RS 61 C) R0 R0) (DPNode (MkDag 2 (bs6 hf9 h7f hf9
    h7c hbe h7f) R0 R0 (RS 93 E) (RS 94 A)) (DPNode (MkDag 2 (bs6 hbf h3f hfe hff h3e h7f) R0 (RS 158 C) (RS 159 E)
    R0) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 hbc hbc hf9 h7c hbe h7f) R0 R0 (RS 221 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs6 hbf h97 hfe hff h3e h7f) R0 R0 (RS 125 E) R0) (DPNode (MkDag 3 (bs6 hfc hbe h79 he7 hee
    h7f) R0 R0 (RS 189 E) (RS 190 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbf h2f hb9 h7c hbe h7f) R0 R0 (RS 11
    E) R0) DPEmpty DPEmpty)))).

Definition dagSub_11_42 : DagPTree :=
  DPNode (MkDag 2 (bs6 hff h2f hfd hcf hee h7f) (RS 10 D) R0 R0 (RS 233 A)) (DPNode (MkDag 8 (bs6 hff hf3 hf9 he7
    h9f hcf) (RS 18 D) R0 R0 (RS 19 C)) (DPNode (MkDag 14 (bs6 he5 hf3 hf7 h3c hfe h5f) R0 R0 R0 (RS 35 B)) (DPNode
    (MkDag 2 (bs6 hf9 h7c hf9 h7c hbe h7f) (RS 66 D) R0 R0 (RS 67 A)) (DPNode (MkDag 20 (bs6 hb3 hcb hf9 h7c hf9
    hee) R0 (RS 131 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h7f h9f hb9 h7c hbe h7f) (RS 195 D) R0 R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbf h2f h9e hff h3e h7f) R0 (RS 99 C) (RS 100 E) R0) (DPNode (MkDag 3
    (bs6 h9f he7 h9f hb9 hfe h7f) R0 R0 R0 (RS 163 B)) DPEmpty DPEmpty) (DPNode (MkDag 21 (bs6 hff h2f h3f h97 h9f
    h3c) R0 (RS 227 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hf9 hfd hcf hcb hee h7f) (RS 50 D) R0 R0 (RS
    51 A)) (DPNode (MkDag 21 (bs6 hb9 hfc hbf h97 h9f h3c) R0 (RS 83 C) R0 R0) (DPNode (MkDag 0 (bs6 hbc hf2 hfe
    h79 h7e h7f) R0 R0 (RS 6 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7b hfc hff hff h3e h7f) (RS 211 B) R0
    R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 haf h9f hf9 h7c hbe h7f) R0 R0 (RS 115 E) R0) (DPNode (MkDag 3
    (bs6 hff h9f hf9 he7 hee h7f) (RS 178 D) R0 R0 (RS 179 C)) DPEmpty DPEmpty) (DPNode (MkDag 18 (bs6 h9f h2f h3e
    hff h7e h79) R0 (RS 243 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 10 (bs6 h7d hcf hcf hff h3f h3e) R0 R0 R0
    (RS 27 B)) (DPNode (MkDag 1 (bs6 hb9 h79 hfe h79 h7e h7f) R0 (RS 43 C) R0 R0) (DPNode (MkDag 3 (bs6 h7f hfe h79
    he7 hee h7f) (RS 75 C) R0 R0 R0) (DPNode (MkDag 4 (bs6 hf7 h2f hb9 h7c hbe h7f) R0 R0 (RS 139 E) (RS 140 C))
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7f h3c hbd hcf hee h7f) (RS 203 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 1 (bs6 hbf h3f h9f hf3 hee h7f) R0 (RS 107 C) (RS 108 E) R0) (DPNode (MkDag 3 (bs6 hf9 hff hf9 h7c hbe
    h7f) (RS 170 D) R0 R0 (RS 171 D)) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 h79 he7 hf9 h7c hbe h7f) R0 R0 R0 (RS
    235 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 h97 he7 hff hff h3e h7f) R0 R0 R0 (RS 59 A)) (DPNode (MkDag 20
    (bs6 hff hcf h3e h79 h79 hee) R0 (RS 91 A) R0 R0) (DPNode (MkDag 2 (bs6 h9f h3d hfe hff h3e h7f) R0 (RS 4 C) R0
    (RS 4 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hcf hfc hff h9f hfe h7f) R0 R0 R0 (RS 219 D)) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 haf h97 hfe hff h3e h7f) R0 R0 (RS 123 E) R0) (DPNode (MkDag 1 (bs6 hcb he7 hff
    hff h3e h7f) R0 R0 R0 (RS 187 D)) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs6 h9f hf9 hf9 h7c hbe h79) R0 (RS 2 C)
    R0 (RS 2 C)) DPEmpty DPEmpty)))).

Definition dagSub_11_43 : DagPTree :=
  DPNode (MkDag 7 (bs6 h5f h73 hf9 he7 h9f hcb) (RS 15 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 h2f hcf he7 h9f h3f h9e)
    R0 R0 R0 (RS 23 C)) (DPNode (MkDag 18 (bs6 he7 h97 hcb hff h73 hf9) (RS 38 D) R0 R0 (RS 39 A)) (DPNode (MkDag
    18 (bs6 hcf h2f h3e hff h7e h79) R0 R0 R0 (RS 71 D)) (DPNode (MkDag 0 (bs6 hcf hef hf9 h7c hbe h7f) R0 R0 R0
    (RS 135 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f h97 h9e h7f hee h7f) R0 (RS 199 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 18 (bs6 hf7 h2f h3e hff h7e h79) R0 R0 (RS 103 E) (RS 104 C)) (DPNode (MkDag 2 (bs6
    hcf h2f hb9 h7c hbe h7f) R0 R0 R0 (RS 167 A)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hbf hfe h79 h79 hf9 hfe)
    R0 R0 (RS 231 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs6 h3f h3c hbf hfc hbe h7f) R0 R0 R0 (RS 55 A))
    (DPNode (MkDag 1 (bs6 hb9 he7 h9f hf3 hee h7f) R0 R0 R0 (RS 87 C)) (DPNode (MkDag 2 (bs6 hff h2f hb9 h7c hbe
    h7f) (RS 150 D) R0 R0 (RS 151 A)) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 h7e h5f h9f hcf hfe h7f) R0 R0 R0 (RS
    213 B)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 haf h9f hb9 h7c hbe h7f) R0 R0 (RS 119 E) R0) (DPNode (MkDag 2
    (bs6 h79 h79 hf9 h7c hbe h7f) R0 R0 R0 (RS 183 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hb9 h79 hff h9f hfe
    h7f) R0 (RS 111 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 12 (bs6 hb9 hfd hcb hdc hbe h5e) R0 (RS 31 C) R0
    R0) (DPNode (MkDag 0 (bs6 hcf hcf hcf he5 hee h7f) R0 R0 R0 (RS 47 A)) (DPNode (MkDag 4 (bs6 hb9 hef hf9 h7c
    hbe h7f) R0 (RS 79 C) R0 R0) (DPNode (MkDag 0 (bs6 hcf h3f h9e h7f hee h7f) R0 R0 R0 (RS 143 D)) DPEmpty
    DPEmpty) (DPNode (MkDag 22 (bs6 h7f h3f hb9 h7c hbe h79) (RS 207 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    3 (bs6 h79 h79 hff h9f hfe h7f) R0 R0 R0 (RS 111 B)) (DPNode (MkDag 0 (bs6 hbb h97 hb9 he5 hee h7f) R0 (RS 175
    C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hb9 hf9 hf9 h7c hbe h7f) R0 (RS 239 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 20 (bs6 hcf h2f h3e h79 h79 hee) (RS 62 D) R0 R0 (RS 63 A)) (DPNode (MkDag 4 (bs6 hb9
    he5 hf9 h7c hbe h7f) R0 (RS 95 C) R0 R0) (DPNode (MkDag 2 (bs6 hff h3f hfe hff h3e h7f) R0 (RS 160 A) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbf hf9 hf9 h7c hbe h7f) R0 (RS 9 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 haf h97 h9e h7f hee h7f) R0 R0 (RS 127 E) R0) (DPNode (MkDag 3 (bs6 h9f hf9 hff h9f hfe h7f) R0
    (RS 191 B) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_11_44 : DagPTree :=
  DPNode (MkDag 2 (bs6 hff hf9 hf9 h7c hbe h7f) (RS 9 D) R0 R0 (RS 223 A)) (DPNode (MkDag 8 (bs6 hbf hf3 hf9 he7
    h9f hcf) R0 (RS 18 C) R0 R0) (DPNode (MkDag 13 (bs6 hf9 hf9 hff h9f hf9 hff) R0 (RS 34 B) R0 R0) (DPNode (MkDag
    2 (bs6 hb9 h7c hf9 h7c hbe h7f) R0 (RS 66 C) R0 R0) (DPNode (MkDag 0 (bs6 h3f h97 h9e h7f hee h7f) R0 R0 R0 (RS
    130 A)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h7b h9f hb9 h7c hbe h7f) (RS 7 B) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs6 hf7 h2f h9e hff h3e h7f) (RS 97 D) (RS 98 C) R0 (RS 98 C)) (DPNode (MkDag 3 (bs6 h97 he7
    h9f hb9 hfe h7f) R0 (RS 162 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 21 (bs6 hbf h2f h3f h97 h9f h3c) R0 (RS
    226 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hb9 hfd hcf hcb hee h7f) R0 (RS 50 C) R0 R0) (DPNode
    (MkDag 4 (bs6 h79 hff hf9 h7c hbe h7f) R0 R0 R0 (RS 80 B)) (DPNode (MkDag 0 (bs6 h3c hf2 hf9 he5 hee h7f) R0 R0
    R0 (RS 146 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hcb hef hf9 h7c hbe h7f) R0 R0 R0 (RS 210 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 19 (bs6 h3f h97 hb9 h7c hbe h7f) R0 R0 R0 (RS 114 C)) (DPNode (MkDag 3 (bs6 h7f h9f
    hf9 he7 hee h7f) R0 R0 R0 (RS 178 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hff h2f h9f hff h3e h7f) (RS 241
    D) R0 R0 (RS 242 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 he7 hcf he7 hf7 h3f h9f) R0 R0 R0 (RS 26 B))
    (DPNode (MkDag 19 (bs6 he5 hff hcf h3c hbe h7f) (RS 41 D) R0 R0 (RS 42 A)) (DPNode (MkDag 3 (bs6 h5f hfe h79
    he7 hee h7f) (RS 74 B) R0 R0 R0) (DPNode (MkDag 2 (bs6 h9f he5 hf9 h7c hbe h7f) R0 R0 R0 (RS 138 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 h5f h3c hbd hcf hee h7f) (RS 202 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    18 (bs6 h3f h2f h3e hff h7e h79) R0 R0 R0 (RS 106 A)) (DPNode (MkDag 3 (bs6 hb9 hff hf9 h7c hbe h7f) R0 (RS 170
    C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 h9f h2f h3e h79 h79 hee) R0 (RS 234 B) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 1 (bs6 h9e he7 hff hff h3e h7f) R0 (RS 58 A) R0 R0) (DPNode (MkDag 20 (bs6 hbf hcf
    h3e h79 h79 hee) R0 (RS 90 C) R0 R0) (DPNode (MkDag 1 (bs6 hb9 he5 hf9 h7c hbe h7f) R0 (RS 1 C) R0 (RS 1 C))
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hcb hdc hbd hcf hee h7f) R0 R0 R0 (RS 218 D)) DPEmpty DPEmpty)) (DPNode
    (MkDag 4 (bs6 h3f h9f hb9 h7c hbe h7f) R0 R0 R0 (RS 122 C)) (DPNode (MkDag 1 (bs6 hcb he7 hbf hff h3e h7f) R0
    R0 R0 (RS 186 D)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hff hdc hfe h79 h79 hee) (RS 249 D) (RS 250 A) R0 (RS
    250 A)) DPEmpty DPEmpty)))).

Definition dagSub_11_45 : DagPTree :=
  DPNode (MkDag 6 (bs6 h79 hf3 hf9 he7 h9f hcb) (RS 14 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 haf hcf he7 h9f h3f h9e)
    R0 R0 (RS 22 E) R0) (DPNode (MkDag 17 (bs6 he5 hf3 hf7 h3c hfe h79) (RS 37 D) R0 R0 (RS 38 B)) (DPNode (MkDag 2
    (bs6 hcf h2f h9e hff h3e h7f) R0 R0 R0 (RS 70 D)) (DPNode (MkDag 22 (bs6 hcf h3f hb9 h7c hbe h79) R0 R0 R0 (RS
    134 D)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfb h97 h9e h7f hee h7f) (RS 197 D) R0 R0 (RS 198 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 h9f h2f h9f hff h3e h7f) R0 R0 R0 (RS 102 C)) (DPNode (MkDag 20 (bs6 hcf hdc
    hfe h79 h79 hee) R0 R0 R0 (RS 166 D)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h79 he7 hff hff h3e h7f) R0 R0 R0
    (RS 228 B)) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs6 hbf h3c hbf hfc hbe h7f) R0 R0 (RS 54 E) R0) (DPNode
    (MkDag 1 (bs6 hf9 he7 hf3 hff h3e h7f) R0 (RS 86 A) R0 R0) (DPNode (MkDag 2 (bs6 h7f h2f hb9 h7c hbe h7f) R0 R0
    R0 (RS 150 B)) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 hfe h5f h9f hcf hfe h7f) R0 R0 (RS 214 E) (RS 215 C))
    DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h3f h9f hf9 h7c hbe h7f) R0 R0 R0 (RS 118 C)) (DPNode (MkDag 22 (bs6
    h9e h79 hf9 h7c hbe h79) R0 (RS 182 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hfe h7e h79 h79 hf9 hfe)
    (RS 245 D) R0 R0 (RS 246 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 11 (bs6 hf9 he7 hcf hdc hbe h5f) R0 R0 R0 (RS
    30 A)) (DPNode (MkDag 18 (bs6 hcf he7 hcf he5 hfe h79) R0 R0 R0 (RS 46 D)) (DPNode (MkDag 3 (bs6 hcf h2f hb9
    h7c hbe h7f) R0 R0 R0 (RS 78 A)) (DPNode (MkDag 4 (bs6 h3f h2f hb9 h7c hbe h7f) R0 R0 R0 (RS 142 D)) DPEmpty
    DPEmpty) (DPNode (MkDag 22 (bs6 h5f h3f hb9 h7c hbe h79) (RS 206 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    20 (bs6 h9e h7e h79 h79 hf9 hfe) R0 (RS 110 B) R0 R0) (DPNode (MkDag 3 (bs6 hcf he7 h9f hb9 hfe h7f) R0 R0 R0
    (RS 174 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hf9 hfc hf9 h7c hbe h7f) (RS 237 D) R0 R0 (RS 238 A))
    DPEmpty DPEmpty))) (DPNode (MkDag 20 (bs6 hf3 hfe h79 h79 hf9 hfe) R0 (RS 62 D) R0 R0) (DPNode (MkDag 2 (bs6
    h79 h7f hf9 h7c hbe h7f) R0 R0 R0 (RS 92 B)) (DPNode (MkDag 2 (bs6 h77 h3f hfe hff h3e h7f) R0 R0 R0 (RS 4 B))
    DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 h3c hbc hf9 h7c hbe h7f) R0 R0 R0 (RS 222 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs6 h3f h97 hfe hff h3e h7f) R0 R0 R0 (RS 126 C)) (DPNode (MkDag 3 (bs6 h7c hbe h79 he7 hee h7f) R0
    R0 R0 (RS 188 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_11_46 : DagPTree :=
  DPNode (MkDag 2 (bs6 h3f h2f hb9 h7c hbe h7f) R0 R0 R0 (RS 153 A)) (DPNode (MkDag 9 (bs6 hbd hcf he7 h9f h3f h9e)
    R0 R0 (RS 20 E) R0) (DPNode (MkDag 15 (bs6 he5 hf2 hf7 h3c hfe h5f) (RS 35 D) R0 R0 (RS 36 B)) (DPNode (MkDag 3
    (bs6 hb9 h79 hf9 h7c hbe h7f) R0 (RS 68 C) R0 R0) (DPNode (MkDag 20 (bs6 hf3 hcb hf9 h7c hf9 hee) (RS 131 D) R0
    R0 (RS 132 D)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hcf h97 hfe hff h3e h7f) R0 R0 R0 (RS 196 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 hff h2f h9e hff h3e h7f) R0 (RS 101 A) R0 R0) (DPNode (MkDag 0 (bs6 h7f h97 hb9
    he5 hee h7f) (RS 164 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hb9 he7 hff hff h3e h7f) R0 R0 R0 (RS
    228 C)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 h9f h2f h97 hdc hbe h7f) R0 (RS 52 C) R0 R0) (DPNode (MkDag 21
    (bs6 hf9 hfc hbf h97 h9f h3c) (RS 83 D) R0 R0 (RS 84 A)) (DPNode (MkDag 22 (bs6 hb2 hf9 hf9 h7c hbe h79) R0 (RS
    148 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h5f hfc hff hff h3e h7f) (RS 212 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs6 h2f h9f hf9 h7c hbe h7f) R0 R0 R0 (RS 116 C)) (DPNode (MkDag 20 (bs6 hf2 hfc
    hfe h79 h79 hee) R0 R0 (RS 180 E) (RS 181 A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hf7 h3f h9f hf3 hee h7f)
    (RS 243 D) R0 R0 (RS 106 C)) DPEmpty DPEmpty)))) (DPNode (MkDag 10 (bs6 hfd hcf hcf hff h3f h3e) R0 R0 R0 (RS
    28 B)) (DPNode (MkDag 1 (bs6 hf9 h79 hfe h79 h7e h7f) R0 (RS 44 D) R0 R0) (DPNode (MkDag 20 (bs6 hfe h5f h3e
    h79 h79 hee) R0 R0 (RS 76 E) (RS 77 D)) (DPNode (MkDag 4 (bs6 h77 h2f hb9 h7c hbe h7f) R0 R0 R0 (RS 138 B))
    DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 h5f h3c hfe h79 h79 hee) (RS 204 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 1 (bs6 hff h3f h9f hf3 hee h7f) (RS 107 D) R0 R0 (RS 109 A)) (DPNode (MkDag 2 (bs6 hcf h3f hfe hff h3e
    h7f) R0 R0 R0 (RS 172 D)) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 hf9 he7 hf9 h7c hbe h7f) (RS 235 D) R0 R0 (RS
    236 A)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 h9f he7 hff hff h3e h7f) R0 (RS 60 C) R0 R0) (DPNode (MkDag 2
    (bs6 hb9 h7f hf9 h7c hbe h7f) R0 R0 R0 (RS 92 C)) (DPNode (MkDag 1 (bs6 h79 he5 hf9 h7c hbe h7f) R0 R0 R0 (RS 1
    B)) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs6 hcf hcf hb9 h7c hbe h79) R0 R0 R0 (RS 220 C)) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs6 h2f h97 hfe hff h3e h7f) R0 R0 R0 (RS 124 C)) (DPNode (MkDag 3 (bs6 hcb he7 h97 hb9 hfe
    h7f) R0 R0 R0 (RS 188 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h77 h2f hb9 h7c hbe h7f) R0 R0 R0 (RS 2 B))
    DPEmpty DPEmpty)))).

Definition dagSub_11_47 : DagPTree :=
  DPNode (MkDag 7 (bs6 h7f h73 hf9 he7 h9f hcb) (RS 16 D) R0 R0 R0) (DPNode (MkDag 9 (bs6 hbf hcf he7 h9f h3f h9e)
    R0 R0 (RS 24 E) R0) (DPNode (MkDag 1 (bs6 hbf hf9 he5 hf3 hf3 hff) R0 (RS 40 C) R0 R0) (DPNode (MkDag 20 (bs6
    hcb hee h79 h79 hf9 hfe) R0 R0 R0 (RS 72 B)) (DPNode (MkDag 2 (bs6 hbb he5 hf9 h7c hbe h7f) R0 (RS 136 C) R0
    R0) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 hf3 hff h9f hcf hfe h7f) (RS 199 D) R0 R0 (RS 200 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 18 (bs6 h77 h2f h3e hff h7e h79) R0 R0 R0 (RS 102 B)) (DPNode (MkDag 3 (bs6 hb9 hef
    hf9 h7c hbe h7f) R0 (RS 168 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 h3f hfe h79 h79 hf9 hfe) R0 R0 R0
    (RS 232 A)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hbf h3c hbe hff h3e h7f) R0 (RS 56 C) R0 R0) (DPNode
    (MkDag 1 (bs6 hf9 he7 h9f hf3 hee h7f) R0 R0 (RS 88 E) (RS 89 A)) (DPNode (MkDag 3 (bs6 hb9 h7f hf9 h7c hbe
    h7f) R0 (RS 152 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs6 hf3 hcf hf9 h7c hf9 hee) R0 R0 (RS 216 E) (RS
    217 D)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h2f h9f hb9 h7c hbe h7f) R0 R0 R0 (RS 120 C)) (DPNode (MkDag 2
    (bs6 hf9 h79 hf9 h7c hbe h7f) (RS 183 D) R0 R0 (RS 184 D)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hbe he7 h9f
    hb9 hfe h7f) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 12 (bs6 hf9 hfd hcb hdc hbe h5e) (RS 31 D)
    R0 R0 (RS 32 A)) (DPNode (MkDag 3 (bs6 hb9 he7 hcf he7 hee h7f) R0 (RS 48 C) R0 R0) (DPNode (MkDag 4 (bs6 hf9
    hef hf9 h7c hbe h7f) R0 (RS 5 A) R0 R0) (DPNode (MkDag 3 (bs6 hcf h3f h9f hb9 hfe h7f) R0 R0 R0 (RS 144 C))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h5e h7f hf9 h7c hbe h7f) (RS 208 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 3 (bs6 hf9 h79 hff h9f hfe h7f) (RS 111 D) R0 R0 (RS 112 C)) (DPNode (MkDag 0 (bs6 hfb h97 hb9 he5 hee
    h7f) (RS 175 D) R0 R0 (RS 176 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hf9 hf9 hf9 h7c hbe h7f) (RS 239 D) R0
    R0 (RS 96 A)) DPEmpty DPEmpty))) (DPNode (MkDag 19 (bs6 hb9 he7 hb9 h7c hbe h7f) R0 (RS 64 C) R0 R0) (DPNode
    (MkDag 4 (bs6 hf9 he5 hf9 h7c hbe h7f) (RS 95 D) R0 R0 (RS 96 A)) (DPNode (MkDag 2 (bs6 h3f h3f hfe hff h3e
    h7f) R0 R0 R0 (RS 247 A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f h2f hb9 h7c hbe h7f) R0 (RS 224 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h2f h97 h9e h7f hee h7f) R0 R0 R0 (RS 128 C)) (DPNode (MkDag 19 (bs6
    h7f h97 hb9 h7c hbe h7f) R0 R0 R0 (RS 192 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_11 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 he7 h97 hb9 he5 hee h7f) (RS 0 D) R0 R0 (RS 248 A)) (DPNode (MkDag 1 (bs6 hf9 he5 hf9
    h7c hbe h7f) (RS 1 D) (RS 154 A) (RS 155 E) (RS 154 A)) (DPNode (MkDag 2 (bs6 hf7 h2f hb9 h7c hbe h7f) (RS 2 D)
    R0 (RS 251 E) (RS 252 C)) (DPNode (MkDag 2 (bs6 hf7 h3f hfe hff h3e h7f) (RS 4 D) (RS 156 C) (RS 157 E) (RS 156
    C)) dagSub_11_40 dagSub_11_41) (DPNode (MkDag 0 (bs6 h3c hf2 hfe h79 h7e h7f) R0 R0 R0 (RS 147 A)) dagSub_11_42
    dagSub_11_43)) (DPNode (MkDag 3 (bs6 hfe he7 h9f hb9 hfe h7f) (RS 3 D) R0 R0 (RS 0 B)) (DPNode (MkDag 4 (bs6
    hb9 hff hf9 h7c hbe h7f) R0 R0 R0 (RS 80 C)) dagSub_11_44 dagSub_11_45) (DPNode (MkDag 4 (bs6 h5f h9f hb9 h7c
    hbe h7f) (RS 194 B) R0 R0 R0) dagSub_11_46 dagSub_11_47))).

Definition dagTree_12 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h72 hf9 hfe h7e he7 h97) R0 R0 R0 (RS 6 B)) (DPNode (MkDag 0 (bs6 h73 hff hdc hbe he7
    h97) R0 R0 R0 (RS 120 B)) (DPNode (MkDag 1 (bs6 h7c hfe h7b h9f he5 hf3) (RS 111 D) R0 R0 (RS 112 B)) (DPNode
    (MkDag 2 (bs6 hf3 hf3 he7 h9f he5 hf2) R0 R0 (RS 121 E) (RS 7 C)) (DPNode (MkDag 1 (bs6 hdc hbe he7 hf3 he5
    hf3) R0 R0 R0 (RS 74 A)) (DPNode (MkDag 7 (bs6 hbd hcb he7 h9e h7c hbe) R0 R0 (RS 17 E) R0) (DPNode (MkDag 0
    (bs6 hb9 hf9 h7e h7e he7 h97) R0 (RS 33 C) R0 R0) (DPNode (MkDag 0 (bs6 h3c hbd hcf he7 he7 h97) R0 R0 R0 (RS
    65 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h3c hf9 hfc hff hff h2f) R0 R0 R0 (RS 97 C)) DPEmpty DPEmpty))
    (DPNode (MkDag 4 (bs6 h9e h5f h3f hbf he5 hf3) R0 (RS 49 A) R0 R0) (DPNode (MkDag 2 (bs6 h9f hcf h3f h97 he5
    hf2) R0 (RS 81 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hfc hfe h7b h9f he5 hf3) R0 R0 R0 (RS 5 B))
    DPEmpty DPEmpty))) (DPNode (MkDag 9 (bs6 hfd hcb he5 he7 hb9 h7d) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 11 (bs6
    h9f h3f hf3 hf2 hff hff) R0 (RS 41 A) R0 R0) (DPNode (MkDag 0 (bs6 hef hff hdc hbe he7 h97) (RS 72 D) R0 R0 (RS
    73 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h3f h3f h9e h7e he5 hf2) R0 R0 R0 (RS 105 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs6 he7 hff he7 h9f he5 hf2) R0 R0 R0 (RS 57 C)) (DPNode (MkDag 11 (bs6 h2f hb9 h7c hbc hff
    hff) R0 R0 R0 (RS 89 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf3 hff hdc hbe he7 h97) (RS 120 D) R0 (RS 1 E)
    (RS 4 C)) DPEmpty DPEmpty)))) (DPNode (MkDag 1 (bs6 hfc hfe h7f h9f he5 hf3) R0 (RS 114 B) R0 (RS 114 B))
    (DPNode (MkDag 7 (bs6 hbf hcb he7 h9e h7c hbe) R0 R0 (RS 21 E) R0) (DPNode (MkDag 1 (bs6 hbc hf9 h7c hfe he5
    hf3) R0 (RS 37 C) R0 R0) (DPNode (MkDag 2 (bs6 hfe h79 hfc hf3 he5 hf2) R0 R0 (RS 69 E) (RS 70 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs6 h3f hb9 hfb h9f he5 hf3) R0 R0 R0 (RS 101 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 hf3 hfc hbc hf9 he7 h97) (RS 52 D) R0 (RS 53 E) (RS 54 C)) (DPNode (MkDag 0 (bs6 he5 hf9 h7c hf9 he7 h97)
    (RS 84 D) R0 R0 (RS 85 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9e hf9 he7 hff he7 h97) R0 (RS 10 A) R0 R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs6 hf9 h7c hfb h9f hcf he7) R0 (RS 29 A) R0 R0) (DPNode (MkDag 3 (bs6 h97
    hb9 hfc hf7 hff h2f) R0 (RS 45 A) R0 R0) (DPNode (MkDag 4 (bs6 he5 hff he7 he7 he5 hf3) R0 R0 R0 (RS 77 B))
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hff hff he7 h9f he5 hf2) R0 R0 (RS 109 E) (RS 7 C)) DPEmpty DPEmpty))
    (DPNode (MkDag 1 (bs6 h3c hbe h7b h9f he5 hf3) R0 R0 R0 (RS 61 C)) (DPNode (MkDag 2 (bs6 h7f hf9 he7 h9f he5
    hf2) R0 R0 R0 (RS 93 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 hf2 hf9 hfe h7e he7 h97) (RS 6 D)
    R0 (RS 0 E) (RS 116 A)) (DPNode (MkDag 0 (bs6 h97 hf9 he7 hff he7 h97) R0 R0 R0 (RS 117 A)) (DPNode (MkDag 7
    (bs6 haf hcb he7 h9e h7c hbe) R0 R0 (RS 19 E) R0) (DPNode (MkDag 0 (bs6 hb9 hf9 he7 hbf he7 h97) R0 (RS 35 C)
    R0 R0) (DPNode (MkDag 0 (bs6 hff hf9 hee h7e he7 h97) R0 (RS 67 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs6 h2f hb9 hfb h9f he5 hf3) R0 R0 R0 (RS 99 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hdc hbc hf9 he7
    h97) R0 R0 (RS 51 E) (RS 52 C)) (DPNode (MkDag 2 (bs6 h9f hb9 h7c hf3 he5 hf2) R0 (RS 83 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 h7c hfd hcf he7 he7 h97) R0 R0 R0 (RS 115 B)) DPEmpty DPEmpty))) (DPNode (MkDag
    10 (bs6 h7f hcf hff he7 hcf h2f) R0 R0 R0 (RS 25 B)) (DPNode (MkDag 11 (bs6 h9f hb9 h7c hbc hff hff) R0 (RS 43
    A) R0 R0) (DPNode (MkDag 1 (bs6 hbc hbe he7 hf3 he5 hf3) R0 (RS 75 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs6 hff h3f h3c hfe he5 hf3) R0 (RS 107 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 h3c hf3 hdc hff hff
    h2f) R0 R0 R0 (RS 59 C)) (DPNode (MkDag 11 (bs6 h3f hb9 h7c hbc hff hff) R0 R0 R0 (RS 91 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 6 (bs6 h79 he7 hfc hbf he5 hf7) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 8 (bs6 he7 hcb he5
    hf7 he7 h9f) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 4 (bs6 h79 hf9 h79 hff he5 hf3) R0 R0 R0 (RS 39 B)) (DPNode
    (MkDag 4 (bs6 hbe h79 hf9 hff he5 hf3) R0 R0 (RS 71 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h2f h3f h9e
    h7e he5 hf2) R0 R0 R0 (RS 103 C)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbe hff he7 h9f he5 hf2) R0 R0 (RS 55
    E) R0) (DPNode (MkDag 0 (bs6 h3c hf9 h7c hbe he7 h97) R0 R0 R0 (RS 87 C)) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs6 h9f hb9 hfc hfe he5 hf3) R0 (RS 9 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hf9 h7b hfe h5e he5
    hf2) R0 R0 (RS 31 E) (RS 32 A)) (DPNode (MkDag 3 (bs6 h9f hf9 hfc hff hff h2f) R0 (RS 47 A) R0 R0) (DPNode
    (MkDag 1 (bs6 he7 h9e h7f h9f he5 hf3) (RS 78 D) R0 R0 (RS 79 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h7c
    hf3 hfc hff hff h2f) R0 R0 R0 (RS 7 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 h3c hbe h7f h9f he5 hf3) R0 R0
    R0 (RS 63 C)) (DPNode (MkDag 3 (bs6 he5 hf9 hfc hf7 hff h2f) R0 R0 R0 (RS 95 C)) DPEmpty DPEmpty) DPEmpty)))))
    (DPNode (MkDag 1 (bs6 h97 hb9 hfc hfe he5 hf3) R0 R0 R0 (RS 118 A)) (DPNode (MkDag 1 (bs6 h7c hfe h7f h9f he5
    hf3) R0 R0 R0 (RS 12 B)) (DPNode (MkDag 4 (bs6 h9f hf9 hf9 hff he5 hf3) R0 R0 R0 (RS 11 C)) (DPNode (MkDag 7
    (bs6 h3d hcb he7 h9e h7c hbe) R0 R0 R0 (RS 18 C)) (DPNode (MkDag 0 (bs6 hf9 hf9 h7e h7e he7 h97) (RS 33 D) R0
    R0 (RS 34 A)) (DPNode (MkDag 0 (bs6 hbf hf9 hee h7e he7 h97) R0 (RS 66 C) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 1 (bs6 haf hb9 hfb h9f he5 hf3) R0 R0 (RS 98 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 11 (bs6 h9e h5f h3f
    h72 hff hff) R0 R0 R0 (RS 50 C)) (DPNode (MkDag 2 (bs6 h97 hb9 h7c hf3 he5 hf2) R0 R0 R0 (RS 82 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs6 hbc hfe h7f h9f he5 hf3) R0 (RS 12 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag
    10 (bs6 hff hcf hff he7 hcf h2f) (RS 25 D) R0 (RS 26 E) (RS 27 A)) (DPNode (MkDag 11 (bs6 h97 hb9 h7c hbc hff
    hff) R0 R0 R0 (RS 42 A)) (DPNode (MkDag 0 (bs6 h7f hff hdc hbe he7 h97) (RS 8 D) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs6 hbf h3f h3c hfe he5 hf3) R0 (RS 106 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hbc
    hf3 hdc hff hff h2f) R0 R0 (RS 58 E) R0) (DPNode (MkDag 11 (bs6 hbf hb9 h7c hbc hff hff) R0 R0 (RS 90 E) R0)
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h73 hf3 he7 h9f he5 hf2) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty)))) (DPNode
    (MkDag 5 (bs6 h9f hcf h3f hfe h7f h3f) R0 (RS 14 B) R0 R0) (DPNode (MkDag 7 (bs6 h3f hcb he7 h9e h7c hbe) R0 R0
    R0 (RS 22 B)) (DPNode (MkDag 1 (bs6 hfc hf9 h7c hfe he5 hf3) R0 (RS 38 B) R0 R0) (DPNode (MkDag 2 (bs6 h7e h79
    hfc hf3 he5 hf2) R0 R0 R0 (RS 68 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 haf h3f h9e h7e he5 hf2) R0 R0 (RS
    102 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h73 hfc hbc hf9 he7 h97) R0 R0 R0 (RS 52 B)) (DPNode (MkDag
    0 (bs6 hbc hf9 h7c hbe he7 h97) R0 R0 (RS 86 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f hf9 he7 hff he7
    h97) R0 (RS 3 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs6 hb9 h7b hfe h5e he5 hf2) R0 R0 R0 (RS 30 C))
    (DPNode (MkDag 3 (bs6 h9f hb9 hfc hf7 hff h2f) R0 R0 R0 (RS 46 A)) (DPNode (MkDag 3 (bs6 he5 hf2 hfc hff hff
    h2f) (RS 77 D) R0 R0 (RS 78 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7f hff he7 h9f he5 hf2) R0 R0 R0 (RS
    108 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hbc hbe h7f h9f he5 hf3) R0 R0 (RS 62 E) R0) (DPNode (MkDag 2
    (bs6 hff hf9 he7 h9f he5 hf2) R0 R0 R0 (RS 94 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 3 (bs6 hfc hf3
    hfc hff hff h2f) R0 R0 (RS 110 E) (RS 2 B)) (DPNode (MkDag 1 (bs6 hf3 he5 he7 hf9 he5 hf3) R0 R0 (RS 119 E) (RS
    120 C)) (DPNode (MkDag 7 (bs6 h2f hcb he7 h9e h7c hbe) R0 R0 R0 (RS 20 C)) (DPNode (MkDag 0 (bs6 hf9 hf9 he7
    hbf he7 h97) R0 (RS 36 C) R0 R0) (DPNode (MkDag 2 (bs6 hbe h79 hfc hf3 he5 hf2) R0 R0 R0 (RS 68 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs6 hbf hb9 hfb h9f he5 hf3) R0 R0 (RS 100 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 h73 hdc hbc hf9 he7 h97) R0 R0 R0 (RS 50 B)) (DPNode (MkDag 1 (bs6 h9f hf9 h7c hfe he5 hf3) R0 R0 R0 (RS
    84 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hfd hcf he7 he7 h97) (RS 115 D) R0 R0 (RS 6 C)) DPEmpty
    DPEmpty))) (DPNode (MkDag 3 (bs6 hb9 h7c hfb h9f hcf he7) R0 (RS 28 C) R0 R0) (DPNode (MkDag 2 (bs6 h9f hf9 he7
    h9f he5 hf2) R0 R0 R0 (RS 44 A)) (DPNode (MkDag 1 (bs6 hfc hbe he7 hf3 he5 hf3) R0 (RS 76 B) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 hbf hff he7 h9f he5 hf2) R0 R0 R0 (RS 108 C)) DPEmpty DPEmpty)) (DPNode (MkDag 1
    (bs6 hbc hbe h7b h9f he5 hf3) R0 R0 (RS 60 E) R0) (DPNode (MkDag 2 (bs6 hef hf9 he7 h9f he5 hf2) R0 R0 R0 (RS
    92 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 6 (bs6 hf9 he7 hfc hbf he5 hf7) (RS 15 D) R0 R0 (RS 16 C))
    (DPNode (MkDag 9 (bs6 h7d hcb he5 he7 hb9 h7d) R0 R0 R0 (RS 24 B)) (DPNode (MkDag 4 (bs6 hf9 hf9 h79 hff he5
    hf3) (RS 39 D) R0 R0 (RS 40 A)) (DPNode (MkDag 4 (bs6 h3e h79 hf9 hff he5 hf3) R0 R0 R0 (RS 72 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 hbf h3f h9e h7e he5 hf2) R0 R0 (RS 104 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2
    (bs6 h3e hff he7 h9f he5 hf2) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 11 (bs6 haf hb9 h7c hbc hff hff) R0 R0 (RS 88
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h73 he5 he7 hf9 he5 hf3) R0 R0 R0 (RS 11 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 2 (bs6 h79 h7b hfe h5e he5 hf2) R0 R0 R0 (RS 30 B)) (DPNode (MkDag 4 (bs6 h9f hff hfc hbe he5
    hf3) R0 R0 R0 (RS 48 A)) (DPNode (MkDag 0 (bs6 he7 h9f hcf he7 he7 h97) (RS 79 D) R0 R0 (RS 80 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs6 hdc hfe h7f h9f he5 hf3) R0 R0 R0 (RS 113 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 hbc hbd hcf he7 he7 h97) R0 R0 (RS 64 E) R0) (DPNode (MkDag 3 (bs6 hbc hf9 hfc hff hff h2f) R0 R0 (RS 96
    E) R0) DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_13 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hf3 hfc hff hfc hbe h5f) R0 (RS 98 C) (RS 99 E) (RS 98 C)) (DPNode (MkDag 1 (bs6 hff he5
    hf3 hcf h97 hff) R0 R0 (RS 103 E) (RS 104 A)) (DPNode (MkDag 2 (bs6 hf3 hff hcf hfb h9e h79) (RS 2 D) R0 R0 (RS
    94 C)) (DPNode (MkDag 4 (bs6 hf9 he7 hcf h3f h97 hdf) (RS 4 D) (RS 92 A) R0 (RS 92 A)) (DPNode (MkDag 1 (bs6
    hcf he7 hf3 hff h97 hff) R0 R0 R0 (RS 46 D)) (DPNode (MkDag 9 (bs6 h5f h97 hcf h3c hfc hfb) (RS 17 B) R0 R0 R0)
    (DPNode (MkDag 11 (bs6 hbf h2f hff h3c hf3 hf9) R0 R0 (RS 33 E) R0) (DPNode (MkDag 2 (bs6 hb9 hfd hcf h2f h9e
    h79) R0 (RS 65 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 he7 he5 hf2 hfc hf3 hf9) R0 R0 R0 (RS 97 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 11 (bs6 h79 hfd hcf hcf h9e h79) (RS 49 B) R0 R0 R0) (DPNode (MkDag 2 (bs6 hfe
    he5 hf3 hfb h9e h79) R0 (RS 81 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3e he5 he7 hff h97 hcf) R0 R0
    R0 (RS 113 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h7b h9f hf9 hfc hbe h5f) (RS 25 B) R0 R0 R0) (DPNode
    (MkDag 0 (bs6 hcb he7 hf3 hff h97 hcf) (RS 40 D) R0 R0 (RS 41 D)) (DPNode (MkDag 11 (bs6 h5e he5 hf2 hfc hf3
    hf9) (RS 73 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9e he5 he7 hff h97 hcf) R0 (RS 105 A) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h7f h3f hff h3f h9f hf9) (RS 57 D) R0 R0 R0) (DPNode (MkDag 2 (bs6 hb9
    h7d hcf h2f h9e h79) R0 (RS 12 C) R0 (RS 12 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 2 (bs6 hf9 h7d hcf
    h2f h9e h79) R0 (RS 9 D) (RS 90 E) (RS 9 D)) (DPNode (MkDag 1 (bs6 hfb h9f hf9 hfb h97 hff) (RS 20 D) R0 R0 (RS
    21 A)) (DPNode (MkDag 4 (bs6 h9e he7 hf7 h3f h97 hdf) R0 (RS 37 A) R0 R0) (DPNode (MkDag 4 (bs6 h79 he7 hcf h3f
    h97 hdf) (RS 69 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hfe he7 h9f hff h97 hb9) R0 (RS 102 A) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 h9e h79 hf7 h3c hf2 hff) R0 (RS 53 A) R0 R0) (DPNode (MkDag 7 (bs6
    h9f h3c hbe h7c hbe h79) R0 (RS 85 B) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs6 hbb h97 hff h2f
    h97 hff) R0 (RS 29 C) R0 R0) (DPNode (MkDag 4 (bs6 hcf hfc hfe h5f h97 hdf) R0 R0 R0 (RS 45 D)) (DPNode (MkDag
    2 (bs6 h97 he7 h9f hff h97 hb9) R0 R0 R0 (RS 77 A)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hff h3c hbe h7c hbe
    h79) R0 (RS 7 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hb9 he7 hf3 hcf h9f hf9) R0 (RS 61 C) R0 R0)
    (DPNode (MkDag 5 (bs6 hb9 hfd hcf h3f h9f hf9) R0 (RS 6 C) R0 (RS 6 C)) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 5 (bs6 hf9 hfd hcf h3f h9f hf9) (RS 6 D) R0 (RS 69 E) (RS 93 A)) (DPNode (MkDag 7 (bs6 hf7 h3c hbe h7c
    hbe h79) R0 (RS 107 C) R0 R0) (DPNode (MkDag 9 (bs6 hcf h97 hb9 hfd hf2 hfb) R0 R0 R0 (RS 19 A)) (DPNode (MkDag
    3 (bs6 hbf h3c hbf h3c hf2 hff) R0 (RS 35 C) R0 R0) (DPNode (MkDag 6 (bs6 h9f h7f hcf h2f h97 hcf) R0 (RS 67 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbe he7 h9f hff h97 hb9) R0 (RS 100 C) (RS 101 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs6 h7f h7f hf2 hf9 hf7 hcb) (RS 51 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hff he5 he7
    hff h97 hcf) R0 R0 (RS 83 E) (RS 84 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h7f h9f hf9 hfc hbe
    h5f) (RS 27 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hcb he7 h97 hdc hbe h5f) R0 R0 R0 (RS 43 D)) (DPNode (MkDag 12
    (bs6 h7f he7 h97 hdc hbe h79) (RS 75 A) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f he5 he7 hff h97
    hcf) R0 (RS 10 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hb9 he7 h9e h7c hf2 hff) R0 (RS 59 C) R0 R0)
    (DPNode (MkDag 2 (bs6 h79 h7d hcf h2f h9e h79) R0 R0 R0 (RS 12 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8
    (bs6 hcb hfc hf3 hfe h7f hcb) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 10 (bs6 h7f h9f hb9 hff h97 h9f) R0 R0 R0 (RS
    23 B)) (DPNode (MkDag 4 (bs6 h9f he7 hf7 h3f h97 hdf) R0 (RS 39 C) R0 R0) (DPNode (MkDag 2 (bs6 h5f h7f hcf hfb
    h9e h79) (RS 71 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hbf he5 hf3 hcf h97 hff) R0 R0 R0 (RS 1 C))
    DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h7f h3d hff h3f h9f hf9) (RS 55 B) R0 R0 R0) (DPNode (MkDag 4 (bs6 hf9
    he7 h9f h9f h97 hdf) (RS 86 D) (RS 87 A) (RS 85 E) (RS 87 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs6
    h9f h97 hff h2f h97 hff) R0 (RS 31 C) R0 R0) (DPNode (MkDag 0 (bs6 hcf he7 hee h7f h97 hcf) R0 R0 R0 (RS 47 B))
    (DPNode (MkDag 1 (bs6 hf3 he5 hf3 hcf h97 hff) R0 (RS 79 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f
    he5 hf3 hcf h97 hff) R0 (RS 5 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs6 hb9 he7 hf3 hf3 hee h5f) R0
    (RS 63 C) R0 R0) (DPNode (MkDag 11 (bs6 hbe he5 hf2 hfc hf3 hf9) R0 R0 (RS 95 E) R0) DPEmpty DPEmpty)
    DPEmpty))))) (DPNode (MkDag 3 (bs6 hcf h2f hcf h3c hf2 hff) R0 R0 R0 (RS 91 A)) (DPNode (MkDag 2 (bs6 hf3 he5
    hf3 hfb h9e h79) (RS 5 D) R0 R0 (RS 111 C)) (DPNode (MkDag 6 (bs6 hcb hff hcf h2f h97 hcf) (RS 9 D) R0 R0 (RS 3
    D)) (DPNode (MkDag 9 (bs6 h7f h97 hcf h3c hfc hfb) (RS 18 D) R0 R0 R0) (DPNode (MkDag 11 (bs6 h3f h2f hff h3c
    hf3 hf9) R0 R0 R0 (RS 34 A)) (DPNode (MkDag 2 (bs6 hf9 hfd hcf h2f h9e h79) (RS 65 D) R0 R0 (RS 66 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 12 (bs6 h9f he7 h97 hdc hbe h79) R0 (RS 13 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6
    (bs6 h5f h7f hf2 hf9 hf7 hcb) (RS 50 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbf he5 he7 hff h97 hcf) R0 R0 R0 (RS
    82 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 he5 he7 hff h97 hcf) R0 R0 R0 (RS 7 A)) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs6 h5f h9f hf9 hfc hbe h5f) (RS 26 B) R0 R0 R0) (DPNode (MkDag 10 (bs6 hcb he7 hee h7f h97
    h9f) R0 R0 R0 (RS 42 D)) (DPNode (MkDag 11 (bs6 h7e he5 hf2 hfc hf3 hf9) (RS 74 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs6 h97 he5 he7 hff h97 hcf) R0 R0 R0 (RS 106 A)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 hcf
    h3c hf7 hfc hbe h79) R0 R0 R0 (RS 58 A)) (DPNode (MkDag 6 (bs6 h79 he7 hf3 hf9 hf7 hcb) R0 R0 R0 (RS 11 B))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hf3 hdc hff hfc hbe h5f) (RS 13 D) (RS 0 C) R0 (RS 0 C))
    (DPNode (MkDag 1 (bs6 h9f h9f hf9 hfb h97 hff) R0 (RS 22 B) R0 R0) (DPNode (MkDag 4 (bs6 h97 he7 hf7 h3f h97
    hdf) R0 R0 R0 (RS 38 A)) (DPNode (MkDag 5 (bs6 h79 hfd hcf h3f h9f hf9) (RS 70 B) R0 R0 (RS 6 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 h3e he7 h9f hff h97 hb9) R0 R0 R0 (RS 109 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3
    (bs6 h9e h7f h3f h3c hf2 hff) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 4 (bs6 h79 he7 h9f h9f h97 hdf) R0 R0 R0 (RS
    86 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs6 hfb h97 hff h2f h97 hff) (RS 29 D) R0 R0 (RS 30 A))
    (DPNode (MkDag 6 (bs6 hcf he7 h9f hff h3f hcb) R0 R0 R0 (RS 8 D)) (DPNode (MkDag 2 (bs6 h9f he7 h9f hff h97
    hb9) R0 (RS 78 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 he7 he7 h9f hff h97 hb9) (RS 109 D) R0 R0 (RS
    110 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hf9 he7 hf3 hcf h9f hf9) (RS 61 D) R0 R0 (RS 62 A)) (DPNode
    (MkDag 2 (bs6 h9f h7f hcf hfb h9e h79) R0 (RS 2 C) R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 4 (bs6
    hb9 he7 h9f h9f h97 hdf) R0 (RS 86 C) R0 (RS 86 C)) (DPNode (MkDag 6 (bs6 hf9 he7 hf3 hf9 hf7 hcb) (RS 11 D)
    (RS 88 A) (RS 89 E) (RS 88 A)) (DPNode (MkDag 1 (bs6 hbb h9f hf9 hfb h97 hff) R0 (RS 20 C) R0 R0) (DPNode
    (MkDag 3 (bs6 hff h3c hbf h3c hf2 hff) (RS 35 D) R0 R0 (RS 36 A)) (DPNode (MkDag 6 (bs6 hf3 hff hcf h2f h97
    hcf) (RS 67 D) R0 R0 (RS 68 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h73 hfc hff hfc hbe h5f) R0 R0 R0 (RS 0
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 h7f he7 hff h2f h97 hcf) (RS 52 A) R0 R0 R0) (DPNode (MkDag 0 (bs6
    h7f he5 he7 hff h97 hcf) R0 R0 R0 (RS 82 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 4 (bs6 hcf h9f hb9 hfb
    h97 hdf) R0 R0 R0 (RS 28 A)) (DPNode (MkDag 3 (bs6 hcb hdc hff hfc hf2 hff) R0 R0 R0 (RS 44 D)) (DPNode (MkDag
    2 (bs6 h9e he7 h9f hff h97 hb9) R0 (RS 76 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hbf h3c hbe h7c hbe
    h79) R0 (RS 108 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hf9 he7 h9e h7c hf2 hff) (RS 59 D) R0 R0 (RS
    60 A)) (DPNode (MkDag 4 (bs6 hb9 he7 hcf h3f h97 hdf) R0 (RS 4 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 9 (bs6 h7b h97 hcf h3c hfc hfb) (RS 16 B) R0 R0 R0) (DPNode (MkDag 10 (bs6 hff h9f hb9 hff h97 h9f) (RS
    23 D) R0 R0 (RS 24 B)) (DPNode (MkDag 2 (bs6 hf3 hcf hff h3f h97 hb9) R0 (RS 40 D) R0 R0) (DPNode (MkDag 2 (bs6
    h7f h7f hcf hfb h9e h79) (RS 72 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f he5 hf3 hcf h97 hff) R0
    R0 R0 (RS 1 B)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h5f h3f hff h3f h9f hf9) (RS 56 B) R0 R0 R0) (DPNode
    (MkDag 6 (bs6 hb9 he7 hf3 hf9 hf7 hcb) R0 (RS 11 C) R0 (RS 11 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 11
    (bs6 hf7 h2f hff h3c hf3 hf9) (RS 31 D) R0 R0 (RS 32 C)) (DPNode (MkDag 0 (bs6 h79 he7 hcf hfc hbe h5f) (RS 48
    B) R0 R0 R0) (DPNode (MkDag 2 (bs6 hbe he5 hf3 hfb h9e h79) R0 (RS 80 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag
    0 (bs6 hbe he5 he7 hff h97 hcf) R0 R0 (RS 112 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs6 hf9 he7 hf3 hf3
    hee h5f) (RS 63 D) R0 R0 (RS 64 A)) (DPNode (MkDag 11 (bs6 h3e he5 hf2 hfc hf3 hf9) R0 R0 R0 (RS 96 B)) DPEmpty
    DPEmpty) DPEmpty)))))).

Definition dagTree_14 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hcb hff h9f h3e h79 hfc) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 1 (bs6 he7 hfc hff hee h79
    hf9) (RS 1 D) R0 R0 (RS 2 B)) (DPNode (MkDag 2 (bs6 he7 hf2 hf9 hee h5f h9f) (RS 2 D) R0 R0 (RS 8 B)) (DPNode
    (MkDag 3 (bs6 he5 hf2 hf9 hff hff hf3) (RS 4 D) R0 R0 (RS 3 B)) (DPNode (MkDag 2 (bs6 he7 hf2 hf9 hfe h5f h9f)
    (RS 8 D) R0 R0 (RS 6 B)) (DPNode (MkDag 9 (bs6 he5 hf3 hfc hff hff h2f) (RS 16 D) R0 R0 (RS 17 B)) (DPNode
    (MkDag 6 (bs6 h3e h7e h7f h73 hf3 hf3) R0 R0 R0 (RS 33 C)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h9e h5f h2f
    h73 hf3 hf3) R0 (RS 11 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hcf h9e h5f hfe h79 he7) R0 R0 R0 (RS
    25 D)) (DPNode (MkDag 1 (bs6 h3f hf7 h3f hee h79 hf9) R0 R0 R0 (RS 41 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 7 (bs6 he5 hf3 hcf hee h7f h2f) (RS 12 D) R0 R0 (RS 9 B)) (DPNode (MkDag 12 (bs6 h9f h2f h3f hf3 hff
    hfc) R0 R0 R0 (RS 21 A)) (DPNode (MkDag 2 (bs6 h3f h72 hf9 hee h5f h9f) R0 R0 R0 (RS 37 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 4 (bs6 h79 h7d hcf hf3 hf9 hf3) R0 R0 R0 (RS 5 B)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h9f
    h3e h79 hf3 hf9 hf3) R0 R0 R0 (RS 29 C)) (DPNode (MkDag 5 (bs6 hbf h2f hcb hf2 hff hf2) R0 R0 (RS 45 E) R0)
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs6 he7 hf2 hf3 hf2 hff hf2) (RS 6 D) R0 R0 (RS 48 A)) (DPNode
    (MkDag 6 (bs6 he5 hee h7f h73 hf3 hf3) (RS 10 D) R0 R0 (RS 1 B)) (DPNode (MkDag 11 (bs6 hbf hcf hcb hee h79
    h7f) R0 (RS 19 C) R0 R0) (DPNode (MkDag 2 (bs6 h2f h72 hf9 hee h5f h9f) R0 R0 R0 (RS 35 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 2 (bs6 h7f he5 hf9 h7e h5f h9f) R0 R0 R0 (RS 7 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hb9
    hf3 hcb hf3 hcf hf3) R0 (RS 27 C) R0 R0) (DPNode (MkDag 2 (bs6 h9f he5 hf9 h7e h5f h9f) R0 (RS 43 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 9 (bs6 h65 hf3 hdc hff hff h2f) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 2
    (bs6 h9f hff h3f h9e h7f h73) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 2 (bs6 h3f hf2 hf9 hfe h5f h9f) R0 R0 R0 (RS
    39 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs6 h73 hee h7f h73 hf3 hf3) R0 R0 R0 (RS 29 B)) (DPNode
    (MkDag 7 (bs6 hff hcf h3f h3e h7f h2f) R0 R0 (RS 47 E) (RS 12 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 3
    (bs6 he5 hf3 hcb hf3 hcf hf3) (RS 3 D) R0 R0 (RS 10 B)) (DPNode (MkDag 4 (bs6 hf9 h7d hcf hf3 hf9 hf3) (RS 5 D)
    R0 R0 (RS 0 D)) (DPNode (MkDag 5 (bs6 he5 hf2 hf9 hf2 hff hf2) (RS 9 D) R0 R0 (RS 4 B)) (DPNode (MkDag 10 (bs6
    he5 he7 hf9 h7e h5f h3c) (RS 17 D) R0 R0 (RS 18 A)) (DPNode (MkDag 2 (bs6 haf h72 hf9 hee h5f h9f) R0 R0 (RS 34
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 10 (bs6 h9e h5f h3f hfe h7f h3c) R0 (RS 50 B) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hcf hff hff hfe h5f h7c) R0 R0 R0 (RS 26 A)) (DPNode (MkDag 10 (bs6 he7 hff h3f hfe h7f
    h3c) R0 R0 R0 (RS 42 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 8 (bs6 h7c hbf h3c hfc hfc hff) (RS 14 E) R0
    R0 R0) (DPNode (MkDag 2 (bs6 h97 hff h3f h9e h7f h73) R0 (RS 22 A) R0 R0) (DPNode (MkDag 2 (bs6 hbf hf2 hf9 hfe
    h5f h9f) R0 R0 (RS 38 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs6 hf3 hee h7f h73 hf3 hf3) R0 R0 (RS
    30 E) (RS 31 C)) (DPNode (MkDag 5 (bs6 h3f h2f hcb hf2 hff hf2) R0 R0 R0 (RS 0 D)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 2 (bs6 hff he5 hf9 h7e h5f h9f) (RS 7 D) R0 R0 (RS 51 A)) (DPNode (MkDag 1 (bs6 h9e h5f h3f hee
    h79 hf9) R0 R0 R0 (RS 49 A)) (DPNode (MkDag 11 (bs6 hff hcf hcb hee h79 h7f) R0 (RS 20 A) R0 R0) (DPNode (MkDag
    2 (bs6 hbf h72 hf9 hee h5f h9f) R0 R0 (RS 36 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h9f h2f hcb hf2 hff
    hf2) R0 (RS 52 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hf9 hf3 hcb hf3 hcf hf3) R0 (RS 28 A) R0 R0)
    (DPNode (MkDag 5 (bs6 hf7 h2f hcb hf2 hff hf2) (RS 43 D) R0 R0 (RS 44 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 9 (bs6 he5 hf3 hdc hff hff h2f) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 13 (bs6 h7f h97 hcb hee h5f h3c) (RS
    24 D) R0 R0 R0) (DPNode (MkDag 1 (bs6 hbf hf7 h3f hee h79 hf9) R0 R0 (RS 40 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 6 (bs6 hbe h7e h7f h73 hf3 hf3) R0 R0 (RS 32 E) R0) (DPNode (MkDag 7 (bs6 h7f hcf h3f h3e h7f
    h2f) R0 R0 R0 (RS 46 B)) DPEmpty DPEmpty) DPEmpty))))).

Definition dagSub_15_48 : DagPTree :=
  DPNode (MkDag 2 (bs6 hf3 hcf hf3 hf9 h7d hcb) R0 R0 (RS 36 E) (RS 37 C)) (DPNode (MkDag 2 (bs6 hb9 he5 hf3 hff
    h72 hf9) R0 R0 R0 (RS 17 C)) (DPNode (MkDag 4 (bs6 h7f hdc hfe he7 hff hcb) (RS 33 B) R0 R0 R0) (DPNode (MkDag
    6 (bs6 hcf hcb hee h79 hfd hcb) R0 R0 R0 (RS 65 C)) (DPNode (MkDag 5 (bs6 h9f hff h9e h7f h3e h5e) R0 R0 R0 (RS
    129 A)) (DPNode (MkDag 4 (bs6 hfc hff h97 hcf he7 hcb) R0 R0 (RS 257 E) (RS 258 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 1 (bs6 hbe he5 hf9 hfc hfe h79) R0 R0 (RS 193 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbd
    hcb hff hb9 hfd hcb) R0 R0 (RS 97 E) R0) (DPNode (MkDag 0 (bs6 h73 hcf h3e h5f hff hf3) R0 R0 R0 (RS 159 B))
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hf9 hfc hbd hcf h2f hcb) R0 (RS 225 A) R0 R0) DPEmpty DPEmpty))) (DPNode
    (MkDag 1 (bs6 h7b h97 hb9 hfc hfe h79) (RS 49 B) R0 R0 R0) (DPNode (MkDag 3 (bs6 hbf h3f h9f hcf hcf hcb) R0
    (RS 81 C) R0 R0) (DPNode (MkDag 5 (bs6 hb9 hfc hf9 hfc hbe h5e) R0 R0 R0 (RS 145 C)) (DPNode (MkDag 8 (bs6 h9e
    h7c hf3 hf9 hfd hcb) R0 (RS 273 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hf9 he7 h97 hcf h2f
    h97) (RS 208 D) R0 R0 (RS 209 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hf3 hcb hff hfe h7f h97) (RS 112 D)
    R0 R0 (RS 113 C)) (DPNode (MkDag 4 (bs6 h79 hf7 h2f he5 hf2 hf9) R0 R0 R0 (RS 177 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 h79 hfc hf3 hcf h2f h97) R0 R0 R0 (RS 239 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 h97 hb9
    h7e h5f h2f hcb) R0 (RS 25 A) R0 R0) (DPNode (MkDag 6 (bs6 h5f h97 hcb he5 hf2 hf9) (RS 41 B) R0 R0 R0) (DPNode
    (MkDag 2 (bs6 h3f h3c hff h2f h72 hf9) R0 R0 R0 (RS 73 A)) (DPNode (MkDag 7 (bs6 hbf h2f h3e he5 hf2 hff) R0 R0
    (RS 11 E) R0) (DPNode (MkDag 2 (bs6 hf3 hff h97 hcf h2f hcb) (RS 264 D) R0 (RS 265 E) (RS 266 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 hf9 he5 hf3 hcf h3e h79) R0 R0 (RS 201 E) (RS 202 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 5 (bs6 hfc hf9 he7 h9f h3f h97) R0 R0 R0 (RS 105 B)) (DPNode (MkDag 6 (bs6 hbe h5f h9e h7f h7f
    hcb) R0 (RS 169 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hf9 hfc hf2 hf9 h7d hcb) R0 R0 (RS 233 E) (RS
    234 A)) DPEmpty DPEmpty))) (DPNode (MkDag 10 (bs6 hee h79 hff hfc hf2 hf9) (RS 56 D) R0 R0 (RS 57 B)) (DPNode
    (MkDag 2 (bs6 h3f h3c hfd hcf h2f hcb) R0 R0 R0 (RS 89 A)) (DPNode (MkDag 2 (bs6 hff hff hdc hfe h7d hcb) R0
    (RS 153 C) R0 R0) (DPNode (MkDag 0 (bs6 h97 hff he5 hf7 h3f h97) R0 (RS 0 A) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 2 (bs6 hf9 h7b h9f hb9 hfd hcb) R0 R0 (RS 217 E) (RS 218 C)) DPEmpty DPEmpty)) (DPNode (MkDag 9
    (bs6 haf h9f h97 hcf he7 hcb) R0 R0 (RS 121 E) R0) (DPNode (MkDag 9 (bs6 hcf h9f h9f he7 hfd hcb) R0 R0 R0 (RS
    185 D)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hf3 hff h9f hf3 hfe h5e) R0 R0 (RS 249 E) (RS 250 C)) DPEmpty
    DPEmpty)))).

Definition dagSub_15_49 : DagPTree :=
  DPNode (MkDag 7 (bs6 hcb hff hcb he5 hf2 hff) R0 R0 R0 (RS 141 D)) (DPNode (MkDag 4 (bs6 hf7 h3f hf3 hcb he7 hcb)
    R0 (RS 21 C) R0 R0) (DPNode (MkDag 2 (bs6 h73 hcf hf3 hf9 h7d hcb) R0 R0 R0 (RS 8 B)) (DPNode (MkDag 3 (bs6 h2f
    he7 h9f h9f h7f hcb) R0 R0 R0 (RS 69 C)) (DPNode (MkDag 3 (bs6 hff hfe h7e h7e h7d hcb) R0 (RS 133 A) R0 R0)
    (DPNode (MkDag 8 (bs6 h9f hff h9f hf3 hff hcb) R0 (RS 261 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6
    (bs6 hf7 h2f h3e h7f hf2 hf9) R0 (RS 197 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbf hcb hff hb9 hfd
    hcb) R0 R0 (RS 101 E) R0) (DPNode (MkDag 10 (bs6 h72 hf7 h2f hcf hff hcb) R0 R0 R0 (RS 163 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 5 (bs6 hb9 hfc hff hf3 hfe h5e) R0 (RS 229 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 10 (bs6
    hcf hdf he7 hff h3d hcb) R0 R0 R0 (RS 53 C)) (DPNode (MkDag 0 (bs6 h9f hfe he7 hf7 h3f h97) R0 R0 R0 (RS 85 C))
    (DPNode (MkDag 1 (bs6 hf9 hf9 hf9 hfc hfe h79) (RS 148 D) R0 R0 (RS 149 A)) (DPNode (MkDag 4 (bs6 hbf hff h97
    hcf he7 hcb) R0 (RS 277 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hf9 hfc hff h2f h72 hf9) R0
    R0 (RS 213 E) (RS 214 A)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 h7e h7f h97 hf9 he5 hff) R0 R0 R0 (RS 117 B))
    (DPNode (MkDag 6 (bs6 hbe h7c hff he5 hf2 hf9) R0 R0 (RS 181 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs6 hf9
    hff hef hf3 hff hcb) R0 R0 (RS 245 E) (RS 246 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 3 (bs6 h7f he5 he7 h9f h7f
    hcb) (RS 7 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 hfb h97 hcb he7 hfd hcb) (RS 44 D) R0 R0 (RS 45 A)) (DPNode
    (MkDag 4 (bs6 hf7 h3f h9f hcf he7 hcb) R0 R0 (RS 77 E) (RS 78 C)) (DPNode (MkDag 6 (bs6 hf9 h7d hcb he5 hf2
    hf9) (RS 140 D) R0 R0 (RS 12 D)) (DPNode (MkDag 5 (bs6 hee h7f h9f hf3 hfe h5e) R0 R0 R0 (RS 269 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 9 (bs6 hb9 he7 h9f hf9 he7 hcb) R0 R0 R0 (RS 205 C)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 h7e h7f h72 hf3 he5 hf3) R0 R0 R0 (RS 107 B)) (DPNode (MkDag 4 (bs6 hbe h7c hbe he7 hff hcb) R0
    (RS 173 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hb9 hfc hf2 hf3 hff hcb) R0 (RS 237 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 9 (bs6 hbe h7e h7e h5f h2f hcb) R0 R0 (RS 61 E) R0) (DPNode (MkDag 0 (bs6 hf7 h3c hf3
    hcb hcf hfd) R0 (RS 93 C) R0 R0) (DPNode (MkDag 1 (bs6 h9f hcf h9e h79 he7 hcb) R0 R0 R0 (RS 157 A)) (DPNode
    (MkDag 1 (bs6 hbe hfc hf3 hcf h2f hcb) R0 R0 (RS 285 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 he7
    hcb he7 h9f h3f h97) (RS 220 D) R0 R0 (RS 221 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hb2 hfb h9f hf3 hff
    hcb) R0 (RS 125 C) R0 R0) (DPNode (MkDag 4 (bs6 hb9 hfd hcb he7 hff hcb) R0 (RS 189 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs6 he7 hdc hf3 hcf h2f hcb) (RS 252 D) R0 R0 (RS 253 B)) DPEmpty DPEmpty)))).

Definition dagSub_15_50 : DagPTree :=
  DPNode (MkDag 6 (bs6 hf3 hf9 hf7 hcb hf2 hf9) R0 (RS 131 C) R0 R0) (DPNode (MkDag 2 (bs6 h79 he5 hf3 hff h72 hf9)
    R0 R0 R0 (RS 17 B)) (DPNode (MkDag 2 (bs6 h7f hfc hfc hf9 h7d hcb) (RS 35 D) R0 R0 R0) (DPNode (MkDag 5 (bs6
    h3e h5f h3c hfe h5f h97) R0 R0 R0 (RS 67 C)) (DPNode (MkDag 10 (bs6 hf3 hcf h9f hdf hf2 hf9) R0 (RS 10 C) R0
    R0) (DPNode (MkDag 8 (bs6 h9e hff h9f hf3 hff hcb) R0 (RS 259 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs6 he7 he5 hf9 hfc hfe h79) R0 R0 R0 (RS 195 A)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 haf hcb hff
    hb9 hfd hcb) R0 R0 (RS 99 E) R0) (DPNode (MkDag 3 (bs6 h72 hfb hfe h79 h7d hcb) R0 R0 R0 (RS 161 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 6 (bs6 hf9 hfc hff hb9 hfd hcb) R0 R0 (RS 227 E) (RS 228 A)) DPEmpty DPEmpty))) (DPNode
    (MkDag 1 (bs6 h7f h97 hb9 hfc hfe h79) (RS 51 D) R0 R0 R0) (DPNode (MkDag 2 (bs6 h9f h3f h9f hb9 hfd hcb) R0 R0
    R0 (RS 83 A)) (DPNode (MkDag 5 (bs6 h79 hfc hf9 hfc hbe h5e) R0 R0 R0 (RS 145 B)) (DPNode (MkDag 11 (bs6 h9f
    hdc hf3 hcf h2f hff) R0 (RS 275 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hf9 hfc hf7 h2f h72
    hf9) R0 (RS 211 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 h3e h7b h97 hf9 he5 hff) R0 R0 R0 (RS 115 B))
    (DPNode (MkDag 4 (bs6 h9f h3f h2f he5 hf2 hf9) R0 (RS 179 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 hf9
    hff he7 hcf he7 hcb) R0 (RS 243 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 10 (bs6 h9f hcb hcf hcf hff hcb)
    R0 (RS 27 A) R0 R0) (DPNode (MkDag 7 (bs6 hcf h97 hcb he5 hf2 hff) R0 R0 R0 (RS 43 A)) (DPNode (MkDag 6 (bs6
    hff h3f h9f h3f hf2 hf9) R0 (RS 75 A) R0 R0) (DPNode (MkDag 0 (bs6 h9f hcf hfe h5e hff h97) R0 (RS 139 B) R0
    R0) (DPNode (MkDag 5 (bs6 hbe h7b h9f hf3 hfe h5e) R0 R0 (RS 267 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 3 (bs6 hb9 he7 hee h79 h7d hcb) R0 (RS 203 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hfc hff hff
    hf9 h7d hcb) R0 R0 R0 (RS 107 C)) (DPNode (MkDag 11 (bs6 hf2 hf9 hf7 hff h2f hff) R0 (RS 171 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs6 hb9 hfc hf2 hf9 he7 hcb) R0 (RS 235 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag
    0 (bs6 hfe h7f h3e h5f hff hf3) R0 R0 (RS 59 E) (RS 60 C)) (DPNode (MkDag 7 (bs6 hff h3c hbe h5f he5 hff) (RS
    90 D) R0 R0 (RS 91 A)) (DPNode (MkDag 4 (bs6 h9e h7c hf3 hcb he7 hcb) R0 R0 R0 (RS 155 A)) (DPNode (MkDag 6
    (bs6 h73 hcf h97 hb9 hfd hcb) R0 R0 R0 (RS 281 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 9 (bs6 hbf hf3 hf9
    h79 hee h79) R0 R0 (RS 219 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 hbf h9f h97 hcf he7 hcb) R0 R0 (RS
    123 E) R0) (DPNode (MkDag 9 (bs6 hb9 he7 hcb he7 hfd hcb) R0 (RS 187 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag
    12 (bs6 hbe h7c hf3 hff h2f hcb) R0 R0 (RS 251 E) R0) DPEmpty DPEmpty)))).

Definition dagSub_15_51 : DagPTree :=
  DPNode (MkDag 8 (bs6 hb9 he5 hff he7 h9f hcb) R0 (RS 15 C) R0 R0) (DPNode (MkDag 4 (bs6 hff h3f hf3 hcb he7 hcb)
    R0 (RS 23 A) R0 R0) (DPNode (MkDag 0 (bs6 h73 hfb hfe h5e hff h97) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 3 (bs6
    h3f he7 h9f h9f h7f hcb) R0 R0 R0 (RS 71 C)) (DPNode (MkDag 7 (bs6 hf7 h2f h3e he5 hf2 hff) R0 R0 (RS 135 E)
    (RS 136 C)) (DPNode (MkDag 2 (bs6 hf3 hdf h97 hcf h2f hcb) R0 R0 (RS 263 E) (RS 264 C)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 6 (bs6 hff h2f h3e h7f hf2 hf9) R0 (RS 199 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 9
    (bs6 he7 hcf h3f hf9 hfe h79) R0 R0 R0 (RS 103 B)) (DPNode (MkDag 5 (bs6 h73 hcb hdc hfe h5f h97) R0 R0 R0 (RS
    165 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hb9 hfc hfe h5f he5 hff) R0 (RS 231 C) R0 R0) DPEmpty DPEmpty)))
    (DPNode (MkDag 2 (bs6 h3c hf2 hfc hfe h7d hcb) R0 R0 R0 (RS 55 C)) (DPNode (MkDag 2 (bs6 h77 h3c hfd hcf h2f
    hcb) R0 R0 R0 (RS 85 B)) (DPNode (MkDag 9 (bs6 hf9 he5 hf3 hfb hfd hcb) R0 (RS 151 C) R0 R0) (DPNode (MkDag 2
    (bs6 hfe h5f h97 hb9 hfd hcb) R0 (RS 279 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 9 (bs6 hb9 hfb h9f
    hcf h3f hcb) R0 (RS 215 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 hbc hfb h97 hcf he7 hcb) R0 R0 (RS
    119 E) R0) (DPNode (MkDag 9 (bs6 he7 hcf h9e he7 hfd hcb) R0 R0 R0 (RS 183 B)) DPEmpty DPEmpty) (DPNode (MkDag
    9 (bs6 h9f h3e h79 h79 hee h79) R0 (RS 247 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 7 (bs6 h5e he7 h97 he5
    hf2 hff) (RS 31 B) R0 R0 R0) (DPNode (MkDag 4 (bs6 h7f h97 hcb he7 hff hcb) R0 R0 R0 (RS 47 B)) (DPNode (MkDag
    4 (bs6 hbf h3f h9f hcf he7 hcb) R0 R0 (RS 79 E) R0) (DPNode (MkDag 8 (bs6 hb9 he7 hcf hcb hff hcb) R0 (RS 143
    C) R0 R0) (DPNode (MkDag 12 (bs6 hfc hfc hf3 hff h2f hcb) R0 R0 (RS 271 E) (RS 272 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 9 (bs6 h79 he7 h9f hf9 he7 hcb) R0 R0 R0 (RS 205 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1
    (bs6 h3c hff h73 hff h2f hcb) R0 R0 R0 (RS 111 A)) (DPNode (MkDag 2 (bs6 hbc hfc hbc hf9 h7d hcb) R0 (RS 175 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hb9 hfc hf3 hcf h2f h97) R0 R0 R0 (RS 239 C)) DPEmpty DPEmpty)))
    (DPNode (MkDag 10 (bs6 he7 hcf h3d hcf hff hcb) (RS 62 D) R0 R0 (RS 63 B)) (DPNode (MkDag 0 (bs6 hff h3c hf3
    hcb hcf hfd) R0 (RS 95 B) R0 R0) (DPNode (MkDag 0 (bs6 h9f h9f h9e h7f h2f hfd) R0 R0 R0 (RS 159 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 hcf hcb he7 hf7 h3f h97) R0 R0 R0 (RS 223 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5
    (bs6 h9e hff h9e h7f h3e h5e) R0 R0 R0 (RS 127 A)) (DPNode (MkDag 8 (bs6 h9f h7f hcf hcb hff hcb) R0 (RS 191 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 h5e h7c hf3 hcf h2f hff) (RS 255 B) R0 R0 R0) DPEmpty
    DPEmpty)))).

Definition dagSub_15_52 : DagPTree :=
  DPNode (MkDag 1 (bs6 h3f hff h9e h79 he7 hcb) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 2 (bs6 hf9 he5 hf3 hff h72 hf9)
    R0 R0 (RS 18 E) (RS 19 A)) (DPNode (MkDag 2 (bs6 h5f hfc hfc hf9 h7d hcb) (RS 34 B) R0 R0 R0) (DPNode (MkDag 5
    (bs6 hbe h5f h3c hfe h5f h97) R0 R0 (RS 66 E) R0) (DPNode (MkDag 4 (bs6 h9e h5f h9e h7f h72 hf9) R0 (RS 130 C)
    R0 R0) (DPNode (MkDag 4 (bs6 h7c hff h97 hcf he7 hcb) R0 R0 R0 (RS 256 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs6 h3e he5 hf9 hfc hfe h79) R0 R0 R0 (RS 194 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h3d hcb hff
    hb9 hfd hcb) R0 R0 R0 (RS 98 C)) (DPNode (MkDag 3 (bs6 hf2 hfb hfe h79 h7d hcb) R0 R0 (RS 162 E) (RS 163 C))
    DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hb9 hfc hff hb9 hfd hcb) R0 R0 R0 (RS 226 C)) DPEmpty DPEmpty))) (DPNode
    (MkDag 1 (bs6 h5f h97 hb9 hfc hfe h79) (RS 50 B) R0 R0 R0) (DPNode (MkDag 3 (bs6 hff h3f h9f hcf hcf hcb) R0
    (RS 82 A) R0 R0) (DPNode (MkDag 5 (bs6 hf9 hfc hf9 hfc hbe h5e) R0 R0 (RS 146 E) (RS 147 A)) (DPNode (MkDag 11
    (bs6 h97 hdc hf3 hcf h2f hff) R0 R0 R0 (RS 274 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hb9 hfc hf7
    h2f h72 hf9) R0 (RS 210 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 hbe h7b h97 hf9 he5 hff) R0 R0 (RS
    114 E) R0) (DPNode (MkDag 4 (bs6 hf9 hf7 h2f he5 hf2 hf9) (RS 177 D) R0 R0 (RS 178 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 4 (bs6 hb9 hff he7 hcf he7 hcb) R0 (RS 242 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 9 (bs6 h9f hb9
    h7e h5f h2f hcb) R0 R0 R0 (RS 26 A)) (DPNode (MkDag 6 (bs6 h7f h97 hcb he5 hf2 hf9) (RS 42 D) R0 R0 R0) (DPNode
    (MkDag 6 (bs6 hbf h3f h9f h3f hf2 hf9) R0 (RS 74 C) R0 R0) (DPNode (MkDag 4 (bs6 he7 hf2 hf3 he7 hff hcb) (RS
    137 D) R0 R0 (RS 138 A)) (DPNode (MkDag 2 (bs6 h73 hff h97 hcf h2f hcb) R0 R0 R0 (RS 264 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs6 h79 he5 hf3 hcf h3e h79) R0 R0 R0 (RS 200 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3
    (bs6 h7c hff hff hf9 h7d hcb) R0 R0 R0 (RS 106 B)) (DPNode (MkDag 6 (bs6 hfe h5f h9e h7f h7f hcb) R0 (RS 170 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h79 hfc hf2 hf9 h7d hcb) R0 R0 R0 (RS 232 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 10 (bs6 h7e h79 hff hfc hf2 hf9) (RS 58 C) R0 R0 R0) (DPNode (MkDag 7 (bs6 hbf h3c hbe h5f he5
    hff) R0 (RS 90 C) R0 R0) (DPNode (MkDag 6 (bs6 hf2 hfc hbe h7f hf2 hf9) R0 (RS 154 A) R0 R0) (DPNode (MkDag 6
    (bs6 hf3 hcf h97 hb9 hfd hcb) R0 R0 (RS 282 E) (RS 283 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h79
    h7b h9f hb9 hfd hcb) R0 R0 R0 (RS 216 B)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 h2f h9f h97 hcf he7 hcb) R0
    R0 R0 (RS 122 C)) (DPNode (MkDag 7 (bs6 hcf h2f hcb he5 hf2 hff) R0 R0 R0 (RS 186 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 5 (bs6 h73 hff h9f hf3 hfe h5e) R0 R0 R0 (RS 248 B)) DPEmpty DPEmpty)))).

Definition dagSub_15_53 : DagPTree :=
  DPNode (MkDag 5 (bs6 h73 hfb h9f hf3 hfe h5e) R0 R0 R0 (RS 283 B)) (DPNode (MkDag 4 (bs6 hbf h3f hf3 hcb he7 hcb)
    R0 (RS 22 C) R0 R0) (DPNode (MkDag 0 (bs6 hf3 hfb hfe h5e hff h97) R0 R0 (RS 38 E) (RS 39 B)) (DPNode (MkDag 3
    (bs6 hbf he7 h9f h9f h7f hcb) R0 R0 (RS 70 E) R0) (DPNode (MkDag 2 (bs6 h9f h2f h9f he5 hf2 hf9) R0 R0 R0 (RS
    134 C)) (DPNode (MkDag 0 (bs6 h9e h5f he5 hf7 h3f h97) R0 R0 R0 (RS 262 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 6 (bs6 hbf h2f h3e h7f hf2 hf9) R0 (RS 198 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h3f hcb hff
    hb9 hfd hcb) R0 R0 R0 (RS 102 B)) (DPNode (MkDag 5 (bs6 hf3 hcb hdc hfe h5f h97) R0 R0 (RS 166 E) (RS 4 C))
    DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hf9 hfc hff hf3 hfe h5e) (RS 229 D) R0 R0 (RS 230 A)) DPEmpty DPEmpty)))
    (DPNode (MkDag 2 (bs6 hbc hf2 hfc hfe h7d hcb) R0 R0 (RS 54 E) R0) (DPNode (MkDag 2 (bs6 hf7 h3c hfd hcf h2f
    hcb) R0 R0 (RS 86 E) (RS 87 C)) (DPNode (MkDag 9 (bs6 hb9 he5 hf3 hfb hfd hcb) R0 (RS 150 C) R0 R0) (DPNode
    (MkDag 4 (bs6 hff hff h97 hcf he7 hcb) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h79
    hfc hff h2f h72 hf9) R0 R0 R0 (RS 212 B)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 hfe h7f h97 hf9 he5 hff) R0
    R0 R0 (RS 118 C)) (DPNode (MkDag 6 (bs6 h3e h7c hff he5 hf2 hf9) R0 R0 R0 (RS 182 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 8 (bs6 h79 hff hef hf3 hff hcb) R0 R0 R0 (RS 244 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 5 (bs6 h7f hfb
    h9f hdf hee h5e) (RS 30 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 h9f h97 hcb he7 hfd hcb) R0 (RS 46 B) R0 R0) (DPNode
    (MkDag 4 (bs6 h77 h3f h9f hcf he7 hcb) R0 R0 R0 (RS 76 B)) (DPNode (MkDag 4 (bs6 hcf h2f hcb he7 hff hcb) R0 R0
    R0 (RS 142 A)) (DPNode (MkDag 5 (bs6 h7e h7f h9f hf3 hfe h5e) (RS 270 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 9 (bs6 hf9 he7 h9f hf9 he7 hcb) R0 R0 (RS 206 E) (RS 207 A)) DPEmpty DPEmpty)) (DPNode (MkDag 1
    (bs6 hbc hff h73 hff h2f hcb) R0 R0 (RS 110 E) R0) (DPNode (MkDag 4 (bs6 hfe h7c hbe he7 hff hcb) R0 (RS 174 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hf9 hfc hf2 hf3 hff hcb) R0 (RS 238 A) R0 R0) DPEmpty DPEmpty)))
    (DPNode (MkDag 9 (bs6 h3e h7e h7e h5f h2f hcb) R0 R0 R0 (RS 62 B)) (DPNode (MkDag 0 (bs6 hbf h3c hf3 hcb hcf
    hfd) R0 (RS 94 C) R0 R0) (DPNode (MkDag 0 (bs6 h97 h9f h9e h7f h2f hfd) R0 (RS 158 A) R0 R0) (DPNode (MkDag 1
    (bs6 h3e hfc hf3 hcf h2f hcb) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7d hcb he7
    hf7 h3f h97) (RS 222 D) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hf2 hfb h9f hf3 hff hcb) R0 (RS 126
    A) R0 R0) (DPNode (MkDag 4 (bs6 hf9 hfd hcb he7 hff hcb) (RS 189 D) R0 R0 (RS 190 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 1 (bs6 h7c hfc hf3 hcf h2f hcb) (RS 254 B) R0 R0 R0) DPEmpty DPEmpty)))).

Definition dagSub_15_54 : DagPTree :=
  DPNode (MkDag 7 (bs6 h3f h2f h3e he5 hf2 hff) R0 R0 R0 (RS 137 B)) (DPNode (MkDag 4 (bs6 h9f h3d hf3 hcb he7 hcb)
    R0 (RS 20 C) R0 R0) (DPNode (MkDag 6 (bs6 hcf hfc hff he5 hf2 hf9) R0 R0 R0 (RS 8 C)) (DPNode (MkDag 3 (bs6 haf
    he7 h9f h9f h7f hcb) R0 R0 (RS 68 E) R0) (DPNode (MkDag 0 (bs6 hf3 hf3 hee h79 hff hf3) R0 (RS 132 C) R0 R0)
    (DPNode (MkDag 8 (bs6 h97 hff h9f hf3 hff hcb) R0 R0 R0 (RS 260 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1
    (bs6 h9f h3c hfc hf3 he7 hcb) R0 (RS 196 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h2f hcb hff hb9 hfd
    hcb) R0 R0 R0 (RS 100 C)) (DPNode (MkDag 10 (bs6 hf2 hf7 h2f hcf hff hcb) R0 R0 (RS 164 E) (RS 165 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 6 (bs6 h79 hfc hff hb9 hfd hcb) R0 R0 R0 (RS 226 B)) DPEmpty DPEmpty))) (DPNode (MkDag
    10 (bs6 hcf h9f hff hff h72 hf9) R0 R0 R0 (RS 52 D)) (DPNode (MkDag 0 (bs6 h97 hfe he7 hf7 h3f h97) R0 (RS 84
    A) R0 R0) (DPNode (MkDag 1 (bs6 hb9 hf9 hf9 hfc hfe h79) R0 (RS 148 C) R0 R0) (DPNode (MkDag 4 (bs6 hf7 hff h97
    hcf he7 hcb) R0 (RS 276 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hb9 hfc hff h2f h72 hf9) R0
    R0 R0 (RS 212 C)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 hee h7f h97 hf9 he5 hff) R0 R0 R0 (RS 116 B)) (DPNode
    (MkDag 2 (bs6 hf3 he7 hfe he5 hf2 hf9) (RS 179 D) R0 R0 (RS 180 C)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs6 hb9
    hff hef hf3 hff hcb) R0 R0 R0 (RS 244 C)) DPEmpty DPEmpty)))) (DPNode (MkDag 1 (bs6 h9e h79 hfc hff hfe h79) R0
    R0 R0 (RS 28 B)) (DPNode (MkDag 9 (bs6 hbb h97 hcb he7 hfd hcb) R0 (RS 44 C) R0 R0) (DPNode (MkDag 9 (bs6 h9f
    h3f h9f hcf h3f hcb) R0 R0 R0 (RS 76 C)) (DPNode (MkDag 6 (bs6 h79 h7d hcb he5 hf2 hf9) R0 R0 R0 (RS 140 B))
    (DPNode (MkDag 5 (bs6 h3e h7b h9f hf3 hfe h5e) R0 R0 R0 (RS 268 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3
    (bs6 hf9 he7 hee h79 h7d hcb) R0 (RS 204 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hfe h7f h72 hf3 he5
    hf3) (RS 107 D) R0 (RS 108 E) (RS 109 C)) (DPNode (MkDag 7 (bs6 hf3 hff h97 he5 hf2 hff) R0 (RS 172 C) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hf9 hfc hf2 hf9 he7 hcb) (RS 235 D) R0 R0 (RS 236 A)) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs6 h7e h7f h3e h5f hff hf3) R0 R0 R0 (RS 58 B)) (DPNode (MkDag 3 (bs6 h9f h3c hf3 hcb hff
    hcb) R0 (RS 92 C) R0 R0) (DPNode (MkDag 1 (bs6 h97 hcf h9e h79 he7 hcb) R0 (RS 156 A) R0 R0) (DPNode (MkDag 5
    (bs6 hf3 hfb h9f hf3 hfe h5e) (RS 283 D) R0 (RS 13 E) (RS 284 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 9
    (bs6 h3f hf3 hf9 h79 hee h79) R0 R0 R0 (RS 220 B)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 h3f h9f h97 hcf he7
    hcb) R0 R0 R0 (RS 124 A)) (DPNode (MkDag 9 (bs6 hf9 he7 hcb he7 hfd hcb) (RS 187 D) R0 R0 (RS 188 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 12 (bs6 h3e h7c hf3 hff h2f hcb) R0 R0 R0 (RS 252 B)) DPEmpty DPEmpty)))).

Definition dagSub_15_55 : DagPTree :=
  DPNode (MkDag 8 (bs6 hf9 he5 hff he7 h9f hcb) R0 (RS 16 A) R0 R0) (DPNode (MkDag 8 (bs6 h9f h3f h9e h5f h7f hcb)
    R0 R0 R0 (RS 24 A)) (DPNode (MkDag 6 (bs6 h7b h97 hcb he5 hf2 hf9) (RS 40 B) R0 R0 R0) (DPNode (MkDag 2 (bs6
    hbf h3c hff h2f h72 hf9) R0 R0 (RS 72 E) R0) (DPNode (MkDag 7 (bs6 h77 h2f h3e he5 hf2 hff) R0 R0 R0 (RS 134
    B)) (DPNode (MkDag 2 (bs6 h73 hdf h97 hcf h2f hcb) R0 R0 R0 (RS 262 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs6 hb9 he5 hf3 hcf h3e h79) R0 R0 R0 (RS 200 C)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h7c hf9 he7
    h9f h3f h97) R0 R0 R0 (RS 104 B)) (DPNode (MkDag 3 (bs6 h7f hcb he7 h9f h7f hcb) R0 R0 R0 (RS 4 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 7 (bs6 hf9 hfc hfe h5f he5 hff) R0 (RS 6 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 1
    (bs6 hbf hff h9e h79 he7 hcb) R0 R0 (RS 9 E) R0) (DPNode (MkDag 2 (bs6 hbf h3c hfd hcf h2f hcb) R0 R0 (RS 88 E)
    R0) (DPNode (MkDag 2 (bs6 hbf hff hdc hfe h7d hcb) R0 (RS 152 C) R0 R0) (DPNode (MkDag 9 (bs6 hf2 hfb hff hf9
    hfe h79) R0 (RS 2 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 9 (bs6 hf9 hfb h9f hcf h3f hcb) R0 (RS 5
    A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs6 h3c hfb h97 hcf he7 hcb) R0 R0 R0 (RS 120 C)) (DPNode (MkDag
    9 (bs6 h7c hfb h9f he7 hfd hcb) (RS 184 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 h9f hfb h97 hb9 hfd
    hcb) R0 R0 R0 (RS 248 C)) DPEmpty DPEmpty)))) (DPNode (MkDag 7 (bs6 h7e he7 h97 he5 hf2 hff) (RS 32 B) R0 R0
    R0) (DPNode (MkDag 4 (bs6 hff h97 hcb he7 hff hcb) (RS 47 D) R0 R0 (RS 48 B)) (DPNode (MkDag 4 (bs6 h3f h3f h9f
    hcf he7 hcb) R0 R0 R0 (RS 80 A)) (DPNode (MkDag 8 (bs6 hf9 he7 hcf hcb hff hcb) R0 (RS 144 A) R0 R0) (DPNode
    (MkDag 12 (bs6 h7c hfc hf3 hff h2f hcb) R0 R0 R0 (RS 270 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6
    hb9 he7 h97 hcf h2f h97) R0 (RS 208 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hb3 hcb hff hfe h7f h97)
    R0 (RS 112 C) R0 R0) (DPNode (MkDag 2 (bs6 hfc hfc hbc hf9 h7d hcb) R0 (RS 176 B) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs6 hf9 hfc hf3 hcf h2f h97) R0 R0 (RS 240 E) (RS 241 A)) DPEmpty DPEmpty))) (DPNode (MkDag 6
    (bs6 h7d hcb hee h79 hfd hcb) (RS 64 D) R0 R0 R0) (DPNode (MkDag 3 (bs6 he5 hf9 h7d hcf hcf hcb) R0 R0 R0 (RS
    96 C)) (DPNode (MkDag 0 (bs6 hf3 hcf h3e h5f hff hf3) R0 R0 (RS 160 E) (RS 161 C)) DPEmpty DPEmpty) (DPNode
    (MkDag 2 (bs6 hb9 hfc hbd hcf h2f hcb) R0 (RS 224 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h97 hff h9e
    h7f h3e h5e) R0 (RS 128 A) R0 R0) (DPNode (MkDag 8 (bs6 hf3 hff hcf hcb hff hcb) (RS 191 D) R0 R0 (RS 192 C))
    DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 h7e h7c hf3 hcf h2f hff) (RS 256 C) R0 R0 R0) DPEmpty DPEmpty)))).

Definition dagTree_15 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h9f hff he5 hf7 h3f h97) R0 R0 R0 (RS 281 C)) (DPNode (MkDag 1 (bs6 he7 hfc hf3 hcf h2f
    hcb) R0 R0 R0 (RS 274 A)) (DPNode (MkDag 0 (bs6 h9e hff he5 hf7 h3f h97) R0 R0 R0 (RS 280 A)) (DPNode (MkDag 3
    (bs6 hff hcb he7 h9f h7f hcb) R0 R0 (RS 167 E) (RS 168 A)) dagSub_15_48 dagSub_15_49) (DPNode (MkDag 4 (bs6 hb9
    hfc hf2 hf9 h7d hcb) R0 R0 R0 (RS 232 C)) dagSub_15_50 dagSub_15_51)) (DPNode (MkDag 2 (bs6 hbe h5f h97 hb9 hfd
    hcb) R0 (RS 278 C) R0 R0) (DPNode (MkDag 2 (bs6 hb9 h7b h9f hb9 hfd hcb) R0 R0 R0 (RS 216 C)) dagSub_15_52
    dagSub_15_53) (DPNode (MkDag 5 (bs6 h5f hfb h9f hdf hee h5e) (RS 29 B) R0 R0 R0) dagSub_15_54 dagSub_15_55))).

Definition dagTree_16 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hff hb9 h7d hff h2f) (RS 0 D) R0 (RS 77 E) (RS 78 C)) (DPNode (MkDag 0 (bs5 he7 hcb hcf
    hff h2f) R0 R0 R0 (RS 85 A)) (DPNode (MkDag 1 (bs5 h97 hcf h3c hbf h3f) R0 R0 R0 (RS 89 A)) (DPNode (MkDag 2
    (bs5 h9f hcb he7 hf7 h2f) R0 R0 R0 (RS 97 A)) (DPNode (MkDag 1 (bs5 h97 hcf hfc hbf h3f) R0 R0 R0 (RS 87 A))
    (DPNode (MkDag 4 (bs5 hf3 hff he7 hb9 he7) R0 R0 (RS 38 E) (RS 17 D)) (DPNode (MkDag 10 (bs5 h9e h7f h97 hcf
    h3c) R0 R0 R0 (RS 33 A)) (DPNode (MkDag 2 (bs5 h7f h97 he7 hf7 h2f) (RS 65 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 2 (bs5 h97 hcb he7 hf7 h2f) R0 (RS 4 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 haf hb9
    hfd hff h2f) R0 R0 (RS 21 E) R0) (DPNode (MkDag 0 (bs5 he7 hcf h2f hff h2f) R0 R0 R0 (RS 81 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs5 hff hcf he5 hf7 h2f) (RS 24 D) R0 (RS 69 E) (RS 70 C)) (DPNode (MkDag
    13 (bs5 h7f hb9 hfc hff h2f) R0 R0 R0 (RS 39 B)) (DPNode (MkDag 3 (bs5 haf hcf he7 h9f h3c) R0 R0 (RS 25 E) R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hbc hf3 hfc hbf h3f) R0 R0 (RS 57 E) R0) (DPNode (MkDag 2 (bs5
    h9f hcf he5 hf7 h2f) R0 (RS 2 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 3 (bs5 h97 hcf he7 h9f h3c)
    R0 R0 R0 (RS 90 A)) (DPNode (MkDag 0 (bs5 he5 hff hcf hff h2f) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 12 (bs5 h9f
    h9f h97 hff h2f) R0 R0 R0 (RS 15 C)) (DPNode (MkDag 1 (bs5 h7d hcf hfc hbf h3f) R0 R0 R0 (RS 67 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h7f hf3 hfc hbf h3f) R0 R0 R0 (RS 53 B)) (DPNode (MkDag 2 (bs5 h3f hcb
    he7 hf7 h2f) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 8 (bs5 h9e h5f hf3 hfb he5) R0 R0 R0
    (RS 29 C)) (DPNode (MkDag 2 (bs5 h7c hbe he7 hf7 h2f) (RS 45 E) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7d hcf hcf hff
    h2f) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 haf hbf h3c hbf h3f) R0 R0 (RS 61 E)
    R0) (DPNode (MkDag 0 (bs5 h9f hcf hcf hff h2f) R0 (RS 3 A) R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0
    (bs5 h97 hcf hcf hff h2f) R0 R0 R0 (RS 92 A)) (DPNode (MkDag 0 (bs5 h9f hcf h2f hff h2f) R0 R0 R0 (RS 95 A))
    (DPNode (MkDag 6 (bs5 hcf hfc hff hf7 h2f) R0 R0 R0 (RS 39 C)) (DPNode (MkDag 11 (bs5 h9f hcf h97 hcf h2f) R0
    R0 R0 (RS 35 A)) (DPNode (MkDag 2 (bs5 h7f hcb he7 hf7 h2f) (RS 23 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs5 h3f hb9 hfd hff h2f) R0 R0 R0 (RS 51 B)) (DPNode (MkDag 3 (bs5 hcf hcb he7 h9f h3c) R0 R0
    R0 (RS 83 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hfd hcf hcf hff h2f) R0 R0 R0 (RS 0 C)) (DPNode
    (MkDag 3 (bs5 h3f hf9 hf9 hf7 h3c) R0 R0 R0 (RS 43 A)) (DPNode (MkDag 3 (bs5 h3f hcf he7 h9f h3c) R0 R0 R0 (RS
    75 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hbc hfe he5 hf7 h2f) R0 R0 (RS 59 E) R0) (DPNode (MkDag
    3 (bs5 h9f hcf he7 h9f h3c) R0 (RS 9 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h9f hcb hcf
    hff h2f) R0 R0 R0 (RS 85 A)) (DPNode (MkDag 2 (bs5 hef h97 he7 hf7 h2f) (RS 22 D) R0 R0 (RS 64 B)) (DPNode
    (MkDag 4 (bs5 h73 hff he7 hb9 he7) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 3 (bs5 hbd hcf he7 h9f h3c) R0 R0 (RS 71
    E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 hbf hf3 he7 h9f h3c) R0 R0 (RS 55 E) R0) (DPNode (MkDag
    1 (bs5 h9f hcf h7c hbf h3f) R0 (RS 8 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 9 (bs5 h73 hcf h72 hf9
    hff) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 2 (bs5 hbc hf9 he7 hf7 h2f) R0 R0 (RS 47 E) R0) (DPNode (MkDag 2 (bs5
    hbf hcb he5 hf7 h2f) R0 R0 (RS 79 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hbf hbf h3c hbf h3f)
    R0 R0 (RS 63 E) R0) (DPNode (MkDag 0 (bs5 h97 hcf h2f hff h2f) R0 (RS 10 A) R0 R0) DPEmpty DPEmpty)
    DPEmpty))))) (DPNode (MkDag 0 (bs5 h97 hb9 h7d hff h2f) R0 R0 R0 (RS 93 A)) (DPNode (MkDag 2 (bs5 h97 hcf he5
    hf7 h2f) R0 R0 R0 (RS 88 A)) (DPNode (MkDag 2 (bs5 h97 hcf he7 hf7 h2f) R0 R0 R0 (RS 91 A)) (DPNode (MkDag 5
    (bs5 hcb hdc hff hcf h3f) R0 R0 R0 (RS 18 D)) (DPNode (MkDag 11 (bs5 h97 hcf h97 hcf h2f) R0 (RS 34 A) R0 R0)
    (DPNode (MkDag 2 (bs5 h5f hcb he7 hf7 h2f) (RS 66 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h97 hcb
    hcf hff h2f) R0 (RS 14 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbf hb9 hfd hff h2f) R0 R0 (RS 50 E)
    R0) (DPNode (MkDag 3 (bs5 h7d hcb he7 h9f h3c) (RS 82 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 3
    (bs5 h2f hcf he7 h9f h3c) R0 R0 R0 (RS 73 C)) (DPNode (MkDag 3 (bs5 hbf hf9 hf9 hf7 h3c) R0 R0 (RS 42 E) R0)
    (DPNode (MkDag 3 (bs5 hbf hcf he7 h9f h3c) R0 R0 (RS 74 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5
    h3c hf3 hfc hbf h3f) R0 R0 R0 (RS 58 C)) (DPNode (MkDag 1 (bs5 h9f hcf h3c hbf h3f) R0 (RS 12 A) R0 R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 2 (bs5 h9f hcb he5 hf7 h2f) R0 R0 R0 (RS 94 A)) (DPNode (MkDag 0 (bs5 h2f
    hb9 hfd hff h2f) R0 R0 R0 (RS 49 C)) (DPNode (MkDag 4 (bs5 h73 hdf he7 hb9 he7) R0 R0 R0 (RS 15 B)) (DPNode
    (MkDag 2 (bs5 h7f hcf he5 hf7 h2f) R0 R0 R0 (RS 24 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hff hf3
    hfc hbf h3f) R0 R0 R0 (RS 54 C)) (DPNode (MkDag 0 (bs5 h9e h79 h7d hff h2f) R0 (RS 11 A) R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 9 (bs5 hf3 hcf h72 hf9 hff) R0 R0 (RS 30 E) (RS 31 A)) (DPNode (MkDag 0 (bs5
    h65 hff hcf hff h2f) R0 R0 R0 (RS 20 B)) (DPNode (MkDag 0 (bs5 h7f hb9 h7d hff h2f) R0 R0 R0 (RS 0 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h2f hbf h3c hbf h3f) R0 R0 R0 (RS 62 C)) (DPNode (MkDag 0 (bs5 h9f hb9
    h7d hff h2f) R0 (RS 13 A) R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 3 (bs5 h9f hcb he7 h9f h3c) R0 R0
    R0 (RS 96 A)) (DPNode (MkDag 1 (bs5 h97 hcf h7c hbf h3f) R0 R0 R0 (RS 86 A)) (DPNode (MkDag 0 (bs5 hff hff h2f
    hff h2f) (RS 19 D) R0 R0 (RS 44 B)) (DPNode (MkDag 12 (bs5 h97 h9f h97 hff h2f) R0 (RS 36 A) R0 R0) (DPNode
    (MkDag 1 (bs5 hfd hcf hfc hbf h3f) R0 R0 (RS 68 E) (RS 24 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5
    hef hf3 hfc hbf h3f) R0 R0 R0 (RS 52 B)) (DPNode (MkDag 2 (bs5 hbf hcb he7 hf7 h2f) R0 R0 (RS 84 E) R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 7 (bs5 h9f hcb hee h5e h7e) R0 (RS 28 A) R0 R0) (DPNode (MkDag 0 (bs5 hbf hff
    h2f hff h2f) R0 (RS 19 C) R0 R0) (DPNode (MkDag 2 (bs5 he7 hcf he7 hf7 h2f) R0 R0 R0 (RS 76 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 h3c hfe he5 hf7 h2f) R0 R0 R0 (RS 60 C)) (DPNode (MkDag 2 (bs5 h9f hcf
    he7 hf7 h2f) R0 (RS 6 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 4 (bs5 hf3 hdf he7 hb9 he7) R0 R0
    (RS 37 E) (RS 16 C)) (DPNode (MkDag 0 (bs5 h7e h79 h7d hff h2f) (RS 67 C) R0 R0 R0) (DPNode (MkDag 13 (bs5 hff
    hb9 hfc hff h2f) R0 R0 (RS 40 E) (RS 41 C)) (DPNode (MkDag 3 (bs5 h3d hcf he7 h9f h3c) R0 R0 R0 (RS 72 C))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h3f hf3 he7 h9f h3c) R0 R0 R0 (RS 56 C)) (DPNode (MkDag 1 (bs5
    h9f hcf hfc hbf h3f) R0 (RS 5 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 10 (bs5 h9e h7b h97 hcf h3c)
    R0 (RS 32 A) R0 R0) (DPNode (MkDag 2 (bs5 h3c hf9 he7 hf7 h2f) R0 R0 R0 (RS 48 C)) (DPNode (MkDag 2 (bs5 h3f
    hcb he5 hf7 h2f) R0 R0 R0 (RS 80 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h3f hbf h3c hbf h3f) R0 R0
    R0 (RS 22 B)) (DPNode (MkDag 3 (bs5 h97 hcb he7 h9f h3c) R0 (RS 7 A) R0 R0) DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_17 : DagNTree :=
  MkDagNTree (MkDag 0 (bs2 h7c hf3) (RS 1 B) R0 R0 R0) (DPNode (MkDag 1 (bs2 h5e h79) (RS 2 B) R0 R0 R0) (DPNode
    (MkDag 1 (bs2 h7e h79) (RS 3 B) R0 R0 R0) (DPNode (MkDag 3 (bs2 h79 he7) (RS 5 B) R0 R0 R0) (DPNode (MkDag 7
    (bs2 h79 he7) (RS 9 B) R0 R0 R0) (DPNode (MkDag 15 (bs2 hcb he5) R0 R0 R0 (RS 17 D)) (DPNode (MkDag 25 (bs2 hbf
    hcf) R0 R0 (RS 33 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 20 (bs2 hb9 h7b) R0 (RS 25 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 11 (bs2 h79 he7) (RS 13 B) R0 R0 R0) (DPNode (MkDag 18 (bs2 hf9 he7) R0 (RS 21 A) R0
    R0) DPEmpty DPEmpty) (DPNode (MkDag 22 (bs2 he7 hcb) R0 R0 R0 (RS 29 B)) DPEmpty DPEmpty))) (DPNode (MkDag 5
    (bs2 h79 he7) (RS 7 B) R0 R0 R0) (DPNode (MkDag 9 (bs2 h79 he7) (RS 11 B) R0 R0 R0) (DPNode (MkDag 17 (bs2 hcf
    h2f) R0 R0 R0 (RS 19 A)) (DPNode (MkDag 26 (bs2 he7 hb9) R0 R0 R0 (RS 35 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 21 (bs2 hbf hf7) R0 R0 (RS 27 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs2 h79 he7) (RS 15 B) R0 R0
    R0) (DPNode (MkDag 19 (bs2 hf9 h7d) R0 R0 (RS 23 E) (RS 24 A)) DPEmpty DPEmpty) (DPNode (MkDag 24 (bs2 h7d hcb)
    (RS 31 D) R0 R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs2 h79 he7) (RS 4 B) R0 R0 R0) (DPNode (MkDag 4 (bs2
    h79 he7) (RS 6 B) R0 R0 R0) (DPNode (MkDag 8 (bs2 h79 he7) (RS 10 B) R0 R0 R0) (DPNode (MkDag 16 (bs2 hcb he5)
    R0 R0 R0 (RS 18 D)) (DPNode (MkDag 25 (bs2 h3f hcf) R0 R0 R0 (RS 34 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 20 (bs2 hf9 h7b) (RS 25 D) R0 R0 (RS 26 C)) DPEmpty DPEmpty)) (DPNode (MkDag 12 (bs2 h79 he7) (RS 14 B)
    R0 R0 R0) (DPNode (MkDag 19 (bs2 hb9 h7d) R0 R0 R0 (RS 22 C)) DPEmpty DPEmpty) (DPNode (MkDag 23 (bs2 he7 hfe)
    (RS 29 D) R0 R0 (RS 30 B)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs2 h79 he7) (RS 8 B) R0 R0 R0) (DPNode (MkDag
    10 (bs2 h79 he7) (RS 12 B) R0 R0 R0) (DPNode (MkDag 18 (bs2 hb9 he7) R0 (RS 20 C) R0 R0) (DPNode (MkDag 26 (bs2
    he7 hf9) (RS 35 D) R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 21 (bs2 h3f hf7) R0 R0 R0 (RS 28
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 14 (bs2 h79 he7) (RS 3 B) R0 R0 R0) (DPNode (MkDag 19 (bs2 h79 h7d) R0 R0
    R0 (RS 22 B)) DPEmpty DPEmpty) (DPNode (MkDag 24 (bs2 hcf hcb) R0 R0 R0 (RS 32 C)) DPEmpty DPEmpty))))).

Definition dagTree_18 : DagNTree :=
  MkDagNTree (MkDag 0 nil (RS 0 B) R0 R0 R0) DPEmpty.

Definition dagSub_19_56 : DagPTree :=
  DPNode (MkDag 0 (bs5 h7f he7 h9e h5f hfe) (RS 69 D) R0 R0 (RS 67 B)) (DPNode (MkDag 0 (bs5 hbf he7 h97 hf9 h7e)
    R0 R0 R0 (RS 47 C)) (DPNode (MkDag 0 (bs5 h7e he7 h97 hf9 h7e) (RS 8 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hbe he7
    h97 hf9 h7e) R0 (RS 65 C) R0 R0) (DPNode (MkDag 0 (bs5 hff he7 h9f hcf h3e) R0 R0 (RS 126 E) (RS 183 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h5e he7 h97 hf9 h7e) (RS 32 B) R0 R0 R0) (DPNode (MkDag 0 (bs5
    hbe he5 hf2 hfb hfe) R0 (RS 161 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hcb he5 hf2 hfb hfe)
    R0 R0 R0 (RS 114 D)) (DPNode (MkDag 0 (bs5 h9f he7 h9e h79 h7e) R0 (RS 81 C) R0 R0) (DPNode (MkDag 0 (bs5 hb9
    hfc hf3 hcf h3e) R0 (RS 41 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hcb he7 h9f hcf hee) R0 R0
    R0 (RS 113 D)) (DPNode (MkDag 0 (bs5 hb9 he7 h9f hcf hee) R0 (RS 177 C) R0 R0) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 0 (bs5 hcb he7 h9e h79 h7e) R0 R0 R0 (RS 112 D)) (DPNode (MkDag 0 (bs5 hcb he7 h97 hcf hee) R0
    R0 R0 (RS 116 B)) (DPNode (MkDag 0 (bs5 h7f he7 h9f h9f hfe) (RS 73 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf he7
    h9e h5f hfe) R0 R0 R0 (RS 22 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 he7 he7 hf3 hcf h3e) (RS 104
    D) R0 R0 (RS 105 A)) (DPNode (MkDag 0 (bs5 hf9 he7 h9f h9f hfe) (RS 168 D) (RS 21 A) R0 (RS 21 A)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 he7 hfc hf3 hcf h3e) (RS 56 D) R0 R0 (RS 57 A)) (DPNode (MkDag 0 (bs5
    h97 he7 h9e h5f hfe) R0 R0 R0 (RS 89 A)) (DPNode (MkDag 0 (bs5 h9e he7 h97 hcf h3e) R0 (RS 19 A) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7 h9e h79 h7e) (RS 55 B) R0 R0 (RS 5 B)) (DPNode (MkDag 0 (bs5
    h97 he7 hf3 hcf h3e) R0 R0 R0 (RS 185 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_57 : DagPTree :=
  DPNode (MkDag 0 (bs5 h7f h3c hf3 hcf h3e) (RS 124 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcb he7 hf2 hfb hfe) R0 R0
    R0 (RS 52 D)) (DPNode (MkDag 0 (bs5 hf9 he5 hf3 hcf h3e) (RS 36 D) (RS 147 A) R0 (RS 147 A)) (DPNode (MkDag 0
    (bs5 h7f he7 h9e hf9 h7e) (RS 70 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf he7 h9e h79 h7e) R0 R0 R0 (RS 133 D))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbe he7 hf3 hcf h3e) R0 (RS 102 C) (RS 103 E) R0) (DPNode
    (MkDag 0 (bs5 h9f he7 h97 hcf hee) R0 (RS 165 B) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hcb
    he7 h97 hcb hee) R0 R0 R0 (RS 27 D)) (DPNode (MkDag 0 (bs5 hbf he5 hf2 hfb hfe) R0 R0 R0 (RS 85 C)) (DPNode
    (MkDag 0 (bs5 h9f h3c hf3 hcf h3e) R0 (RS 11 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7
    h9e hf9 h7e) (RS 53 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79 he5 hf2 hfb hfe) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs5 hfe he7 h9f hcb hee) R0 (RS 182 A) R0 R0) (DPNode (MkDag 0 (bs5 hff he7 hf2
    hfb hfe) R0 R0 (RS 25 E) (RS 152 A)) (DPNode (MkDag 0 (bs5 h5e he7 h97 h9f hfe) (RS 77 B) R0 R0 R0) (DPNode
    (MkDag 0 (bs5 hb9 he7 hf3 hcf h3e) R0 (RS 23 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3e he7
    h97 hcf h3e) R0 R0 R0 (RS 154 B)) (DPNode (MkDag 0 (bs5 hf9 he7 h97 hcf h3e) (RS 172 D) (RS 18 A) R0 (RS 18 A))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h3e he7 h9f hcf hee) R0 R0 R0 (RS 61 B)) (DPNode (MkDag 0 (bs5
    h5f he7 h9f hf9 h7e) (RS 93 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h9e he7 h9f hcf hee) R0 (RS 157 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h5e he7 h9f hcb hee) (RS 125 B) R0 R0 R0) (DPNode (MkDag 0 (bs5
    hff he7 h97 hcf h3e) R0 R0 (RS 189 E) (RS 190 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_58 : DagPTree :=
  DPNode (MkDag 0 (bs5 hcb he7 h9f hcb hee) (RS 10 D) R0 R0 (RS 51 D)) (DPNode (MkDag 0 (bs5 hb9 h7c hf3 hcf h3e)
    R0 (RS 37 C) R0 (RS 37 C)) (DPNode (MkDag 0 (bs5 h7b he7 h9f hf9 h7e) (RS 92 B) R0 R0 R0) (DPNode (MkDag 0 (bs5
    hbf he7 h9e h5f hfe) R0 R0 R0 (RS 67 C)) (DPNode (MkDag 0 (bs5 h5e he7 h97 hcf h3e) (RS 131 B) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h97 he7 h9f hcf h3e) R0 (RS 54 A) R0 (RS 54 A)) (DPNode (MkDag
    0 (bs5 h7f he7 h97 hf9 h7e) R0 R0 R0 (RS 47 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 he7 h9f
    hf9 h7e) (RS 50 D) R0 (RS 175 E) (RS 176 A)) (DPNode (MkDag 0 (bs5 hbe he5 hf3 hcf h3e) R0 (RS 83 C) R0 R0)
    (DPNode (MkDag 0 (bs5 hb9 he5 hf3 hcf h3e) R0 (RS 36 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5
    hcb he7 h97 hf9 h7e) R0 R0 R0 (RS 115 D)) (DPNode (MkDag 0 (bs5 hb9 he5 hf2 hfb hfe) R0 (RS 4 C) R0 (RS 4 C))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hbf he7 h97 h9f hfe) R0 R0 R0 (RS 109 C)) (DPNode (MkDag 0
    (bs5 hf3 he7 h97 h9f hfe) R0 (RS 17 C) R0 R0) (DPNode (MkDag 0 (bs5 h7e he7 hf2 hfb hfe) (RS 75 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 hf9 he7 h9e hf9 h7e) (RS 138 D) R0 R0 (RS 139 A)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs5 hbe he7 h97 hcf h3e) R0 (RS 107 C) (RS 108 E) R0) (DPNode (MkDag 0 (bs5 h79 he7 hf2 hfb hfe) R0
    R0 R0 (RS 169 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf3 he7 h9e h79 h7e) (RS 58 D) R0 R0 (RS 59
    C)) (DPNode (MkDag 0 (bs5 hf3 he7 h97 hcf hee) R0 (RS 10 D) R0 R0) (DPNode (MkDag 0 (bs5 he7 he7 h97 hcf h3e)
    R0 R0 R0 (RS 155 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7 h97 hcf hee) (RS 123 B) R0 R0 (RS
    1 B)) (DPNode (MkDag 0 (bs5 hbe he7 h97 hcb hee) R0 (RS 29 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_59 : DagPTree :=
  DPNode (MkDag 0 (bs5 hcb he7 h9e hf9 h7e) (RS 14 D) R0 R0 (RS 10 D)) (DPNode (MkDag 0 (bs5 hcf he7 h97 hcf hee)
    R0 R0 R0 (RS 137 A)) (DPNode (MkDag 0 (bs5 hcb he7 hf3 hcf h3e) R0 R0 R0 (RS 20 D)) (DPNode (MkDag 0 (bs5 h5e
    he7 h9f hcf h3e) (RS 71 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf he5 hf3 hcf h3e) R0 R0 R0 (RS 135 D)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfe he7 hf3 hcf h3e) R0 (RS 45 A) R0 R0) (DPNode (MkDag 0 (bs5 hf9 he7
    h9f hcb hee) (RS 166 D) R0 R0 (RS 167 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f he7 h9f hcf h3e)
    R0 (RS 99 C) R0 (RS 99 C)) (DPNode (MkDag 0 (bs5 h7f he5 hf2 hfb hfe) R0 R0 R0 (RS 85 B)) (DPNode (MkDag 0 (bs5
    h3e he7 h9f hcb hee) R0 R0 R0 (RS 151 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7 h97 hcb hee)
    (RS 119 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hbf he7 h9f hcf h3e) R0 R0 R0 (RS 128 C)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs5 hcf he7 h97 hf9 h7e) R0 R0 R0 (RS 136 D)) (DPNode (MkDag 0 (bs5 hf3 he7 hf2
    hfb hfe) R0 (RS 186 C) R0 R0) (DPNode (MkDag 0 (bs5 h67 he7 h9f hf9 h7e) R0 R0 R0 (RS 79 B)) (DPNode (MkDag 0
    (bs5 hb9 he7 h97 h9f hfe) R0 (RS 143 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7f he7 h97 h9f
    hfe) (RS 111 D) R0 R0 (RS 109 B)) (DPNode (MkDag 0 (bs5 h79 h7c hf3 hcf h3e) R0 R0 R0 (RS 37 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f he5 hf3 hcf h3e) R0 (RS 63 C) R0 R0) (DPNode (MkDag 0 (bs5 hff he7
    h9f hf9 h7e) (RS 94 D) R0 R0 (RS 156 A)) (DPNode (MkDag 0 (bs5 h9f he7 h9f hcf hee) R0 (RS 159 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7f he7 h9f hcf h3e) (RS 127 B) R0 R0 (RS 128 B)) (DPNode
    (MkDag 0 (bs5 h9e h7c hf3 hcf h3e) R0 (RS 120 B) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_60 : DagPTree :=
  DPNode (MkDag 0 (bs5 h9e he7 h9f hcf h3e) R0 (RS 98 A) R0 (RS 98 A)) (DPNode (MkDag 0 (bs5 hbe h7c hf3 hcf h3e)
    R0 (RS 13 C) R0 R0) (DPNode (MkDag 0 (bs5 hf3 he7 h97 hcb hee) (RS 33 D) (RS 106 C) R0 (RS 106 C)) (DPNode
    (MkDag 0 (bs5 hfe he7 h97 hf9 h7e) R0 (RS 66 A) R0 R0) (DPNode (MkDag 0 (bs5 h7e he7 hf3 hcf h3e) (RS 25 B) R0
    R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbf he7 h9e hf9 h7e) R0 (RS 6 C) R0 R0) (DPNode (MkDag 0
    (bs5 hfe he5 hf2 hfb hfe) R0 (RS 16 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 he7 h97 hf9
    h7e) (RS 49 D) (RS 0 A) (RS 121 E) (RS 0 A)) (DPNode (MkDag 0 (bs5 hf3 he7 h9f hcf hee) R0 (RS 82 C) R0 R0)
    (DPNode (MkDag 0 (bs5 hb9 he7 h9e h79 h7e) R0 (RS 5 C) R0 (RS 5 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs5 hcb he5 hf3 hcf h3e) R0 R0 R0 (RS 48 D)) (DPNode (MkDag 0 (bs5 hf9 he7 h9f hcf hee) (RS 177 D) (RS 178 A)
    R0 (RS 178 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h7f he7 hf2 hfb hfe) (RS 130 B) R0 R0 (RS 44
    B)) (DPNode (MkDag 0 (bs5 hf9 hfc hf3 hcf h3e) (RS 41 D) R0 R0 (RS 145 A)) (DPNode (MkDag 0 (bs5 h5e he7 hf2
    hfb hfe) (RS 74 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hb9 he7 h9e hf9 h7e) R0 (RS 138 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 h9f he7 hf2 hfb hfe) R0 (RS 33 C) R0 R0) (DPNode (MkDag 0 (bs5 hf9 he7 hf2 hfb
    hfe) (RS 169 D) R0 (RS 170 E) (RS 171 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f he7 h9f hf9 h7e)
    R0 (RS 58 C) R0 R0) (DPNode (MkDag 0 (bs5 h9f he7 h9e h5f hfe) R0 (RS 90 C) R0 R0) (DPNode (MkDag 0 (bs5 h9f
    he7 h97 hcf h3e) R0 (RS 42 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7 h97 hf9 h7e) (RS
    122 B) R0 R0 (RS 49 B)) (DPNode (MkDag 0 (bs5 h9f he7 hf3 hcf h3e) R0 (RS 46 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_19_61 : DagPTree :=
  DPNode (MkDag 0 (bs5 hfe h7c hf3 hcf h3e) R0 (RS 145 A) R0 R0) (DPNode (MkDag 0 (bs5 hb9 he7 hf2 hfb hfe) R0 (RS
    169 C) R0 (RS 169 C)) (DPNode (MkDag 0 (bs5 hf9 h7c hf3 hcf h3e) (RS 37 D) (RS 173 A) (RS 174 E) (RS 173 A))
    (DPNode (MkDag 0 (bs5 hdf he7 h9e hf9 h7e) R0 R0 R0 (RS 97 A)) (DPNode (MkDag 0 (bs5 hcf he7 h9f hcf hee) R0 R0
    R0 (RS 134 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h73 he7 h9f h9f hfe) R0 R0 R0 (RS 99 B)) (DPNode
    (MkDag 0 (bs5 h79 he7 h9f hcb hee) R0 R0 R0 (RS 166 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h79
    he7 h9f hcf h3e) (RS 117 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hff he5 hf2 hfb hfe) R0 R0 (RS 86 E) (RS 87 A))
    (DPNode (MkDag 0 (bs5 hbe he7 h9f hcb hee) R0 (RS 28 C) (RS 150 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    0 (bs5 h79 he7 hf3 hcf h3e) (RS 118 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79 he7 h9e h5f hfe) R0 R0 R0 (RS 2 B))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hfe he7 h97 hcb hee) R0 (RS 187 A) R0 R0) (DPNode (MkDag 0
    (bs5 hbf he7 hf2 hfb hfe) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 0 (bs5 h7e he7 h97 h9f hfe) (RS 78 E) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 hb9 he7 h97 hcb hee) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5
    hff he7 h97 h9f hfe) R0 R0 (RS 110 E) (RS 24 D)) (DPNode (MkDag 0 (bs5 hb9 he7 h9f hf9 h7e) R0 (RS 50 C) R0 (RS
    50 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 he7 he7 h9f hcf hee) R0 R0 R0 (RS 62 A)) (DPNode (MkDag
    0 (bs5 h7f he7 h9f hf9 h7e) (RS 15 B) R0 R0 (RS 94 B)) (DPNode (MkDag 0 (bs5 h97 he7 h9f hcf hee) R0 R0 R0 (RS
    158 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7e he7 h9f hcb hee) (RS 126 B) R0 R0 R0) (DPNode
    (MkDag 0 (bs5 h7f he7 h97 hcf h3e) R0 R0 R0 (RS 188 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_62 : DagPTree :=
  DPNode (MkDag 0 (bs5 hf3 he7 h9e hf9 h7e) (RS 11 D) (RS 149 C) R0 (RS 149 C)) (DPNode (MkDag 0 (bs5 h97 he7 h97
    hcf h3e) R0 R0 R0 (RS 153 A)) (DPNode (MkDag 0 (bs5 h79 hfc hf3 hcf h3e) (RS 120 B) R0 R0 R0) (DPNode (MkDag 0
    (bs5 hff he7 h9e h5f hfe) R0 R0 (RS 8 E) (RS 68 B)) (DPNode (MkDag 0 (bs5 h7e he7 h97 hcf h3e) (RS 110 B) R0 R0
    R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hf3 he7 h9f h9f hfe) (RS 99 D) (RS 100 C) (RS 101 E) (RS
    100 C)) (DPNode (MkDag 0 (bs5 h9e he7 h97 hcf hee) R0 (RS 43 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs5 hcb he7 h9f hcf h3e) R0 R0 R0 (RS 91 D)) (DPNode (MkDag 0 (bs5 hfe he5 hf3 hcf h3e) R0 (RS 84 A)
    R0 R0) (DPNode (MkDag 0 (bs5 hb9 he7 h97 hf9 h7e) R0 (RS 49 C) R0 (RS 49 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs5 hcb he7 h9e h5f hfe) R0 R0 R0 (RS 40 D)) (DPNode (MkDag 0 (bs5 hb9 he7 h9e h5f hfe) R0 (RS 2 C)
    R0 (RS 2 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hcb he7 h97 hcf h3e) R0 R0 R0 (RS 31 D)) (DPNode
    (MkDag 0 (bs5 h97 he7 h97 hcf hee) R0 R0 R0 (RS 164 A)) (DPNode (MkDag 0 (bs5 h7f he7 h97 hcb hee) (RS 76 B) R0
    R0 R0) (DPNode (MkDag 0 (bs5 hb9 he7 h9f hcf h3e) R0 (RS 7 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs5 hfe he7 h97 hcf h3e) R0 (RS 26 A) R0 R0) (DPNode (MkDag 0 (bs5 hb9 he7 h97 hcf h3e) R0 (RS 172 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hbe he7 h9f hcf hee) R0 R0 (RS 60 E) R0) (DPNode (MkDag 0 (bs5
    hcb he7 h9f h9f hfe) R0 R0 R0 (RS 38 D)) (DPNode (MkDag 0 (bs5 h9f he7 h97 h9f hfe) R0 (RS 93 B) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hcf h3e) (RS 12 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hbf he7
    h97 hcf h3e) R0 R0 R0 (RS 188 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_19_63 : DagPTree :=
  DPNode (MkDag 0 (bs5 h5e he7 h9f hcf hee) (RS 39 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf9 he7 hf3 hcf h3e) (RS 23
    D) R0 R0 (RS 141 A)) (DPNode (MkDag 0 (bs5 h7e he7 h9f hcf hee) (RS 95 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7e
    he7 h9f hcf h3e) (RS 72 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf he5 hf2 hfb hfe) R0 R0 R0 (RS 30 D)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3e he7 hf3 hcf h3e) R0 R0 R0 (RS 104 B)) (DPNode (MkDag 0 (bs5 hb9 he7
    h9f h9f hfe) R0 (RS 168 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h79 he5 hf3 hcf h3e) (RS 121
    B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h9e he7 h9e h5f hfe) R0 (RS 88 A) R0 R0) (DPNode (MkDag 0 (bs5 he7 he7 h9f
    hcb hee) R0 R0 R0 (RS 54 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h79 he7 h97 h9f hfe) (RS 35 B) R0
    R0 R0) (DPNode (MkDag 0 (bs5 h9e he7 hf3 hcf h3e) R0 (RS 184 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 0 (bs5 hcb he7 h97 h9f hfe) R0 R0 R0 (RS 34 B)) (DPNode (MkDag 0 (bs5 hff he7 h97 hf9 h7e) R0 R0 (RS 162
    E) (RS 163 A)) (DPNode (MkDag 0 (bs5 he7 he7 h9f hf9 h7e) R0 R0 R0 (RS 80 A)) (DPNode (MkDag 0 (bs5 hf9 he7 h97
    h9f hfe) (RS 143 D) R0 R0 (RS 144 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hcf he7 h9f hf9 h7e) R0
    R0 R0 (RS 132 D)) (DPNode (MkDag 0 (bs5 h79 he7 h9f hf9 h7e) R0 R0 R0 (RS 50 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs5 hf3 he5 hf2 hfb hfe) R0 (RS 64 C) R0 R0) (DPNode (MkDag 0 (bs5 h7f he5 hf3 hcf h3e) (RS
    96 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf3 he5 hf3 hcf h3e) R0 (RS 160 C) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs5 h5e he7 hf3 hcf h3e) (RS 129 B) R0 R0 R0) DPEmpty DPEmpty))).

Definition dagTree_19 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hb9 he7 h97 hcf hee) R0 (RS 1 C) R0 (RS 1 C)) (DPNode (MkDag 0 (bs5 hf9 he7 h97 hcf hee)
    (RS 1 D) R0 (RS 122 E) (RS 148 A)) (DPNode (MkDag 0 (bs5 hf9 he7 h9e h5f hfe) (RS 2 D) (RS 14 D) (RS 181 E) (RS
    14 D)) (DPNode (MkDag 0 (bs5 hf9 he5 hf2 hfb hfe) (RS 4 D) (RS 179 A) (RS 180 E) (RS 179 A)) dagSub_19_56
    dagSub_19_57) (DPNode (MkDag 0 (bs5 hff he7 h9e hf9 h7e) (RS 6 D) (RS 9 A) R0 (RS 9 A)) dagSub_19_58
    dagSub_19_59)) (DPNode (MkDag 0 (bs5 hf9 he7 h97 hcb hee) (RS 3 D) R0 R0 (RS 142 A)) (DPNode (MkDag 0 (bs5 hf9
    he7 h9e h79 h7e) (RS 5 D) R0 (RS 120 E) (RS 146 A)) dagSub_19_60 dagSub_19_61) (DPNode (MkDag 0 (bs5 hf9 he7
    h9f hcf h3e) (RS 7 D) R0 R0 (RS 140 A)) dagSub_19_62 dagSub_19_63))).

Definition dagSub_20_64 : DagPTree :=
  DPNode (MkDag 6 (bs5 hf9 hfc hfd hcb hf3) (RS 8 D) (RS 200 A) R0 (RS 200 A)) (DPNode (MkDag 13 (bs5 hf9 hfc hbe
    h79 hfc) (RS 16 D) (RS 171 A) R0 (RS 171 A)) (DPNode (MkDag 22 (bs5 hf9 h7c hf3 hf3 hf3) R0 R0 (RS 160 E) (RS
    161 A)) (DPNode (MkDag 38 (bs5 h9f hff h73 hfb h9f) R0 (RS 65 C) R0 R0) (DPNode (MkDag 24 (bs5 h79 hfc hbe h7e
    h7d) R0 R0 R0 (RS 29 B)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs5 hb9 hff he7 hff h9f) R0 (RS 23 C) R0 (RS 23
    C)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 h3f hcb hee h5f h72) R0 R0 R0 (RS 97 B)) (DPNode (MkDag 22 (bs5 h79
    h7c hf3 hf3 hf3) R0 R0 R0 (RS 32 B)) DPEmpty DPEmpty) (DPNode (MkDag 33 (bs5 h3f hff h2f hcb hef) R0 R0 R0 (RS
    225 C)) DPEmpty DPEmpty))) (DPNode (MkDag 22 (bs5 h3e hff h73 hf3 hf3) R0 R0 R0 (RS 49 B)) (DPNode (MkDag 41
    (bs5 hf7 h3f hb9 h79 hf3) (RS 80 D) R0 R0 (RS 81 C)) (DPNode (MkDag 5 (bs5 hbe h5f hfe h79 hf9) R0 (RS 7 C) R0
    R0) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs5 hcf h3c hbd hcf hf3) R0 R0 R0 (RS 209 D)) DPEmpty DPEmpty)) (DPNode
    (MkDag 19 (bs5 hbf hff h3f hb9 h7f) R0 R0 (RS 113 E) R0) (DPNode (MkDag 11 (bs5 hb9 hfc hbe h5e h7f) R0 (RS 177
    C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 21 (bs5 hbf h3f h9e he7 h97) R0 (RS 100 C) R0 (RS 100 C))
    (DPNode (MkDag 34 (bs5 hcb hfc hbe h7f h3e) R0 R0 R0 (RS 41 D)) (DPNode (MkDag 39 (bs5 h9f hcf h9e h7b h9e) R0
    R0 R0 (RS 73 A)) (DPNode (MkDag 49 (bs5 hcf h3c hfe h7f h3c) R0 R0 R0 (RS 137 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 33 (bs5 hb9 hfc hfd hcf hef) R0 (RS 39 C) R0 (RS 39 C)) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 h3f h3f
    h3e he7 h9f) R0 R0 R0 (RS 216 A)) (DPNode (MkDag 19 (bs5 hb9 hfc hbe h79 he7) R0 R0 R0 (RS 22 C)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h97 hf9 h7e h5f h3f) R0 (RS 57 A) R0 R0) (DPNode (MkDag 0 (bs5 h73 hdf
    hf3 hcf h3f) R0 R0 R0 (RS 0 B)) (DPNode (MkDag 52 (bs5 h9f he7 hf3 hcb hf3) R0 (RS 153 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 27 (bs5 hbf hff he7 he7 h9f) R0 (RS 217 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 39
    (bs5 hb9 hff h97 h9f h9e) R0 R0 R0 (RS 121 C)) (DPNode (MkDag 54 (bs5 hb9 he7 h9e h5f h2f) R0 (RS 186 C) R0 (RS
    186 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_65 : DagPTree :=
  DPNode (MkDag 4 (bs5 h9e h7c hff hf9 he5) R0 R0 R0 (RS 71 A)) (DPNode (MkDag 17 (bs5 hff h9e h7f hf9 h7c) R0 R0
    (RS 219 E) (RS 220 C)) (DPNode (MkDag 30 (bs5 hcf h3f h72 hf9 hf3) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 32 (bs5
    hfe h7c hfe hff h9e) R0 (RS 69 C) R0 R0) (DPNode (MkDag 25 (bs5 hf9 he7 h97 hcf hee) R0 (RS 133 A) (RS 134 E)
    (RS 133 A)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5 h79 hfc hf3 hfb h9e) R0 R0 R0 (RS 195 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 21 (bs5 hff h3f h9e he7 h97) (RS 100 D) R0 (RS 101 E) (RS 102 A)) (DPNode (MkDag 23 (bs5 h79 h7c
    hfe h7f h73) R0 R0 R0 (RS 163 B)) DPEmpty DPEmpty) (DPNode (MkDag 9 (bs5 hbf hfc hf3 hfb h9f) R0 (RS 11 C) R0
    R0) DPEmpty DPEmpty))) (DPNode (MkDag 36 (bs5 h9f h9f h9e h7f h73) R0 (RS 53 C) R0 R0) (DPNode (MkDag 5 (bs5
    hff h3f h3f hf3 hf3) (RS 84 D) R0 R0 (RS 85 A)) (DPNode (MkDag 33 (bs5 h7d hcf he7 hcf h3f) R0 R0 R0 (RS 149
    B)) DPEmpty DPEmpty) (DPNode (MkDag 42 (bs5 he7 hcb hf2 hf9 h7c) R0 R0 R0 (RS 86 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 29 (bs5 h7f hee h7f hff h3c) (RS 28 D) R0 R0 R0) (DPNode (MkDag 4 (bs5 hb9 he7 hf3 hcf h72) R0 (RS 4 C)
    R0 (RS 4 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hcf hfc hfc hbf h2f) R0 R0 R0 (RS 117 D))
    (DPNode (MkDag 35 (bs5 h73 hcf hf2 hf3 hee) R0 R0 R0 (RS 43 B)) (DPNode (MkDag 22 (bs5 hdf h3c hbe h7f hf3) R0
    R0 R0 (RS 77 A)) (DPNode (MkDag 35 (bs5 hff hb9 h7f hf3 hee) R0 R0 (RS 141 E) (RS 30 D)) DPEmpty DPEmpty)
    (DPNode (MkDag 4 (bs5 h79 hfc hff hf9 he5) R0 R0 R0 (RS 203 B)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs5 hbd
    hff h3f hb9 h7f) R0 R0 (RS 109 E) R0) (DPNode (MkDag 49 (bs5 hf9 hfc hbe h5f h3c) R0 (RS 173 A) (RS 174 E) (RS
    173 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs5 h79 hff hf2 hf3 hf3) (RS 61 B) R0 R0 R0) (DPNode
    (MkDag 37 (bs5 h9f hdf h9f hdf hf2) R0 (RS 93 C) R0 (RS 93 C)) (DPNode (MkDag 53 (bs5 h97 hdf hf3 hf9 hfe) R0
    R0 R0 (RS 157 A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hbe h5f h3f hfe h7f) R0 R0 (RS 221 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 9 (bs5 hf9 hfc hf3 hfb h9f) (RS 124 D) R0 R0 (RS 125 A)) (DPNode (MkDag 10 (bs5 hb9
    h7b h9f h9f h9f) R0 (RS 189 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_66 : DagPTree :=
  DPNode (MkDag 8 (bs5 hb9 hfb h97 hcf h9e) R0 (RS 205 C) R0 (RS 205 C)) (DPNode (MkDag 15 (bs5 hb9 hfc hf3 hfb
    h9e) R0 (RS 195 C) R0 (RS 195 C)) (DPNode (MkDag 28 (bs5 hee h5e h7c hbc hfc) R0 R0 R0 (RS 222 B)) (DPNode
    (MkDag 15 (bs5 hf3 hfc hf3 hfb h9e) R0 (RS 67 C) R0 R0) (DPNode (MkDag 48 (bs5 hf9 hfc hbf hff hcf) (RS 130 D)
    (RS 131 A) R0 (RS 131 A)) DPEmpty DPEmpty) (DPNode (MkDag 20 (bs5 h79 hff he7 hff h9f) R0 R0 R0 (RS 23 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 38 (bs5 h7e h5f hf3 hcb hf3) (RS 37 C) R0 R0 R0) (DPNode (MkDag 7 (bs5 hf9 h7c
    hfe h79 hf3) R0 (RS 26 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 39 (bs5 hbc hbf h97 h9f h9e) R0 R0 (RS 227 E)
    R0) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs5 h9f hcf hfc hff hf3) R0 (RS 51 A) R0 R0) (DPNode (MkDag 41 (bs5
    h3f h3f hb9 h79 hf3) R0 R0 R0 (RS 83 A)) (DPNode (MkDag 0 (bs5 h3e h79 h7e h7f h3f) R0 R0 R0 (RS 147 B))
    DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hbf hfe h7e h5f h73) R0 R0 (RS 211 E) R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 46 (bs5 hb2 hf3 he7 hfe h7c) R0 (RS 115 C) R0 R0) (DPNode (MkDag 16 (bs5 hb9 hfc hf3 hcf h3f) R0 (RS 179
    C) R0 (RS 179 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 23 (bs5 hb9 h7c hfe h7f h73) R0 R0 R0 (RS 163 C))
    (DPNode (MkDag 6 (bs5 hcf hfc hff h9f hfc) R0 R0 R0 (RS 43 C)) (DPNode (MkDag 8 (bs5 h9f h9f h97 hcf h9e) R0 R0
    R0 (RS 75 B)) (DPNode (MkDag 51 (bs5 h79 he5 hf3 hdf hf3) (RS 139 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag
    33 (bs5 h79 hfc hfd hcf hef) R0 R0 R0 (RS 39 B)) DPEmpty DPEmpty)) (DPNode (MkDag 45 (bs5 h65 hf7 h3c hff h2f)
    R0 R0 R0 (RS 107 B)) (DPNode (MkDag 13 (bs5 hb9 hfc hbe h79 hfc) R0 (RS 16 C) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 37 (bs5 h79 h7b h9f hff h72) (RS 59 B) R0 R0 R0) (DPNode (MkDag 43 (bs5 h9e h7f h73 hf9 h7f) R0
    (RS 91 A) R0 (RS 91 A)) (DPNode (MkDag 40 (bs5 h9e h79 hf3 hcf h2f) R0 R0 R0 (RS 155 A)) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs5 h7f h9f hf9 hf9 h79) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty)) (DPNode (MkDag 39 (bs5 h79 hff
    h97 h9f h9e) R0 R0 R0 (RS 121 B)) (DPNode (MkDag 54 (bs5 hf9 he7 h9e h5f h2f) (RS 186 D) R0 (RS 187 E) (RS 188
    A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_67 : DagPTree :=
  DPNode (MkDag 11 (bs5 hcf h3c hf3 hcb hf3) R0 R0 R0 (RS 136 D)) (DPNode (MkDag 19 (bs5 hf9 hfc hbe h79 he7) R0 R0
    (RS 169 E) (RS 170 A)) (DPNode (MkDag 32 (bs5 hb9 hfc hfe hff h9e) R0 (RS 197 C) R0 (RS 197 C)) (DPNode (MkDag
    6 (bs5 hfc hfc hfd hcb hf3) R0 (RS 12 A) R0 R0) (DPNode (MkDag 25 (bs5 h79 he7 h97 hcf hee) R0 R0 R0 (RS 132
    B)) DPEmpty DPEmpty) (DPNode (MkDag 32 (bs5 h79 hfc hfe hff h9e) R0 R0 R0 (RS 197 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 21 (bs5 h9f h3f h9f he7 h97) R0 (RS 103 C) R0 R0) (DPNode (MkDag 49 (bs5 hb9 h7b h97 hdf hf3) R0 (RS 167
    C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 24 (bs5 h72 hfc hbe h7e h7d) R0 R0 R0 (RS 229 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 13 (bs5 hf2 hfb hfe h79 hfc) R0 (RS 55 A) R0 R0) (DPNode (MkDag 5 (bs5 h9e h5f h72 hf9 h79) R0
    (RS 0 C) R0 (RS 0 C)) (DPNode (MkDag 16 (bs5 hff hcf hcf hcf h3f) (RS 150 D) R0 (RS 151 E) (RS 152 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 38 (bs5 hfe h5f hf3 hcb hf3) R0 (RS 215 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 39
    (bs5 hb9 hef h97 h9f h9e) R0 (RS 119 C) R0 R0) (DPNode (MkDag 4 (bs5 h79 he7 hf3 hcf h72) R0 R0 R0 (RS 4 B))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 25 (bs5 hcf h3f h97 hcb hee) R0 R0 R0 (RS 36 D)) (DPNode (MkDag 25
    (bs5 h73 hfb hfd hcb hee) R0 R0 R0 (RS 45 B)) (DPNode (MkDag 22 (bs5 hff h3c hbe h7f hf3) (RS 78 D) R0 R0 (RS
    79 A)) (DPNode (MkDag 36 (bs5 hff hfe h7e h5f h73) R0 R0 (RS 143 E) (RS 144 A)) DPEmpty DPEmpty) (DPNode (MkDag
    55 (bs5 hcf h2f h9e h7b hfe) (RS 206 D) R0 R0 (RS 208 D)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs5 haf hff h3f
    hb9 h7f) R0 R0 (RS 111 E) R0) (DPNode (MkDag 49 (bs5 h79 hfc hbe h5f h3c) R0 R0 R0 (RS 172 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 38 (bs5 h9e hff h73 hfb h9f) R0 (RS 63 A) R0 R0) (DPNode (MkDag 2 (bs5 hbf hcb hee h5f
    h72) R0 (RS 2 C) (RS 96 E) R0) (DPNode (MkDag 12 (bs5 hf7 hcb hff hfe h7e) R0 (RS 15 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 28 (bs5 h7e h5e h7c hbc hfc) (RS 35 D) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 26 (bs5 hf9
    hfc hbe h7f he7) R0 (RS 127 A) R0 R0) (DPNode (MkDag 38 (bs5 hb9 hff h73 hfb h9f) R0 (RS 191 C) R0 (RS 191 C))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_68 : DagPTree :=
  DPNode (MkDag 7 (bs5 hf3 he7 h9e h79 hf3) (RS 9 D) R0 (RS 135 E) (RS 14 D)) (DPNode (MkDag 14 (bs5 hb9 he7 hf2
    hf3 hf3) R0 (RS 183 C) R0 (RS 183 C)) (DPNode (MkDag 27 (bs5 h9f hff he7 he7 h9f) R0 R0 R0 (RS 105 B)) (DPNode
    (MkDag 15 (bs5 hf3 hdc hf3 hfb h9e) R0 (RS 66 C) R0 R0) (DPNode (MkDag 48 (bs5 hb9 hfc hbf hff hcf) R0 (RS 130
    C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs5 h79 hff h73 hfb h9f) R0 R0 R0 (RS 191 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 38 (bs5 hee h5f hf3 hcb hf3) (RS 97 D) R0 R0 (RS 98 B)) (DPNode (MkDag 7 (bs5 hb9 h7c hfe h79
    hf3) R0 (RS 162 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 18 (bs5 hbc hbf hf9 h7f h2f) R0 R0 (RS 21 E) R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 22 (bs5 he7 hff h73 hf3 hf3) R0 R0 R0 (RS 50 A)) (DPNode (MkDag 41 (bs5 hbf
    h3f hb9 h79 hf3) R0 R0 (RS 82 E) R0) (DPNode (MkDag 0 (bs5 hbe h79 h7e h7f h3f) R0 R0 (RS 146 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 5 (bs5 hcf h2f h3f hf3 hf3) R0 R0 R0 (RS 210 C)) DPEmpty DPEmpty)) (DPNode (MkDag 19
    (bs5 h3f hff h3f hb9 h7f) R0 R0 R0 (RS 114 A)) (DPNode (MkDag 11 (bs5 hf9 hfc hbe h5e h7f) (RS 177 D) (RS 178
    A) R0 (RS 178 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 22 (bs5 hb9 h7c hf3 hf3 hf3) R0 R0 R0 (RS 32 C))
    (DPNode (MkDag 8 (bs5 hcb hdc hbd hcf hee) R0 R0 R0 (RS 42 D)) (DPNode (MkDag 8 (bs5 h97 h9f h97 hcf h9e) R0
    (RS 74 A) R0 R0) (DPNode (MkDag 50 (bs5 h79 he7 hbf hdf hf2) (RS 138 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 4 (bs5 hb9 hfc hff hf9 he5) R0 (RS 203 C) R0 (RS 203 C)) DPEmpty DPEmpty)) (DPNode (MkDag 44 (bs5 h7f
    he5 hff he7 he5) (RS 106 E) R0 R0 R0) (DPNode (MkDag 19 (bs5 h79 hfc hbe h79 he7) R0 R0 R0 (RS 22 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f hf9 h7e h5f h3f) R0 R0 R0 (RS 58 B)) (DPNode (MkDag 0 (bs5 h73 hff
    hf3 hcf h3f) R0 R0 R0 (RS 87 B)) (DPNode (MkDag 34 (bs5 hf3 he7 hee h7f h3e) R0 (RS 154 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 27 (bs5 hff hff he7 he7 h9f) (RS 217 D) R0 R0 (RS 1 C)) DPEmpty DPEmpty)) (DPNode
    (MkDag 39 (bs5 hf9 hff h97 h9f h9e) R0 R0 (RS 122 E) (RS 123 A)) (DPNode (MkDag 14 (bs5 h79 he7 hf2 hf3 hf3) R0
    R0 R0 (RS 183 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_69 : DagPTree :=
  DPNode (MkDag 10 (bs5 hbf h3f h3e he7 h9f) R0 (RS 27 C) (RS 104 E) R0) (DPNode (MkDag 18 (bs5 h3c hbf hf9 h7f
    h2f) R0 R0 R0 (RS 226 C)) (DPNode (MkDag 31 (bs5 hfe h79 h7e h7f h73) R0 (RS 24 A) (RS 99 E) (RS 24 A)) (DPNode
    (MkDag 6 (bs5 hbc hfc hfd hcb hf3) R0 (RS 70 C) R0 R0) (DPNode (MkDag 30 (bs5 h9f h3c hf3 hdf hf3) R0 (RS 9 C)
    R0 (RS 9 C)) DPEmpty DPEmpty) (DPNode (MkDag 32 (bs5 hf9 hfc hfe hff h9e) (RS 197 D) R0 (RS 198 E) (RS 199 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 21 (bs5 h7f h3f h9e he7 h97) R0 R0 R0 (RS 100 B)) (DPNode (MkDag 3 (bs5 hb9
    h7c hfc hff hf3) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 24 (bs5 hf2 hfc hbe h7e h7d) R0 R0 (RS 230
    E) (RS 231 A)) DPEmpty DPEmpty))) (DPNode (MkDag 11 (bs5 hf3 hcf h3f hcb hf3) R0 (RS 54 C) R0 R0) (DPNode
    (MkDag 42 (bs5 h9f hcb hf2 hf9 h7c) R0 (RS 86 A) R0 R0) (DPNode (MkDag 33 (bs5 hfd hcf he7 hcf h3f) R0 R0 R0
    (RS 150 C)) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs5 hbe h5f hf3 hcb hf3) R0 (RS 214 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 47 (bs5 hcf hf9 h7e h79 h79) R0 R0 R0 (RS 118 A)) (DPNode (MkDag 16 (bs5 h79 hfc hf3 hcf h3f) R0
    R0 R0 (RS 179 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 24 (bs5 hf9 hfc hbe h7e h7d) R0 R0 (RS 128 E) (RS
    129 A)) (DPNode (MkDag 25 (bs5 hf3 hfb hfd hcb hee) R0 R0 (RS 46 E) (RS 47 C)) (DPNode (MkDag 22 (bs5 hbf h3c
    hbe h7f hf3) R0 (RS 78 C) R0 R0) (DPNode (MkDag 35 (bs5 h7f hb9 h7f hf3 hee) R0 R0 R0 (RS 140 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 8 (bs5 hf9 hfb h97 hcf h9e) R0 (RS 206 D) (RS 207 E) (RS 206 D)) DPEmpty DPEmpty))
    (DPNode (MkDag 19 (bs5 h3d hff h3f hb9 h7f) R0 R0 R0 (RS 110 C)) (DPNode (MkDag 0 (bs5 hb9 hfc hbe h5f h3f) R0
    (RS 5 C) R0 (RS 5 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 31 (bs5 h79 hfb h9f hdf hf3) (RS 62 A) R0 R0
    R0) (DPNode (MkDag 2 (bs5 hf7 hcb hee h5f h72) R0 (RS 94 C) (RS 95 E) (RS 94 C)) (DPNode (MkDag 53 (bs5 h9f hdf
    hf3 hf9 hfe) R0 (RS 158 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h3e h5f h3f hfe h7f) R0 R0 R0 (RS 34
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 26 (bs5 hb9 hfc hbe h7f he7) R0 (RS 126 C) R0 R0) (DPNode (MkDag 10 (bs5
    hf9 h7b h9f h9f h9f) (RS 189 D) (RS 190 A) R0 (RS 190 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_70 : DagPTree :=
  DPNode (MkDag 9 (bs5 hff hfc hf3 hfb h9f) (RS 11 D) R0 R0 (RS 229 C)) (DPNode (MkDag 16 (bs5 h9e h79 hf3 hff h2f)
    R0 (RS 90 A) R0 (RS 90 A)) (DPNode (MkDag 29 (bs5 hcf hfe h7f hff h3c) R0 R0 R0 (RS 223 C)) (DPNode (MkDag 32
    (bs5 hbe h7c hfe hff h9e) R0 (RS 68 C) R0 R0) (DPNode (MkDag 25 (bs5 hb9 he7 h97 hcf hee) R0 (RS 132 C) R0 (RS
    132 C)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5 hf9 hfc hf3 hfb h9e) R0 (RS 38 A) (RS 196 E) (RS 38 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 31 (bs5 h7e h79 h7e h7f h73) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 23 (bs5 hf9 h7c hfe
    h7f h73) R0 R0 (RS 164 E) (RS 165 A)) DPEmpty DPEmpty) (DPNode (MkDag 39 (bs5 h3c hbf h97 h9f h9e) R0 R0 R0 (RS
    228 A)) DPEmpty DPEmpty))) (DPNode (MkDag 36 (bs5 h97 h9f h9e h7f h73) R0 R0 R0 (RS 52 A)) (DPNode (MkDag 5
    (bs5 hbf h3f h3f hf3 hf3) R0 (RS 84 C) R0 R0) (DPNode (MkDag 11 (bs5 he7 hcf h3e h7e h7f) R0 R0 R0 (RS 148 B))
    DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h3f hfe h7e h5f h73) R0 R0 R0 (RS 212 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 46 (bs5 hf2 hf3 he7 hfe h7c) (RS 115 D) R0 R0 (RS 116 B)) (DPNode (MkDag 16 (bs5 hf9 hfc hf3 hcf h3f) R0
    (RS 180 A) (RS 181 E) (RS 180 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 10 (bs5 hff h3f h3e he7 h9f) R0
    (RS 33 A) R0 R0) (DPNode (MkDag 35 (bs5 hf3 hcf hf2 hf3 hee) R0 R0 (RS 44 E) (RS 45 C)) (DPNode (MkDag 40 (bs5
    h7f hfc hf3 hdf h2f) (RS 76 D) R0 R0 R0) (DPNode (MkDag 34 (bs5 h79 he7 h9e h7f h3e) (RS 31 D) R0 R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hf9 hfc hff hf9 he5) R0 (RS 10 A) (RS 204 E) (RS 10 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 45 (bs5 he5 hf7 h3c hff h2f) R0 R0 R0 (RS 108 C)) (DPNode (MkDag 49 (bs5 hb9 hfc hbe
    h5f h3c) R0 (RS 172 C) R0 (RS 172 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs5 h79 hff h72 hf9 hf2) (RS
    60 B) R0 R0 R0) (DPNode (MkDag 37 (bs5 h97 hdf h9f hdf hf2) R0 (RS 92 A) R0 (RS 92 A)) (DPNode (MkDag 53 (bs5
    h9e h7f h73 hf9 hee) R0 (RS 156 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 17 (bs5 h7f h9e h7f hf9 h7c) R0 R0 R0
    (RS 20 B)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 hb9 hfc hf3 hfb h9f) R0 (RS 124 C) R0 R0) (DPNode (MkDag 54
    (bs5 h79 he7 h9e h5f h2f) R0 R0 R0 (RS 186 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_20_71 : DagPTree :=
  DPNode (MkDag 12 (bs5 hbf hcb hff hfe h7e) R0 (RS 159 C) R0 R0) (DPNode (MkDag 20 (bs5 hf9 hff he7 hff h9f) R0
    (RS 18 A) (RS 194 E) (RS 18 A)) (DPNode (MkDag 33 (bs5 hf9 hfc hfd hcf hef) R0 (RS 201 A) (RS 202 E) (RS 201
    A)) (DPNode (MkDag 39 (bs5 h97 hcf h9e h7b h9e) R0 (RS 72 A) R0 R0) (DPNode (MkDag 7 (bs5 h73 he7 h9e h79 hf3)
    R0 R0 R0 (RS 9 B)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5 hb9 hfc hfd hcb hf3) R0 (RS 8 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 10 (bs5 hf7 h3f h3e he7 h9f) (RS 103 D) (RS 13 C) R0 (RS 13 C)) (DPNode (MkDag 49 (bs5
    hf9 h7b h97 hdf hf3) R0 (RS 168 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 48 (bs5 h9e h7c hbf hff hcf) R0 (RS
    134 B) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs5 h9e hf9 h7e h5f h3f) R0 R0 R0 (RS 56 A)) (DPNode (MkDag
    0 (bs5 hf3 hff hf3 hcf h3f) (RS 87 D) (RS 19 A) (RS 89 E) (RS 19 A)) (DPNode (MkDag 16 (bs5 h7f hcf hcf hcf
    h3f) R0 R0 R0 (RS 150 B)) DPEmpty DPEmpty) (DPNode (MkDag 31 (bs5 hbe h79 h7e h7f h73) R0 (RS 37 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 39 (bs5 hf9 hef h97 h9f h9e) R0 (RS 120 A) R0 R0) (DPNode (MkDag 14 (bs5 hf9
    he7 hf2 hf3 hf3) R0 (RS 184 A) (RS 185 E) (RS 184 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 26 (bs5 hcf
    h3c hf7 hff he7) R0 R0 R0 (RS 140 C)) (DPNode (MkDag 22 (bs5 hbe hff h73 hf3 hf3) R0 R0 (RS 48 E) R0) (DPNode
    (MkDag 3 (bs5 h9f h3c hff h9f h73) R0 (RS 80 C) R0 R0) (DPNode (MkDag 36 (bs5 h7f hfe h7e h5f h73) R0 R0 R0 (RS
    142 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs5 h79 hfb h97 hcf h9e) R0 R0 R0 (RS 205 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 19 (bs5 h2f hff h3f hb9 h7f) R0 R0 R0 (RS 112 C)) (DPNode (MkDag 0 (bs5 h79 hfc hbe h5f h3f) R0
    R0 R0 (RS 5 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 38 (bs5 h97 hff h73 hfb h9f) R0 R0 R0 (RS 64 A))
    (DPNode (MkDag 2 (bs5 h77 hcb hee h5f h72) R0 R0 R0 (RS 93 B)) (DPNode (MkDag 12 (bs5 hff hcb hff hfe h7e) R0
    (RS 25 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 33 (bs5 hbf hff h2f hcb hef) R0 R0 (RS 224 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 24 (bs5 hb9 hfc hbe h7e h7d) R0 R0 R0 (RS 29 C)) (DPNode (MkDag 38 (bs5 hf9 hff h73
    hfb h9f) R0 (RS 192 A) (RS 193 E) (RS 192 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_20 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf3 hdf hf3 hcf h3f) R0 (RS 87 C) (RS 88 E) (RS 87 C)) (DPNode (MkDag 1 (bs5 hff h9f hf9
    hf9 h79) R0 R0 (RS 218 E) (RS 20 C)) (DPNode (MkDag 2 (bs5 hff hcb hee h5f h72) R0 (RS 213 C) R0 R0) (DPNode
    (MkDag 4 (bs5 hf9 he7 hf3 hcf h72) R0 (RS 17 A) (RS 182 E) (RS 17 A)) dagSub_20_64 dagSub_20_65) (DPNode (MkDag
    3 (bs5 hcf h2f h9f hdf hf3) R0 R0 R0 (RS 142 C)) dagSub_20_66 dagSub_20_67)) (DPNode (MkDag 3 (bs5 hf9 h7c hfc
    hff hf3) (RS 3 D) R0 R0 (RS 166 A)) (DPNode (MkDag 0 (bs5 hf9 hfc hbe h5f h3f) (RS 5 D) R0 (RS 175 E) (RS 176
    A)) dagSub_20_68 dagSub_20_69) (DPNode (MkDag 5 (bs5 hfe h5f hfe h79 hf9) (RS 7 D) R0 R0 (RS 145 C))
    dagSub_20_70 dagSub_20_71))).

Definition dagSub_21_72 : DagPTree :=
  DPNode (MkDag 7 (bs5 h79 he7 h9f hcb hef) (RS 131 B) R0 R0 R0) (DPNode (MkDag 12 (bs5 hfe h5f hfd hcf h3f) R0 (RS
    17 B) R0 R0) (DPNode (MkDag 18 (bs5 h7c hff h2f h3f h2f) R0 R0 R0 (RS 33 B)) (DPNode (MkDag 28 (bs5 h79 hf2 hf3
    he7 hbf) R0 R0 R0 (RS 65 B)) (DPNode (MkDag 37 (bs5 h7f h2f h9f h9f h3c) (RS 129 B) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 32 (bs5 hff hcf h97 hcb he7) R0 (RS 97 A) R0 R0) (DPNode (MkDag 5 (bs5 h9f he7 h9e h79
    h7f) R0 R0 R0 (RS 161 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs5 hbe he7 hfe h7f h3f) R0 (RS 49 C)
    R0 R0) (DPNode (MkDag 1 (bs5 hff hcf h2f h9f he5) R0 R0 R0 (RS 81 C)) (DPNode (MkDag 34 (bs5 h2f h9f h2f h3e
    he5) R0 R0 R0 (RS 145 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h7c hff h2f h9f he5) (RS 113 D) R0 R0
    R0) (DPNode (MkDag 3 (bs5 h97 he7 h9f hf9 h7f) R0 R0 R0 (RS 177 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    3 (bs5 haf hcb he5 hf9 h7f) R0 R0 (RS 25 E) R0) (DPNode (MkDag 20 (bs5 hf2 hf9 hf9 hf3 he5) R0 (RS 41 A) R0 R0)
    (DPNode (MkDag 16 (bs5 hb9 he7 h9f h9f h3c) R0 R0 R0 (RS 73 C)) (DPNode (MkDag 29 (bs5 h5f h9f hf9 hf9 he5) (RS
    103 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 9 (bs5 hcf h3f h2f hfe h7f) R0 R0 R0 (RS 138 D))
    (DPNode (MkDag 2 (bs5 h77 h2f h9f hdf h3c) R0 R0 R0 (RS 167 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 25
    (bs5 h3e h7f hef hcb he7) R0 R0 R0 (RS 57 B)) (DPNode (MkDag 10 (bs5 h9f he7 h9e h7f h2f) R0 (RS 89 C) R0 R0)
    (DPNode (MkDag 11 (bs5 h2f h3f h2f h9f h9f) R0 R0 R0 (RS 153 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5
    (bs5 h5e he7 h9e h79 h7f) (RS 121 B) R0 R0 R0) (DPNode (MkDag 36 (bs5 h97 he7 hf2 hf9 hfd) R0 R0 R0 (RS 185 A))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_73 : DagPTree :=
  DPNode (MkDag 2 (bs5 h3f h2f h9f hdf h3c) R0 R0 R0 (RS 170 A)) (DPNode (MkDag 7 (bs5 he5 hf3 hf3 hf9 h7f) (RS 20
    D) R0 R0 (RS 21 B)) (DPNode (MkDag 19 (bs5 hbc hf3 hff hcb he7) R0 R0 (RS 37 E) R0) (DPNode (MkDag 29 (bs5 h9f
    h72 hf9 hf9 he5) R0 (RS 69 C) R0 R0) (DPNode (MkDag 38 (bs5 h79 hfc hfe h5f h3f) (RS 10 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 19 (bs5 h9f h3c hf3 hcb hcf) R0 (RS 101 A) R0 R0) (DPNode (MkDag 39 (bs5 h3f
    h2f h9e h7b he5) R0 R0 R0 (RS 165 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs5 h7f he7 he7 hcf h3c) R0
    R0 R0 (RS 51 B)) (DPNode (MkDag 3 (bs5 hfe h7f h97 hcb hef) R0 (RS 5 C) R0 R0) (DPNode (MkDag 35 (bs5 h2f h9f
    hfe h7c hff) R0 R0 R0 (RS 149 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 35 (bs5 h9f h9f hfe h7c hff) R0 (RS
    117 B) R0 (RS 117 B)) (DPNode (MkDag 10 (bs5 hff hcf he5 hf7 h3f) R0 (RS 181 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 16 (bs5 he7 hcf h2f h9f h3c) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 22 (bs5 hf7 he7 hee
    h7f he5) R0 R0 (RS 45 E) (RS 46 C)) (DPNode (MkDag 2 (bs5 hbf hb9 h7d hcf h3c) R0 R0 (RS 77 E) R0) (DPNode
    (MkDag 1 (bs5 hbc hff h2f h9f he5) R0 (RS 1 C) (RS 142 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 24 (bs5
    hbe h7f h7f hcf h3f) R0 (RS 109 C) (RS 110 E) R0) (DPNode (MkDag 20 (bs5 h9f h2f he5 hf9 he5) R0 R0 R0 (RS 8
    B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 19 (bs5 hfb h97 hf3 hcb hcf) R0 (RS 61 A) R0 R0) (DPNode (MkDag
    31 (bs5 hbf hcf h9e h7f hf3) R0 R0 R0 (RS 93 C)) (DPNode (MkDag 36 (bs5 hfe he7 hf2 hf9 hfd) (RS 156 D) R0 R0
    (RS 157 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7f h2f h9e h7f h3c) (RS 125 B) R0 R0 R0) (DPNode
    (MkDag 5 (bs5 hbf he7 h9e h79 h7f) R0 R0 R0 (RS 189 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_74 : DagPTree :=
  DPNode (MkDag 8 (bs5 h79 hfc hfe h5e h7f) (RS 133 C) R0 R0 R0) (DPNode (MkDag 13 (bs5 hff hff hcb hf2 hfc) (RS 18
    D) R0 R0 (RS 19 B)) (DPNode (MkDag 10 (bs5 h79 hf9 he7 hf7 h3f) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 28 (bs5 hb9
    hff he7 he7 hff) R0 (RS 67 C) R0 R0) (DPNode (MkDag 20 (bs5 h7f h2f he5 hf9 he5) (RS 8 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 hff hcf h9f hf9 he5) R0 R0 (RS 99 E) (RS 100 A)) (DPNode (MkDag 39 (bs5
    h77 h2f h9e h7b he5) R0 R0 R0 (RS 161 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs5 hbf he7 he7 hcf
    h3c) R0 R0 R0 (RS 51 C)) (DPNode (MkDag 30 (bs5 h3f h97 hf2 hf9 he7) R0 R0 R0 (RS 83 A)) (DPNode (MkDag 34 (bs5
    h3f h9f h2f h3e he5) R0 R0 R0 (RS 147 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 35 (bs5 hbb h9f hfe h7c hff)
    R0 (RS 115 C) R0 R0) (DPNode (MkDag 10 (bs5 hf7 hcf he5 hf7 h3f) R0 (RS 179 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 3 (bs5 hbf hcb he5 hf9 h7f) R0 R0 (RS 27 E) R0) (DPNode (MkDag 21 (bs5 h97 he5 he7
    hcf h9f) R0 (RS 43 A) R0 R0) (DPNode (MkDag 16 (bs5 h79 he7 h9f h9f h3c) R0 R0 R0 (RS 73 B)) (DPNode (MkDag 6
    (bs5 hcf he7 hff h3c hff) R0 R0 R0 (RS 139 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 hcb he7 h9f hf9
    h7f) R0 R0 R0 (RS 107 D)) (DPNode (MkDag 37 (bs5 hbf h2f h9f h9f h3c) R0 (RS 171 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 4 (bs5 h7c hfb hfd hf9 he5) (RS 4 D) R0 R0 R0) (DPNode (MkDag 20 (bs5 hbe he7 he5 hf9
    he5) R0 (RS 91 C) R0 R0) (DPNode (MkDag 11 (bs5 h3f h3f h2f h9f h9f) R0 R0 R0 (RS 155 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 10 (bs5 h7f h2f h9e h7f h2f) (RS 123 B) R0 R0 R0) (DPNode (MkDag 6 (bs5 hf3 he7 hf2 hf3
    hff) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_75 : DagPTree :=
  DPNode (MkDag 11 (bs5 hff h3f h2f h9f h9f) (RS 14 D) R0 R0 (RS 183 A)) (DPNode (MkDag 3 (bs5 hbd hcb he5 hf9 h7f)
    R0 R0 (RS 23 E) R0) (DPNode (MkDag 1 (bs5 hb2 hf9 hfc hfb he5) R0 (RS 39 C) R0 R0) (DPNode (MkDag 9 (bs5 hbe
    h7f h2f hfe h7f) R0 (RS 71 C) R0 R0) (DPNode (MkDag 33 (bs5 h7d hff h3f h9f h3f) R0 R0 R0 (RS 133 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 33 (bs5 h9f hff h3f h9f h3f) R0 (RS 103 B) R0 R0) (DPNode (MkDag 10 (bs5 hff
    h2f h9e h7f h2f) R0 (RS 0 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 24 (bs5 hff hfc hf2 hf7 h3f) R0
    R0 R0 (RS 55 C)) (DPNode (MkDag 10 (bs5 h7b he7 h9e h7f h2f) R0 R0 R0 (RS 87 B)) (DPNode (MkDag 35 (bs5 h3f h9f
    hfe h7c hff) R0 R0 R0 (RS 151 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 36 (bs5 h5e he7 hf2 hf9 hfd) (RS 119
    B) R0 R0 R0) (DPNode (MkDag 35 (bs5 h7b h9f hfe h7c hff) R0 R0 R0 (RS 115 B)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 18 (bs5 h7c hf7 h2f h3f h2f) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 22 (bs5 hbf he7 hee h7f he5) R0
    R0 (RS 47 E) R0) (DPNode (MkDag 1 (bs5 hef hcf h2f h9f he5) R0 R0 R0 (RS 79 B)) (DPNode (MkDag 1 (bs5 h3c hff
    h2f h9f he5) R0 R0 R0 (RS 143 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 24 (bs5 h3e h7f h7f hcf h3f) R0 R0
    R0 (RS 111 B)) (DPNode (MkDag 9 (bs5 h7f h3f h2f hfe h7f) R0 R0 R0 (RS 11 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 27 (bs5 hf3 hff hfc hf7 h3c) R0 R0 (RS 63 E) (RS 64 B)) (DPNode (MkDag 31 (bs5 h7f hcf h9e h7f
    hf3) R0 R0 R0 (RS 93 B)) (DPNode (MkDag 5 (bs5 h9e he7 h9e h79 h7f) R0 R0 R0 (RS 159 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 2 (bs5 h7f h2f h9f hdf h3c) (RS 127 B) R0 R0 R0) (DPNode (MkDag 5 (bs5 h7f he7 h9e h79
    h7f) R0 R0 R0 (RS 189 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_76 : DagPTree :=
  DPNode (MkDag 6 (bs5 hff he7 hf2 hf3 hff) R0 (RS 158 A) R0 R0) (DPNode (MkDag 13 (bs5 h7f hff hcb hf2 hfc) R0 R0
    R0 (RS 18 B)) (DPNode (MkDag 18 (bs5 hfc hff h2f h3f h2f) R0 R0 R0 (RS 34 B)) (DPNode (MkDag 28 (bs5 hf9 hf2
    hf3 he7 hbf) R0 R0 R0 (RS 66 A)) (DPNode (MkDag 20 (bs5 h5f h2f he5 hf9 he5) (RS 130 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 hbf hcf h9f hf9 he5) R0 R0 R0 (RS 98 C)) (DPNode (MkDag 39 (bs5 hf7 h2f
    h9e h7b he5) R0 R0 (RS 162 E) (RS 163 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs5 hfe he7 hfe h7f
    h3f) R0 (RS 50 A) R0 R0) (DPNode (MkDag 30 (bs5 hbf h97 hf2 hf9 he7) R0 R0 (RS 82 E) R0) (DPNode (MkDag 34 (bs5
    hbf h9f h2f h3e he5) R0 R0 (RS 146 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 34 (bs5 hcf h9f h2f h3e he5)
    R0 R0 R0 (RS 114 A)) (DPNode (MkDag 3 (bs5 h9f he7 h9f hf9 h7f) R0 (RS 178 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 3 (bs5 h2f hcb he5 hf9 h7f) R0 R0 R0 (RS 26 C)) (DPNode (MkDag 21 (bs5 h9e he5 he7
    hcf h9f) R0 R0 R0 (RS 42 A)) (DPNode (MkDag 16 (bs5 hf9 he7 h9f h9f h3c) R0 R0 (RS 74 E) (RS 75 D)) (DPNode
    (MkDag 29 (bs5 hfb h9f hf9 hf9 he5) R0 R0 R0 (RS 173 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 29 (bs5 hff
    h9f hf9 hf9 he5) (RS 105 D) R0 R0 (RS 6 D)) (DPNode (MkDag 2 (bs5 hbf h2f h9f hdf h3c) R0 R0 (RS 12 E) R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 26 (bs5 he7 hcf hfd hcb hcf) (RS 57 D) R0 R0 (RS 58 B)) (DPNode
    (MkDag 2 (bs5 hf3 he7 h9f hdf h3c) R0 (RS 90 C) R0 R0) (DPNode (MkDag 11 (bs5 hbf h3f h2f h9f h9f) R0 R0 (RS
    154 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 h7e he7 h9e h79 h7f) (RS 122 B) R0 R0 R0) (DPNode
    (MkDag 36 (bs5 h9f he7 hf2 hf9 hfd) R0 (RS 186 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_77 : DagPTree :=
  DPNode (MkDag 10 (bs5 hf7 h2f h9e h7f h2f) R0 (RS 165 C) R0 R0) (DPNode (MkDag 15 (bs5 he5 hf3 hcb he7 hfc) (RS
    21 D) R0 R0 (RS 22 C)) (DPNode (MkDag 19 (bs5 h3c hf3 hff hcb he7) R0 R0 R0 (RS 38 A)) (DPNode (MkDag 29 (bs5
    hf3 hf2 hf9 hf9 he5) R0 (RS 70 C) R0 R0) (DPNode (MkDag 33 (bs5 hfd hff h3f h9f h3f) R0 R0 (RS 134 E) (RS 135
    B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 33 (bs5 h97 hff h3f h9f h3f) R0 R0 R0 (RS 102 A)) (DPNode (MkDag
    10 (bs5 hbf h2f h9e h7f h2f) R0 (RS 166 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 24 (bs5 h7f hfc hf2
    hf7 h3f) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 5 (bs5 hfc hfb h9e h79 h7f) R0 (RS 86 B) R0 R0) (DPNode (MkDag 35
    (bs5 hbf h9f hfe h7c hff) R0 R0 (RS 150 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 11 (bs5 h7f h3f h2f h9f
    h9f) (RS 118 B) R0 R0 (RS 14 B)) (DPNode (MkDag 2 (bs5 hbe h79 hfd hcf h3c) R0 (RS 2 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 17 (bs5 he7 hff hff hcf h3f) R0 R0 R0 (RS 30 B)) (DPNode (MkDag 22 (bs5 h77 he7 hee
    h7f he5) R0 R0 R0 (RS 44 B)) (DPNode (MkDag 2 (bs5 h3f hb9 h7d hcf h3c) R0 R0 R0 (RS 78 B)) (DPNode (MkDag 24
    (bs5 h7e h7f h7f hcf h3f) R0 R0 R0 (RS 109 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 24 (bs5 hfe h7f h7f hcf
    h3f) R0 (RS 140 C) (RS 141 E) (RS 140 C)) (DPNode (MkDag 29 (bs5 h9f h9f hf9 hf9 he5) R0 (RS 174 B) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 19 (bs5 h9f h97 hf3 hcb hcf) R0 R0 R0 (RS 62 C)) (DPNode (MkDag 31
    (bs5 hff hcf h9e h7f hf3) R0 R0 (RS 94 E) (RS 95 A)) (DPNode (MkDag 6 (bs5 hbf he7 hf2 hf3 hff) R0 (RS 9 C) R0
    R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 h5f h2f h9f hdf h3c) (RS 126 B) R0 R0 R0) (DPNode (MkDag 5
    (bs5 hff he7 h9e h79 h7f) R0 R0 (RS 190 E) (RS 191 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_78 : DagPTree :=
  DPNode (MkDag 9 (bs5 hff h3f h2f hfe h7f) R0 R0 R0 (RS 175 A)) (DPNode (MkDag 14 (bs5 he5 hf3 hff h3f h3f) (RS 19
    D) R0 R0 (RS 20 B)) (DPNode (MkDag 10 (bs5 hf9 hf9 he7 hf7 h3f) R0 R0 R0 (RS 36 C)) (DPNode (MkDag 28 (bs5 hf9
    hff he7 he7 hff) (RS 67 D) R0 R0 (RS 68 A)) (DPNode (MkDag 4 (bs5 h79 he7 h9f hf9 he5) (RS 132 B) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 h7f hcf h9f hf9 he5) R0 R0 R0 (RS 98 B)) (DPNode (MkDag 39 (bs5
    hbf h2f h9e h7b he5) R0 R0 (RS 164 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs5 hff he7 he7 hcf
    h3c) R0 R0 (RS 52 E) (RS 53 B)) (DPNode (MkDag 3 (bs5 hbe h7f h97 hcb hef) R0 (RS 84 C) R0 R0) (DPNode (MkDag
    35 (bs5 haf h9f hfe h7c hff) R0 R0 (RS 148 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 35 (bs5 hfb h9f hfe
    h7c hff) (RS 115 D) (RS 116 A) R0 (RS 116 A)) (DPNode (MkDag 10 (bs5 hbf hcf he5 hf7 h3f) R0 (RS 180 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 3 (bs5 h3f hcb he5 hf9 h7f) R0 R0 R0 (RS 28 B)) (DPNode (MkDag 21
    (bs5 h9f he5 he7 hcf h9f) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 10 (bs5 hcf h3f he5 hf7 h3f) R0 R0 R0 (RS 76 C))
    (DPNode (MkDag 3 (bs5 hcf he7 h9f hf9 h7f) R0 R0 R0 (RS 109 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 10
    (bs5 hcf hcf he5 hf7 h3f) R0 R0 R0 (RS 108 C)) (DPNode (MkDag 37 (bs5 hff h2f h9f h9f h3c) R0 (RS 172 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 19 (bs5 hbb h97 hf3 hcb hcf) R0 (RS 60 C) R0 R0) (DPNode (MkDag 20
    (bs5 hfe he7 he5 hf9 he5) R0 (RS 92 A) R0 R0) (DPNode (MkDag 36 (bs5 hbe he7 hf2 hf9 hfd) R0 (RS 156 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h5f h2f h9e h7f h3c) (RS 124 B) R0 R0 R0) (DPNode (MkDag 3 (bs5
    hfe he7 h97 hcb hef) R0 (RS 188 A) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_21_79 : DagPTree :=
  DPNode (MkDag 12 (bs5 hbe h5f hfd hcf h3f) R0 (RS 16 C) R0 R0) (DPNode (MkDag 3 (bs5 h3d hcb he5 hf9 h7f) R0 R0
    R0 (RS 24 C)) (DPNode (MkDag 1 (bs5 hf2 hf9 hfc hfb he5) R0 (RS 40 C) R0 R0) (DPNode (MkDag 9 (bs5 hfe h7f h2f
    hfe h7f) R0 (RS 72 A) R0 R0) (DPNode (MkDag 29 (bs5 h7b h9f hf9 hf9 he5) (RS 136 B) R0 R0 (RS 137 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 29 (bs5 h7f h9f hf9 hf9 he5) (RS 104 D) R0 R0 (RS 105 B)) (DPNode (MkDag 2
    (bs5 hf7 h2f h9f hdf h3c) R0 R0 (RS 168 E) (RS 169 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 25 (bs5 hbe
    h7f hef hcb he7) R0 R0 (RS 56 E) R0) (DPNode (MkDag 10 (bs5 hfb he7 h9e h7f h2f) (RS 87 D) R0 R0 (RS 88 A))
    (DPNode (MkDag 11 (bs5 haf h3f h2f h9f h9f) R0 R0 (RS 152 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 36
    (bs5 h7e he7 hf2 hf9 hfd) (RS 7 B) R0 R0 R0) (DPNode (MkDag 36 (bs5 h9e he7 hf2 hf9 hfd) R0 (RS 184 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 18 (bs5 hfc hf7 h2f h3f h2f) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 22
    (bs5 h3f he7 hee h7f he5) R0 R0 R0 (RS 48 A)) (DPNode (MkDag 1 (bs5 h7f hcf h2f h9f he5) R0 R0 R0 (RS 80 B))
    (DPNode (MkDag 34 (bs5 haf h9f h2f h3e he5) R0 R0 (RS 144 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1
    (bs5 he7 hdf h2f h9f he5) R0 R0 R0 (RS 112 B)) (DPNode (MkDag 3 (bs5 h9e he7 h9f hf9 h7f) R0 (RS 176 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 27 (bs5 h73 hff hfc hf7 h3c) R0 R0 R0 (RS 62 B)) (DPNode (MkDag 32
    (bs5 hbf hcf h97 hcb he7) R0 (RS 96 C) R0 R0) (DPNode (MkDag 5 (bs5 h97 he7 h9e h79 h7f) R0 (RS 160 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 37 (bs5 h5f h2f h9f h9f h3c) (RS 128 B) R0 R0 R0) (DPNode (MkDag 39
    (bs5 h9f h2f h9e h7b he5) R0 (RS 13 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_21 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h9f h2f h9e h7f h3c) R0 R0 R0 (RS 167 C)) (DPNode (MkDag 1 (bs5 hfc hff h2f h9f he5) R0
    (RS 182 B) R0 R0) (DPNode (MkDag 2 (bs5 hfe h79 hfd hcf h3c) R0 (RS 108 C) R0 R0) (DPNode (MkDag 4 (bs5 hcf h9f
    hfd hf9 he5) R0 R0 R0 (RS 59 A)) dagSub_21_72 dagSub_21_73) (DPNode (MkDag 6 (bs5 hcb he7 hff h3c hff) R0 R0 R0
    (RS 106 D)) dagSub_21_74 dagSub_21_75)) (DPNode (MkDag 3 (bs5 hbe he7 h97 hcb hef) R0 (RS 187 C) R0 R0) (DPNode
    (MkDag 5 (bs5 hbc hfb h9e h79 h7f) R0 (RS 85 C) R0 R0) dagSub_21_76 dagSub_21_77) (DPNode (MkDag 6 (bs5 h7f he7
    hf2 hf3 hff) (RS 120 B) R0 R0 R0) dagSub_21_78 dagSub_21_79))).

Definition dagTree_22 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hfe h5e h7e h5f h2f) R0 (RS 2 C) (RS 80 E) (RS 2 C)) (DPNode (MkDag 1 (bs5 h97 hdc hbc
    hf9 h7c) R0 (RS 85 A) R0 (RS 85 A)) (DPNode (MkDag 2 (bs5 hf3 hcf hff hf9 h7c) (RS 2 D) (RS 81 A) (RS 82 E) (RS
    81 A)) (DPNode (MkDag 1 (bs5 he7 hfc hbc hf9 h7c) (RS 4 D) R0 R0 (RS 28 A)) (DPNode (MkDag 4 (bs5 hf9 h7e h7f
    h73 hcb) R0 (RS 9 D) R0 R0) (DPNode (MkDag 1 (bs5 hbf hcf h2f hb9 h7c) R0 R0 (RS 17 E) R0) (DPNode (MkDag 2
    (bs5 hbc hbf h9e h79 h7c) R0 (RS 33 C) R0 R0) (DPNode (MkDag 1 (bs5 h3e hf9 he5 hf9 h7c) R0 R0 R0 (RS 65 B))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hee h5e h7e h5f h2f) (RS 96 D) R0 R0 (RS 80 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs5 hef hf3 hcf hb9 h7c) R0 R0 R0 (RS 49 B)) (DPNode (MkDag 0 (bs5 h7e h5e h7e h5f h2f) (RS
    81 A) R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 11 (bs5 h2f hcb he7 hfe h79) R0 R0 R0 (RS 25
    C)) (DPNode (MkDag 12 (bs5 hff hff hfe h5f h2f) R0 (RS 41 B) R0 R0) (DPNode (MkDag 11 (bs5 he5 hff he7 hfe h79)
    (RS 72 D) R0 R0 (RS 73 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hdc hf3 hf9 hf9 h7c) R0 R0 R0 (RS 57
    A)) (DPNode (MkDag 2 (bs5 h7f hef h9e h79 h7c) (RS 89 C) R0 R0 (RS 90 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 8 (bs5 hcf he7 hbf he5 hee) R0 R0 R0 (RS 13 D)) (DPNode (MkDag 2 (bs5 hff hf9 h7e h79 h7c) R0 R0 R0 (RS
    21 C)) (DPNode (MkDag 2 (bs5 he7 he7 hcf hb9 h7c) (RS 36 D) R0 R0 (RS 37 A)) (DPNode (MkDag 3 (bs5 hbc hff h3f
    hfe h7c) R0 (RS 69 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 hee h5f h3f h9e h7c) R0 R0 R0 (RS 78 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h3f hcf hee h5f h2f) R0 R0 R0 (RS 53 B)) (DPNode (MkDag 2 (bs5 h9e h7f
    hcf hb9 h7c) R0 (RS 1 A) R0 (RS 1 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs5 h9f hff h7f hf9 h7c) R0
    (RS 29 B) R0 R0) (DPNode (MkDag 13 (bs5 haf hf3 hf9 hff h3c) R0 R0 (RS 45 E) R0) (DPNode (MkDag 3 (bs5 h3e h5f
    h3f h9e h7c) R0 R0 R0 (RS 96 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h73 hcf hee h5f h2f) R0 R0 R0
    (RS 59 B)) (DPNode (MkDag 10 (bs5 h3e h5e he5 hef h9e) R0 R0 R0 (RS 93 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 3 (bs5 h9e h5f h3f hfe h7c) R0 R0 R0 (RS 55 B)) (DPNode (MkDag 6 (bs5 hcf h3f h9e h7f h73) R0 R0 R0 (RS
    11 D)) (DPNode (MkDag 2 (bs5 hef hf9 h7e h79 h7c) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 10 (bs5 he7 h9f he5 hef
    h9e) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 3 (bs5 h7c hf7 h3f hfe h7c) (RS 67 D) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 11 (bs5 hbe h7f he7 hfe h79) R0 R0 (RS 99 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hff hf3
    hcf hb9 h7c) R0 R0 R0 (RS 51 C)) (DPNode (MkDag 2 (bs5 h73 hcf hff hf9 h7c) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 11 (bs5 h3f hcb he7 hfe h79) R0 R0 R0 (RS 27 B)) (DPNode (MkDag 13 (bs5 hbd hf3 hf9
    hff h3c) R0 R0 (RS 43 E) R0) (DPNode (MkDag 3 (bs5 hbe h5f h3f h9e h7c) R0 (RS 75 C) (RS 76 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hfc hf3 hf9 hf9 h7c) (RS 58 D) R0 R0 (RS 59 C)) (DPNode (MkDag 2 (bs5
    hff hef h9e h79 h7c) (RS 90 D) R0 R0 (RS 91 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 9 (bs5 hcf he7 hf3
    hff hfc) R0 R0 R0 (RS 15 D)) (DPNode (MkDag 11 (bs5 h3d hcb he7 hfe h79) R0 R0 R0 (RS 23 C)) (DPNode (MkDag 12
    (bs5 hf7 hff hfe h5f h2f) R0 (RS 39 C) R0 R0) (DPNode (MkDag 10 (bs5 h7c hbe he5 hef h9e) R0 R0 R0 (RS 71 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h9e h5f h3d hfe h7c) R0 (RS 6 A) R0 R0) (DPNode (MkDag 14 (bs5
    h97 h9f hfc hff h97) R0 (RS 87 A) R0 (RS 87 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 hff h97 he5
    hf9 h7c) (RS 30 D) R0 R0 (RS 31 B)) (DPNode (MkDag 13 (bs5 hbf hf3 hf9 hff h3c) R0 R0 (RS 47 E) R0) (DPNode
    (MkDag 3 (bs5 h7e h5f h3f h9e h7c) (RS 0 C) R0 R0 (RS 75 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5
    h73 hfb hfe h5f h2f) R0 R0 R0 (RS 61 B)) (DPNode (MkDag 11 (bs5 h7e h7f he7 hfe h79) (RS 75 C) R0 R0 (RS 95 B))
    DPEmpty DPEmpty) DPEmpty))))) (DPNode (MkDag 1 (bs5 h9e h5e he5 hf9 h7c) R0 (RS 88 B) R0 (RS 88 B)) (DPNode
    (MkDag 2 (bs5 hdc hbf h9e h79 h7c) R0 R0 R0 (RS 32 A)) (DPNode (MkDag 5 (bs5 hcf h3f h9f hcf h7c) (RS 9 D) R0
    R0 (RS 10 D)) (DPNode (MkDag 1 (bs5 h3f hcf h2f hb9 h7c) R0 R0 R0 (RS 18 B)) (DPNode (MkDag 2 (bs5 hfc hbf h9e
    h79 h7c) R0 (RS 34 B) R0 R0) (DPNode (MkDag 1 (bs5 he7 hf9 he5 hf9 h7c) (RS 65 D) R0 R0 (RS 66 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 10 (bs5 h7e h5e he5 hef h9e) R0 R0 R0 (RS 89 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2
    (bs5 h7f hf3 hcf hb9 h7c) R0 R0 R0 (RS 50 B)) (DPNode (MkDag 0 (bs5 h9e h79 he7 hcf h2f) R0 (RS 83 A) R0 (RS 83
    A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 11 (bs5 hbf hcb he7 hfe h79) R0 R0 (RS 26 E) R0) (DPNode (MkDag 3
    (bs5 he5 hf7 h3f hfe h7c) R0 R0 R0 (RS 42 C)) (DPNode (MkDag 2 (bs5 he5 hf2 hf9 hf9 h7c) (RS 73 D) R0 R0 (RS 74
    A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hbc hf3 hf9 hf9 h7c) R0 (RS 58 C) R0 R0) (DPNode (MkDag 10
    (bs5 hfe h5e he5 hef h9e) R0 R0 (RS 97 E) (RS 98 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs5 hcf he7
    hff he5 hee) R0 R0 R0 (RS 14 D)) (DPNode (MkDag 11 (bs5 hbd hcb he7 hfe h79) R0 R0 (RS 22 E) R0) (DPNode (MkDag
    1 (bs5 h9f hdc hfc hf9 h7c) R0 (RS 38 C) R0 R0) (DPNode (MkDag 3 (bs5 hfc hff h3f hfe h7c) R0 (RS 70 B) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hb3 hcf hff hf9 h7c) R0 (RS 2 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    12 (bs5 he7 h9f hfe h5f h2f) (RS 53 D) R0 R0 (RS 54 A)) (DPNode (MkDag 1 (bs5 h9f hdc hbc hf9 h7c) R0 (RS 86 A)
    R0 (RS 86 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 h7f h97 he5 hf9 h7c) R0 R0 R0 (RS 30 B)) (DPNode
    (MkDag 13 (bs5 h2f hf3 hf9 hff h3c) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 0 (bs5 hbe h5e h7e h5f h2f) R0 (RS 0 C)
    (RS 79 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5 hf3 hfb hfe h5f h2f) R0 R0 (RS 62 E) (RS 63 C))
    (DPNode (MkDag 11 (bs5 hee h7f he7 hfe h79) R0 R0 R0 (RS 94 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 4
    (bs5 hb9 h7e h7f h73 hcb) R0 (RS 8 C) R0 R0) (DPNode (MkDag 7 (bs5 hcf h3f h3f he5 hee) R0 R0 R0 (RS 12 D))
    (DPNode (MkDag 2 (bs5 h7f hf9 h7e h79 h7c) R0 R0 R0 (RS 20 B)) (DPNode (MkDag 11 (bs5 he7 hf3 he7 hfe h79) (RS
    35 D) R0 R0 (RS 36 B)) (DPNode (MkDag 3 (bs5 hdc hff h3f hfe h7c) R0 R0 R0 (RS 68 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 11 (bs5 h3e h7f he7 hfe h79) R0 R0 R0 (RS 100 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbf hcf hee
    h5f h2f) R0 R0 (RS 52 E) R0) (DPNode (MkDag 11 (bs5 h9e h5e he7 hfe h79) R0 (RS 84 A) R0 (RS 84 A)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs5 he7 hcb hcf hb9 h7c) (RS 27 D) R0 R0 (RS 4 B)) (DPNode (MkDag 13 (bs5
    h3d hf3 hf9 hff h3c) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 3 (bs5 hfe h5f h3f h9e h7c) R0 (RS 77 C) (RS 78 E) (RS
    77 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hf3 hcf hee h5f h2f) R0 R0 (RS 60 E) (RS 61 C)) (DPNode
    (MkDag 10 (bs5 hbe h5e he5 hef h9e) R0 R0 (RS 92 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 10 (bs5 hcf
    hcf hcb hef h9e) R0 R0 R0 (RS 16 C)) (DPNode (MkDag 11 (bs5 haf hcb he7 hfe h79) R0 R0 (RS 24 E) R0) (DPNode
    (MkDag 12 (bs5 hbf hff hfe h5f h2f) R0 (RS 40 C) R0 R0) (DPNode (MkDag 10 (bs5 hfc hbe he5 hef h9e) (RS 71 D)
    R0 R0 (RS 72 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 10 (bs5 h7f he7 he5 hef h9e) (RS 56 D) R0 R0 R0)
    (DPNode (MkDag 14 (bs5 h9f h9f hfc hff h97) R0 (RS 3 A) R0 (RS 3 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    3 (bs5 h7c hbf h2f hfe h7c) (RS 5 D) R0 R0 R0) (DPNode (MkDag 13 (bs5 h3f hf3 hf9 hff h3c) R0 R0 R0 (RS 48 B))
    (DPNode (MkDag 0 (bs5 h3e h5e h7e h5f h2f) R0 R0 R0 (RS 101 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5
    hbe hf9 he5 hf9 h7c) R0 R0 (RS 64 E) R0) (DPNode (MkDag 11 (bs5 hfe h7f he7 hfe h79) R0 R0 R0 (RS 74 C))
    DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_23 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hb2 hf9 hef h97 he7) R0 (RS 1 C) R0 R0) (DPNode (MkDag 0 (bs5 hf2 hf9 hef h97 he7) R0
    (RS 2 C) R0 R0) (DPNode (MkDag 0 (bs5 hf2 hf9 hff h97 he7) R0 (RS 3 C) R0 R0) (DPNode (MkDag 0 (bs5 hf2 hf9 he7
    h97 he7) R0 (RS 5 C) R0 R0) (DPNode (MkDag 3 (bs5 hf2 hf7 h2f hbf he7) R0 (RS 9 C) R0 R0) (DPNode (MkDag 5 (bs5
    h9e h7c hbe h7d hcf) R0 (RS 17 A) R0 R0) (DPNode (MkDag 0 (bs5 h3d hfe h7f h97 he7) R0 R0 R0 (RS 33 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 1 (bs5 hbc hf9 hfc hfe he7) R0 R0 (RS 51 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5
    hfe h5f h3f hbf he7) R0 (RS 25 C) R0 R0) (DPNode (MkDag 1 (bs5 h7d hf2 hfc hfe he7) R0 R0 R0 (RS 41 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs5 hfc hf9 he5 hff he7) R0 R0 (RS 57 E) (RS 58 B)) DPEmpty DPEmpty))) (DPNode
    (MkDag 1 (bs5 hf3 hf9 h7c hfe he7) R0 (RS 13 C) R0 R0) (DPNode (MkDag 2 (bs5 hbe hff hfc hf3 he7) R0 (RS 21 C)
    R0 R0) (DPNode (MkDag 0 (bs5 h3f hfe h7f h97 he7) R0 R0 R0 (RS 37 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5
    haf hb9 hf9 hff he7) R0 R0 (RS 53 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 hfb h97 hdc hfe he7) (RS 28 D)
    R0 R0 (RS 29 A)) (DPNode (MkDag 0 (bs5 hbf hb9 hff h97 he7) R0 R0 (RS 45 E) R0) DPEmpty DPEmpty) (DPNode (MkDag
    3 (bs5 hef hf7 h2f hbf he7) (RS 60 D) R0 R0 (RS 61 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 1 (bs5 hf2 hf9 hfc
    hfe he7) R0 (RS 7 C) R0 R0) (DPNode (MkDag 3 (bs5 hf3 hf9 he5 hff he7) R0 (RS 11 C) R0 R0) (DPNode (MkDag 6
    (bs5 h9f hdc hfe h7e h5f) R0 (RS 19 C) R0 R0) (DPNode (MkDag 0 (bs5 h2f hfe h7f h97 he7) R0 R0 R0 (RS 35 C))
    DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h7f hf9 hfc hbe he7) R0 R0 R0 (RS 46 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hfe h5e h7f h97 he7) R0 (RS 27 B) R0 R0) (DPNode (MkDag 1 (bs5 hcb hf9 h7c hfe he7) R0 R0 R0 (RS
    43 D)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h79 hf9 h7c hf3 he7) R0 R0 R0 (RS 59 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 4 (bs5 hf2 hff hff h3d hcf) R0 R0 (RS 15 E) (RS 16 A)) (DPNode (MkDag 3 (bs5 he5 hf2 hf9 hff
    he7) R0 R0 R0 (RS 23 A)) (DPNode (MkDag 1 (bs5 he7 h9f hdc hbe he7) R0 R0 R0 (RS 39 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 3 (bs5 hbf hb9 hf9 hff he7) R0 R0 (RS 55 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 he5 hf7
    h3f hbf he7) R0 R0 R0 (RS 31 C)) (DPNode (MkDag 1 (bs5 hff hf9 hfc hbe he7) R0 R0 R0 (RS 47 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs5 hbc hf9 h79 hff he7) R0 R0 (RS 63 E) R0) DPEmpty DPEmpty))))) (DPNode (MkDag 1
    (bs5 hf2 hf9 hfc hbe he7) R0 (RS 4 C) R0 R0) (DPNode (MkDag 2 (bs5 hf2 hf9 hfc hf3 he7) R0 (RS 6 C) R0 R0)
    (DPNode (MkDag 1 (bs5 hf3 hf9 h7c hbe he7) R0 (RS 10 C) R0 R0) (DPNode (MkDag 6 (bs5 h97 hdc hfe h7e h5f) R0 R0
    R0 (RS 18 A)) (DPNode (MkDag 0 (bs5 haf hfe h7f h97 he7) R0 R0 (RS 34 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1
    (bs5 hef hf9 hfc hbe he7) R0 R0 R0 (RS 50 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hbe h5e h7f h97 he7) R0
    (RS 26 C) R0 R0) (DPNode (MkDag 1 (bs5 hfd hf2 hfc hfe he7) R0 R0 R0 (RS 42 D)) DPEmpty DPEmpty) (DPNode (MkDag
    3 (bs5 h7c hf9 he5 hff he7) R0 R0 R0 (RS 56 B)) DPEmpty DPEmpty))) (DPNode (MkDag 3 (bs5 hf3 hf9 h79 hff he7)
    R0 (RS 1 C) R0 R0) (DPNode (MkDag 2 (bs5 hfe hff hfc hf3 he7) R0 (RS 22 B) R0 R0) (DPNode (MkDag 2 (bs5 he7 hfe
    h7c hf3 he7) R0 R0 R0 (RS 38 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 h2f hb9 hf9 hff he7) R0 R0 R0 (RS 54
    C)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 h9f h97 hdc hfe he7) R0 (RS 30 B) R0 R0) (DPNode (MkDag 0 (bs5 h3f
    hb9 hff h97 he7) R0 R0 R0 (RS 49 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 h7f hf7 h2f hbf he7) (RS 56 C) R0
    R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 3 (bs5 hf2 hf9 hf9 hff he7) R0 (RS 8 C) R0 R0) (DPNode (MkDag 2 (bs5
    hf3 hf9 h7c hf3 he7) R0 (RS 12 C) R0 R0) (DPNode (MkDag 2 (bs5 hf3 hfc hbc hf3 he7) R0 (RS 20 C) R0 R0) (DPNode
    (MkDag 0 (bs5 hbf hfe h7f h97 he7) R0 R0 (RS 36 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h3c hf9 hfc hfe
    he7) R0 R0 R0 (RS 52 C)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 h7b h97 hdc hfe he7) R0 R0 R0 (RS 28 B))
    (DPNode (MkDag 3 (bs5 hcf hcf h2f hbf he7) R0 R0 R0 (RS 44 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hf9 hf9
    h7c hf3 he7) R0 R0 R0 (RS 62 C)) DPEmpty DPEmpty))) (DPNode (MkDag 4 (bs5 h72 hff hff h3d hcf) R0 R0 R0 (RS 14
    B)) (DPNode (MkDag 3 (bs5 hbe h5f h3f hbf he7) R0 (RS 24 C) R0 R0) (DPNode (MkDag 0 (bs5 he7 hf7 he7 h97 he7)
    R0 R0 R0 (RS 40 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 h3f hb9 hf9 hff he7) R0 R0 R0 (RS 60 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs5 hbd hfe h7f h97 he7) R0 R0 (RS 32 E) R0) (DPNode (MkDag 2 (bs5 he5 hf9 hfc hf3
    he7) R0 R0 R0 (RS 48 C)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs5 h3c hf9 h79 hff he7) R0 R0 R0 (RS 0 A)) DPEmpty
    DPEmpty)))))).

Definition dagTree_24 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 0 C) R0 R0) DPEmpty.

Definition dagTree_25 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 he7 h97 hcf hfc hbf h3c) (RS 0 D) R0 R0 (RS 1 B)) (DPNode (MkDag 0 (bs6 he7 h97 hcf h3c
    hbf h3c) (RS 1 D) R0 R0 (RS 2 B)) (DPNode (MkDag 0 (bs6 he7 h97 hcf he7 hf7 h3c) (RS 2 D) R0 R0 (RS 3 B))
    (DPNode (MkDag 0 (bs6 he7 h9f hcf h2f hff h3c) (RS 4 D) R0 R0 (RS 5 B)) (DPNode (MkDag 0 (bs6 he7 h97 hcf he7
    h9f h3c) (RS 8 D) R0 R0 (RS 9 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hf9 hfd hff h3c) (RS 16 D) R0 R0 (RS 17 B))
    (DPNode (MkDag 0 (bs6 hb9 hfd hcf hcf hff h3c) R0 R0 R0 (RS 33 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 hcf h3c hfe he5 hf7 h3c) R0 R0 R0 (RS 25 D)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he7 h9f hcb hcf hff
    h3c) (RS 12 D) R0 R0 (RS 0 B)) (DPNode (MkDag 0 (bs6 hff he5 hff hcf hff h3c) (RS 20 D) R0 R0 (RS 21 A))
    (DPNode (MkDag 0 (bs6 hf3 hff hb9 h7d hff h3c) (RS 36 D) R0 R0 (RS 37 D)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs6 hcb hff hcf he5 hf7 h3c) R0 R0 R0 (RS 29 D)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 he7 h97 hcf
    h7c hbf h3c) (RS 6 D) R0 R0 (RS 7 B)) (DPNode (MkDag 0 (bs6 he7 h9f hcb he5 hf7 h3c) (RS 10 D) R0 R0 (RS 11 B))
    (DPNode (MkDag 0 (bs6 he5 hfc hbe he7 hf7 h3c) (RS 18 D) R0 R0 (RS 19 A)) (DPNode (MkDag 0 (bs6 h79 hfd hcf hcf
    hff h3c) R0 R0 R0 (RS 33 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfe h7e h79 h7d hff h3c) R0 R0 (RS
    27 E) (RS 28 D)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he5 hf3 hff hcf hff h3c) (RS 14 D) R0 R0 (RS 15 B))
    (DPNode (MkDag 0 (bs6 h79 h7f hf3 hfc hbf h3c) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 0 (bs6 h79 he7 hcb hcf hff
    h3c) (RS 39 E) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hb9 he7 hcf he7 hf7 h3c) R0 (RS 31 C)
    R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs6 he7 h97 hb9 h7d hff h3c) (RS 3 D) R0 R0 (RS 4 B)) (DPNode
    (MkDag 0 (bs6 he7 h9f hcb he7 hf7 h3c) (RS 5 D) R0 R0 (RS 6 B)) (DPNode (MkDag 0 (bs6 he7 h97 hcf hcf hff h3c)
    (RS 9 D) R0 R0 (RS 10 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hf3 hfc hbf h3c) (RS 17 D) R0 R0 (RS 18 B)) (DPNode
    (MkDag 0 (bs6 hf9 hfd hcf hcf hff h3c) R0 R0 (RS 34 E) (RS 35 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 hcb hef h97 he7 hf7 h3c) R0 R0 R0 (RS 26 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he5 hf3 hfe he7 hf7
    h3c) (RS 13 D) R0 R0 (RS 14 B)) (DPNode (MkDag 0 (bs6 h9f h2f hb9 hfd hff h3c) R0 (RS 22 B) R0 R0) (DPNode
    (MkDag 0 (bs6 hcb hcf hcb he7 h9f h3c) R0 R0 R0 (RS 38 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hcf
    h2f hcf he7 h9f h3c) R0 R0 R0 (RS 30 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 he7 h97 hcf he5 hf7 h3c) (RS
    7 D) R0 R0 (RS 8 B)) (DPNode (MkDag 0 (bs6 he7 h9f hcb he7 h9f h3c) (RS 11 D) R0 R0 (RS 12 B)) (DPNode (MkDag 0
    (bs6 hbf he5 hff hcf hff h3c) R0 (RS 20 C) R0 R0) (DPNode (MkDag 0 (bs6 h9f h7f hb9 h7d hff h3c) R0 (RS 36 C)
    R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7e h7e h79 h7d hff h3c) R0 R0 R0 (RS 26 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 he5 hf3 hf9 he7 hf7 h3c) (RS 15 D) R0 R0 (RS 16 B)) (DPNode (MkDag 0 (bs6 hf9
    h7f hf3 hfc hbf h3c) (RS 23 D) R0 R0 (RS 24 D)) (DPNode (MkDag 0 (bs6 h67 h97 hcf hfc hbf h3c) R0 R0 R0 (RS 0
    B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hf9 he7 hcf he7 hf7 h3c) R0 (RS 32 A) R0 R0) DPEmpty
    DPEmpty))))).

Definition dagTree_26 : DagNTree :=
  MkDagNTree (MkDag 0 nil (RS 0 D) R0 R0 (RS 0 B)) DPEmpty.

Definition dagTree_27 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hbf h3f hff h3c hfe) R0 (RS 12 C) R0 R0) (DPNode (MkDag 0 (bs5 hf3 he7 h9e h7c hf3) R0
    R0 (RS 14 E) (RS 15 C)) (DPNode (MkDag 0 (bs5 he7 he5 hf7 hf9 hff) R0 R0 R0 (RS 7 A)) (DPNode (MkDag 0 (bs5 hdf
    h2f hff h3c hfe) R0 R0 R0 (RS 5 A)) (DPNode (MkDag 0 (bs5 h79 he5 hf7 hf9 hff) R0 R0 R0 (RS 9 B)) (DPNode
    (MkDag 0 (bs5 h3e he5 hf7 hf9 hff) R0 R0 R0 (RS 2 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hff h3f
    hff h3c hfe) R0 (RS 13 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hff h2f hff h3c hfe) (RS 6 D) R0 R0
    (RS 7 A)) (DPNode (MkDag 0 (bs5 h9f h3d hff h3c hfe) R0 (RS 11 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5
    h73 he7 h9e h7c hf3) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs5 h7f he7 h9e h7c hf3) (RS 4 D)
    R0 R0 R0) (DPNode (MkDag 0 (bs5 hbf h2f hff h3c hfe) R0 (RS 6 C) R0 R0) (DPNode (MkDag 0 (bs5 hf9 he5 hf7 hf9
    hff) (RS 9 D) R0 R0 (RS 10 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h9f h3c hbc hfc hbe) R0 R0 R0 (RS 1 C))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h9f h3c hbe h7f h97) R0 (RS 8 B) R0 R0) (DPNode (MkDag 0 (bs5 hf7 h3f
    hff h3c hfe) R0 (RS 0 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hbe he5 hf7 hf9 hff) R0 R0 (RS 16 E) R0)
    DPEmpty DPEmpty)))).

Definition dagTree_28 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h3d hcf hfc hfe h7c) R0 R0 R0 (RS 57 C)) (DPNode (MkDag 0 (bs5 h73 hcb he7 h9f hfc) R0
    R0 R0 (RS 8 B)) (DPNode (MkDag 1 (bs5 hbd hcf he7 hf3 he5) R0 (RS 66 C) R0 R0) (DPNode (MkDag 2 (bs5 h2f h9f
    h9e h7f he5) R0 R0 R0 (RS 54 C)) (DPNode (MkDag 0 (bs5 hf3 hcb he7 h9f hfc) (RS 8 D) (RS 3 C) (RS 1 E) (RS 3
    C)) (DPNode (MkDag 2 (bs5 h9e hf9 h7e h7f he5) R0 (RS 17 A) R0 R0) (DPNode (MkDag 2 (bs5 hbe h7f h9e h7f he5)
    R0 (RS 33 C) R0 R0) (DPNode (MkDag 1 (bs5 hbf hcf h3f hfe he5) R0 (RS 65 C) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 2 (bs5 h7e h7f h9e h7f he5) (RS 5 C) R0 R0 (RS 33 B)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5
    h9f hff h3d hfe he5) R0 (RS 25 B) R0 R0) (DPNode (MkDag 0 (bs5 h7d hcf he7 h9f hfc) (RS 41 D) R0 R0 (RS 6 B))
    DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hee h5e h79 hf9 he5) R0 R0 R0 (RS 28 B)) DPEmpty DPEmpty))) (DPNode
    (MkDag 1 (bs5 he7 hcf h3f hfe he5) R0 R0 R0 (RS 40 B)) (DPNode (MkDag 2 (bs5 h9f hcb hee h7e he5) R0 (RS 21 A)
    R0 R0) (DPNode (MkDag 2 (bs5 hcf h2f h9e h7e he5) (RS 36 D) R0 R0 (RS 38 C)) DPEmpty DPEmpty) (DPNode (MkDag 2
    (bs5 h3c hfb h9e h7f he5) R0 R0 R0 (RS 53 C)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 h7e h5e h79 hf9 he5) R0
    R0 R0 (RS 7 B)) (DPNode (MkDag 2 (bs5 he7 hcf he7 he7 he5) R0 R0 R0 (RS 45 B)) DPEmpty DPEmpty) (DPNode (MkDag
    0 (bs5 h3f hcf hfc hfe h7c) R0 R0 R0 (RS 61 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs5 hfd hcf he7 h9f hfc)
    R0 R0 R0 (RS 49 C)) (DPNode (MkDag 0 (bs5 hff h9f hff hf7 hfc) (RS 10 D) (RS 36 D) (RS 37 E) (RS 36 D)) (DPNode
    (MkDag 2 (bs5 h9f hf9 h7e h7f he5) R0 (RS 19 A) R0 R0) (DPNode (MkDag 0 (bs5 hbd hcf hfc hfe h7c) R0 (RS 5 C)
    (RS 0 E) R0) (DPNode (MkDag 1 (bs5 hfd hcf he7 hf3 he5) R0 (RS 67 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs5 h7f hcf he7 hf3 he5) R0 R0 R0 (RS 49 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hbe h5f h9e h7e
    he5) R0 (RS 27 C) R0 R0) (DPNode (MkDag 1 (bs5 hbf hcf he7 hf3 he5) R0 R0 (RS 43 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h2f hcf hfc hfe h7c) R0 R0 R0 (RS 59 C)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 hf2 hfc
    hf2 hff he5) R0 R0 (RS 15 E) (RS 16 A)) (DPNode (MkDag 1 (bs5 h9e hff h3d hfe he5) R0 (RS 23 A) R0 R0) (DPNode
    (MkDag 2 (bs5 hbf hfe h79 hf9 he5) R0 R0 (RS 39 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hbf h9f h9e h7f
    he5) R0 R0 (RS 55 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 h73 hcb he7 he7 he5) R0 R0 R0 (RS 3 B))
    (DPNode (MkDag 2 (bs5 hcf h9f h9e h7f he5) R0 R0 R0 (RS 8 C)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h9f h3f
    h9e h7e he5) R0 (RS 63 C) R0 R0) DPEmpty DPEmpty))))) (DPNode (MkDag 2 (bs5 hf3 hcb he7 he7 he5) R0 (RS 29 C)
    (RS 30 E) (RS 29 C)) (DPNode (MkDag 0 (bs5 hfd hcf hfc hfe h7c) R0 (RS 10 C) (RS 35 E) (RS 10 C)) (DPNode
    (MkDag 2 (bs5 h3e h7b h9e h7f he5) R0 R0 R0 (RS 47 B)) (DPNode (MkDag 2 (bs5 h97 hf9 h7e h7f he5) R0 R0 R0 (RS
    18 A)) (DPNode (MkDag 2 (bs5 hfe h7f h9e h7f he5) R0 (RS 34 C) R0 (RS 34 C)) (DPNode (MkDag 1 (bs5 hff hcf h3f
    hfe he5) R0 (RS 2 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hff hcf he7 hf3 he5) (RS 49 D) R0
    (RS 50 E) (RS 51 C)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 he5 hff he7 he7 he5) R0 R0 R0 (RS 26 A)) (DPNode
    (MkDag 0 (bs5 hcf hcf he7 h9f hfc) R0 R0 R0 (RS 42 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 haf hcf hfc hfe
    h7c) R0 R0 (RS 58 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 hbe h5e h79 hf9 he5) R0 (RS 7 C) R0 (RS 7 C))
    (DPNode (MkDag 1 (bs5 h9e h5f hff h97 he5) R0 R0 R0 (RS 22 A)) (DPNode (MkDag 0 (bs5 h7f h9f hff hf7 hfc) R0 R0
    R0 (RS 10 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 haf h9f h9e h7f he5) R0 R0 (RS 4 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs5 hbe h7b h9e h7f he5) R0 (RS 31 C) (RS 9 E) R0) (DPNode (MkDag 2 (bs5 h7c hfb h9e h7f he5)
    (RS 46 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 he7 h9f hff hf7 hfc) (RS 61 D) R0 R0 (RS 11 B))
    DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs5 hfe h5e h79 hf9 he5) R0 (RS 8 C) (RS 28 E) (RS 8 C)) (DPNode (MkDag 1
    (bs5 he7 hf7 h2f hfe he5) (RS 11 D) R0 R0 (RS 62 A)) (DPNode (MkDag 2 (bs5 h97 hcb hee h7e he5) R0 R0 R0 (RS 20
    A)) (DPNode (MkDag 0 (bs5 h7d hcf hfc hfe h7c) R0 R0 R0 (RS 5 B)) (DPNode (MkDag 2 (bs5 hff hcf he7 he7 he5) R0
    (RS 13 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hbc hfb h9e h7f he5) R0 R0 (RS 52 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hfe h5f h9e h7e he5) R0 (RS 13 C) R0 R0) (DPNode (MkDag 1 (bs5 h3f hcf
    he7 hf3 he5) R0 R0 R0 (RS 44 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hbf hcf hfc hfe h7c) R0 R0 (RS 60 E)
    R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 h72 hfc hf2 hff he5) R0 R0 R0 (RS 14 B)) (DPNode (MkDag 1 (bs5 h97
    hff h3d hfe he5) R0 R0 R0 (RS 24 A)) (DPNode (MkDag 2 (bs5 h3f hfe h79 hf9 he5) R0 R0 R0 (RS 12 B)) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs5 h3f h9f h9e h7f he5) R0 R0 R0 (RS 56 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5
    hfe h7b h9e h7f he5) R0 (RS 32 C) R0 R0) (DPNode (MkDag 2 (bs5 hee h7f h9e h7f he5) (RS 47 D) R0 R0 (RS 48 B))
    DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hf7 hcf h3f hfe he5) R0 (RS 64 C) R0 R0) DPEmpty DPEmpty)))))).

Definition dagTree_29 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h7b h9e h7f h9f h9f) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 1 (bs5 hf2 hf7 h3f h3f h2f) R0
    R0 (RS 35 E) (RS 36 C)) (DPNode (MkDag 2 (bs5 hf2 hff he5 hf7 h3c) (RS 2 D) R0 (RS 4 E) (RS 40 C)) (DPNode
    (MkDag 2 (bs5 h72 hff he5 hf7 h3c) R0 R0 R0 (RS 2 B)) (DPNode (MkDag 7 (bs5 h7d hf2 hfc hff hf9) R0 R0 R0 (RS
    28 B)) (DPNode (MkDag 10 (bs5 h7d hcb hcf hff hcb) R0 R0 R0 (RS 17 B)) (DPNode (MkDag 12 (bs5 h9e h79 he5 hf2
    hf9) R0 (RS 33 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs5 h7f hf9 he5 hf9 he5) R0 R0 R0 (RS 25
    B)) (DPNode (MkDag 3 (bs5 hf2 hf7 h3c hbf h3f) (RS 40 D) R0 (RS 3 E) (RS 36 C)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 8 (bs5 h2f hcb he7 h9f h3f) R0 R0 R0 (RS 13 C)) (DPNode (MkDag 0 (bs5 hf3 hee h5f hfe h7f) (RS
    20 D) R0 R0 (RS 21 C)) (DPNode (MkDag 11 (bs5 hf3 hff h3c hff hcf) (RS 36 D) R0 (RS 37 E) (RS 38 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs5 hfd hf2 hfc hff hf9) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty))) (DPNode
    (MkDag 5 (bs5 h7c hbf h3f hb9 he7) R0 R0 R0 (RS 26 B)) (DPNode (MkDag 8 (bs5 h3d hcb he7 h9f h3f) R0 R0 R0 (RS
    11 C)) (DPNode (MkDag 4 (bs5 hf9 hff hb9 hfd hcf) R0 R0 R0 (RS 19 A)) (DPNode (MkDag 1 (bs5 h7f hff h9e h5f
    h2f) (RS 1 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 hfc hbf h3f hb9 he7) R0 R0 R0 (RS 7 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5 h3f hcb he7 h9f h3f) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 0 (bs5 h3e h7e
    h5f hfe h7f) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 13 (bs5 hf3 hf7 h3f h3f h2f) (RS 38 D) R0 (RS 39 E) (RS 2 C))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h9f h9e h7f h9f h9f) R0 (RS 31 A) R0 R0) DPEmpty DPEmpty))))
    (DPNode (MkDag 3 (bs5 h72 hf7 h3c hbf h3f) R0 R0 R0 (RS 40 B)) (DPNode (MkDag 4 (bs5 h79 hff hb9 hfd hcf) R0 R0
    R0 (RS 18 B)) (DPNode (MkDag 8 (bs5 hbd hcb he7 h9f h3f) R0 R0 (RS 10 E) R0) (DPNode (MkDag 10 (bs5 hfd hcb hcf
    hff hcb) R0 R0 R0 (RS 5 B)) (DPNode (MkDag 3 (bs5 h9e h79 he7 hf3 hdf) R0 R0 R0 (RS 34 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 7 (bs5 hff hf9 he5 hf9 he5) R0 R0 R0 (RS 6 B)) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5
    hbf hcb he7 h9f h3f) R0 R0 (RS 14 E) R0) (DPNode (MkDag 0 (bs5 hbe h7e h5f hfe h7f) R0 R0 (RS 22 E) R0) (DPNode
    (MkDag 11 (bs5 h73 hff h3c hff hcf) R0 R0 R0 (RS 36 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfb h9e
    h7f h9f h9f) R0 R0 R0 (RS 30 A)) DPEmpty DPEmpty))) (DPNode (MkDag 6 (bs5 he7 h9f hdc hbf hf9) R0 R0 R0 (RS 27
    B)) (DPNode (MkDag 8 (bs5 haf hcb he7 h9f h3f) R0 R0 (RS 12 E) R0) (DPNode (MkDag 7 (bs5 h9f h3f hf3 hff hb9)
    R0 (RS 20 C) R0 R0) (DPNode (MkDag 1 (bs5 h72 hf7 h3f h3f h2f) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 11 (bs5 he7 hf7 he7 he7 h9f) R0 R0 R0 (RS 8 B)) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 he7 hcb
    he7 hf7 h3f) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 7 (bs5 hef hf9 he5 hf9 he5) R0 R0 R0 (RS 24 B)) (DPNode (MkDag
    13 (bs5 h73 hf7 h3f h3f h2f) R0 R0 R0 (RS 38 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 h9e h5e h7c
    hbe he7) R0 R0 R0 (RS 32 A)) DPEmpty DPEmpty))))).

Definition dagTree_30 : DagNTree :=
  MkDagNTree (MkDag 0 (bs2 hf3 hf9) R0 R0 (RS 13 E) (RS 1 D)) (DPNode (MkDag 1 (bs2 hcf h2f) R0 R0 R0 (RS 2 D))
    (DPNode (MkDag 2 (bs2 hcf h3f) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 4 (bs2 hcf h3f) R0 R0 R0 (RS 2 D)) (DPNode
    (MkDag 6 (bs2 h73 hf9) R0 R0 R0 (RS 7 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs2 h73 hf9) R0 R0 R0 (RS 11 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs2 h72 hf9) R0 R0 R0 (RS 5 B)) (DPNode (MkDag 7 (bs2 h73 hf9) R0 R0 R0 (RS
    9 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 3 (bs2 hcf h2f) R0 R0 R0 (RS 4 D)) (DPNode (MkDag 5 (bs2 hf2
    hf9) R0 R0 (RS 6 E) (RS 7 C)) (DPNode (MkDag 7 (bs2 hf3 hf9) R0 R0 (RS 10 E) (RS 11 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs2 h73 hf9) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs2 hf3 hf9) (RS 7 D) R0
    (RS 8 E) (RS 9 C)) (DPNode (MkDag 8 (bs2 hf3 hf9) (RS 11 D) R0 (RS 12 E) (RS 0 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_31 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 R0 R0 (RS 0 D)) DPEmpty.

Definition dagTree_32 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 he7 h9e h79 hf2 hf3 hff) (RS 0 D) (RS 1 A) R0 (RS 1 A)) (DPNode (MkDag 0 (bs6 h9e h79
    he5 hf3 hcf h2f) R0 (RS 2 A) R0 (RS 2 A)) (DPNode (MkDag 0 (bs6 h9e h79 he5 hee h5f h7f) R0 (RS 3 A) R0 (RS 3
    A)) (DPNode (MkDag 0 (bs6 h9e h79 he5 hf3 hf9 h7d) R0 (RS 5 A) R0 (RS 5 A)) (DPNode (MkDag 0 (bs6 h9e h79 he5
    hf3 hf9 hfd) R0 (RS 9 A) R0 (RS 9 A)) (DPNode (MkDag 0 (bs6 he5 hee h5f h73 hf3 hff) (RS 16 D) R0 R0 (RS 17 B))
    (DPNode (MkDag 0 (bs6 hbc hbc hff hf2 hf9 hfd) R0 (RS 33 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbc
    hbe h7f h72 hf3 hff) R0 R0 (RS 49 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he7 hf7 hff hf3 hf9 h7d) (RS
    24 D) R0 R0 (RS 25 B)) (DPNode (MkDag 0 (bs6 hf3 hee h79 hfe h5f h7f) R0 R0 (RS 41 E) (RS 42 C)) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 hbc hfe h7f h73 hf3 hff) R0 R0 (RS 57 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 0
    (bs6 h9e h79 he7 hf2 hf9 h7d) R0 (RS 13 A) R0 (RS 13 A)) (DPNode (MkDag 0 (bs6 he7 h9e h5f h72 hff h2f) (RS 20
    D) R0 R0 (RS 21 B)) (DPNode (MkDag 0 (bs6 hcf h9f hdf hf3 hf9 he7) R0 R0 R0 (RS 37 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 hbc hf3 hcb hf3 hf9 he7) R0 R0 (RS 53 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hbe h79
    hf3 hcb hff) R0 (RS 29 C) R0 R0) (DPNode (MkDag 0 (bs6 haf h3c hff hf2 hf9 h7d) R0 R0 (RS 45 E) R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h9e h79 he7 hf2 hf9 he7) R0 (RS 7 A) R0 (RS 7 A)) (DPNode (MkDag 0
    (bs6 h9e h79 he5 hf3 hdf h2f) R0 (RS 11 A) R0 (RS 11 A)) (DPNode (MkDag 0 (bs6 he5 hf3 hdf hf3 hf9 he7) (RS 18
    D) R0 R0 (RS 19 B)) (DPNode (MkDag 0 (bs6 h9f hfc hff h9e h5f h7f) R0 R0 R0 (RS 35 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 hbc hbc hff h73 hff h2f) R0 R0 (RS 51 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7c hf3 hdf
    hee h5f h7f) (RS 27 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbe h7e h79 hfe h5f h7f) R0 R0 (RS 43 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 hbc hfc hff hee h5f h7f) R0 R0 (RS 59 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 0
    (bs6 he7 h9e h7f h73 hff h2f) (RS 14 D) R0 R0 (RS 15 B)) (DPNode (MkDag 0 (bs6 he7 hf3 hff hf2 hf9 h7d) (RS 22
    D) R0 R0 (RS 23 B)) (DPNode (MkDag 0 (bs6 hf9 hf7 hcb hf3 hf3 hff) R0 (RS 39 A) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 hbc hfe h79 hf3 hf9 hfd) R0 R0 (RS 55 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7c hbe h7f
    h72 hf9 he7) (RS 31 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbf h3c hff hf2 hf9 h7d) R0 R0 (RS 47 E) R0) DPEmpty
    DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 h9e h79 he7 hf2 hf9 hfd) R0 (RS 4 A) R0 (RS 4 A)) (DPNode (MkDag 0
    (bs6 h9e h79 he5 hf3 hf3 hff) R0 (RS 6 A) R0 (RS 6 A)) (DPNode (MkDag 0 (bs6 h9e h79 he7 hf3 hcb hff) R0 (RS 10
    A) R0 (RS 10 A)) (DPNode (MkDag 0 (bs6 he7 h9f hdf hf2 hf9 hfd) (RS 17 D) R0 R0 (RS 18 B)) (DPNode (MkDag 0
    (bs6 hfc hbc hff hf2 hf9 hfd) R0 (RS 34 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3c hbe h7f h72 hf3
    hff) R0 R0 R0 (RS 50 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he7 he7 hcb hf3 hf9 he7) (RS 25 D) R0 R0 (RS
    26 B)) (DPNode (MkDag 0 (bs6 h73 hee h79 hfe h5f h7f) R0 R0 R0 (RS 40 B)) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs6 h3c hfe h7f h73 hf3 hff) R0 R0 R0 (RS 58 C)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h9e h79 he7 hf2 hf3
    hff) R0 (RS 1 A) R0 (RS 1 A)) (DPNode (MkDag 0 (bs6 he7 hf3 hdf hf2 hf9 h7d) (RS 21 D) R0 R0 (RS 22 B)) (DPNode
    (MkDag 0 (bs6 hb9 hf7 hcb hf3 hf3 hff) R0 (RS 38 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3c hf3 hcb
    hf3 hf9 he7) R0 R0 R0 (RS 54 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hfc hbe h79 hf3 hcb hff) (RS 29 D) R0
    R0 (RS 30 B)) (DPNode (MkDag 0 (bs6 h2f h3c hff hf2 hf9 h7d) R0 R0 R0 (RS 46 C)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 0 (bs6 h9e h79 he5 hf3 hff h2f) R0 (RS 8 A) R0 (RS 8 A)) (DPNode (MkDag 0 (bs6 h9e h79 he5 hf3
    hf9 he7) R0 (RS 12 A) R0 (RS 12 A)) (DPNode (MkDag 0 (bs6 he5 hf3 hff hf3 hf9 he7) (RS 19 D) R0 R0 (RS 20 B))
    (DPNode (MkDag 0 (bs6 h7f h9e h7f h73 hcf h2f) (RS 36 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3c
    hbc hff h73 hff h2f) R0 R0 R0 (RS 52 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hdc hbe h79 hf3 hcb hff) R0 R0
    R0 (RS 28 A)) (DPNode (MkDag 0 (bs6 h3e h7e h79 hfe h5f h7f) R0 R0 R0 (RS 44 C)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 h3c hfc hff hee h5f h7f) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf7 hcb
    hf3 hf9 he7) (RS 15 D) R0 R0 (RS 16 B)) (DPNode (MkDag 0 (bs6 he7 h9f hdf h73 hff h2f) (RS 23 D) R0 R0 (RS 24
    B)) (DPNode (MkDag 0 (bs6 h9f h3f hcb hf3 hf3 hff) R0 R0 R0 (RS 40 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6
    h3c hfe h79 hf3 hf9 hfd) R0 R0 R0 (RS 56 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hdc hbc hff hf2 hf9 hfd)
    R0 R0 R0 (RS 32 A)) (DPNode (MkDag 0 (bs6 h3f h3c hff hf2 hf9 h7d) R0 R0 R0 (RS 48 C)) DPEmpty DPEmpty)
    DPEmpty))))).

Definition dagTree_33 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 0 A) R0 (RS 0 A)) DPEmpty.

Definition dagSub_34_80 : DagPTree :=
  DPNode (MkDag 0 (bs6 hcf hfe h79 h7c hf3 hcf) R0 R0 R0 (RS 74 A)) (DPNode (MkDag 0 (bs6 hfc hfe h79 he5 hf2 hfb)
    (RS 16 D) R0 R0 (RS 158 B)) (DPNode (MkDag 0 (bs6 h5f h9f hf9 he7 hfe h5f) (RS 205 B) R0 R0 R0) (DPNode (MkDag
    0 (bs6 h5f h2f hb9 he7 hf2 hfb) (RS 65 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hf3 hf2 hf9 h7c hbe hff) (RS 128 D)
    R0 R0 (RS 129 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hbe h79 he7 hf3 hfb) (RS 3 D) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 h7e h7f hf9 he5 hfe h5f) (RS 11 C) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbc hfe h7f
    h3c hf3 hcf) R0 (RS 161 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he7 he7 hff) (RS 224 D) R0
    R0 (RS 5 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h9f h3e h79 he5 hfe h5f) R0 (RS 49 C) R0 R0) (DPNode
    (MkDag 0 (bs6 hf7 h3f hb9 he7 hf2 hfb) (RS 80 D) R0 R0 (RS 81 C)) (DPNode (MkDag 0 (bs6 h9f h9f hf9 hfc hbe
    hff) R0 (RS 145 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfb h97 hb9 he5 hfe h5f) (RS 208 D) R0 R0 (RS
    209 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hf2 hf9 he5 hf3 hcf) R0 R0 R0 (RS 113 B)) (DPNode (MkDag 0
    (bs6 h5e h7e h79 he7 h9e h5f) (RS 177 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hfb hfc
    hf9 he5 hf2 hfb) (RS 24 D) R0 R0 (RS 91 A)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he5 hf3 hcf) (RS 40 D) R0 R0 (RS
    35 B)) (DPNode (MkDag 0 (bs6 h5e h7f hf9 he5 hf3 hcf) (RS 73 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h5f h9e h79 h7c
    hf3 hcf) (RS 137 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hdc hf2 hf9 he5 hf2 hfb) R0 R0 R0 (RS 201
    A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hcf h3e h79 he7 h97 hff) R0 R0 R0 (RS 105 C)) (DPNode (MkDag 0 (bs6
    hdc hfc hf9 he7 hbe h5f) R0 R0 R0 (RS 169 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf9 he5 hf9 he5 hf3 hcf)
    R0 (RS 233 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h9f he5 hf9 he5 hf3 hcf) R0 (RS 57 C) R0 R0)
    (DPNode (MkDag 0 (bs6 h7f hfc hf9 he7 hbe h5f) (RS 89 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hdc hfe h79 he7 hbe
    h5f) R0 R0 R0 (RS 153 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h79 h7f hf9 he5 hfe h5f) R0 R0 R0 (RS 217 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 hef hf9 he5 he7 hff) (RS 120 D) R0 R0 (RS 121 A)) (DPNode (MkDag 0
    (bs6 hfb he5 hf9 he5 hf3 hfb) (RS 184 D) R0 R0 (RS 185 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_81 : DagPTree :=
  DPNode (MkDag 0 (bs6 h5f hfe h79 he7 hfe h5f) (RS 102 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hbe h79 he7 h97 hff)
    (RS 195 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 he7 hf7 hf9 he7 hbe h5f) (RS 36 D) R0 R0 (RS 13 B)) (DPNode (MkDag 0
    (bs6 h5f h3c hf9 hfc hbe hff) (RS 69 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hdf h9e h79 he5 hf2 hfb) R0 R0 R0 (RS
    133 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he7 hbe h5f) R0 (RS 0 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hcb hee h5f h3c hf3 hcf) (RS 100 D) R0 R0 (RS 101 B)) (DPNode (MkDag 0 (bs6 hfc hfe h79
    h7c hf3 hcf) R0 (RS 165 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbc hff hf9 he7 hbe h5f) R0 (RS 229 C)
    R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hcf h3f hb9 hfc hf3 hcf) R0 R0 R0 (RS 53 D)) (DPNode (MkDag 0
    (bs6 hcf hef hf9 he5 hf3 hcf) R0 R0 R0 (RS 85 D)) (DPNode (MkDag 0 (bs6 hbc hf3 hf9 h7c hf3 hcf) R0 (RS 149 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hcb he7 hb9 he7 hf3 hcf) R0 R0 R0 (RS 21 D)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h9f he7 hf9 he7 hf3 hcf) R0 (RS 117 C) R0 R0) (DPNode (MkDag 0 (bs6 h7f hfc hf9 he7 he7
    hff) (RS 181 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h79 he5 hf9 he5 hf3 hcf) (RS 173 B)
    R0 R0 R0) (DPNode (MkDag 0 (bs6 h7f hfc hf9 hfc hbe hff) (RS 45 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hb9 hfe h79
    he5 hf3 hfb) R0 R0 R0 (RS 77 C)) (DPNode (MkDag 0 (bs6 hfb h9f hcf h3c hf3 hcf) R0 (RS 15 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 h7b h9f hf9 he7 hfe h5f) (RS 32 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 h3c hf2 hf9 he7 he7 hff) R0 R0 R0 (RS 109 C)) (DPNode (MkDag 0 (bs6 hf9 h7f hf9 hfc hbe hff) (RS 172 D) R0
    R0 (RS 231 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbf h3f h9f h3c hf3 hcf) R0 R0 (RS 237 E) R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 0 (bs6 hcb hee h79 he5 hfe h5f) R0 R0 R0 (RS 61 B)) (DPNode (MkDag 0 (bs6 h9e h7f hf9
    he7 hfe h5f) R0 R0 R0 (RS 93 B)) (DPNode (MkDag 0 (bs6 hfc hfe h79 hfc hf3 hcf) R0 (RS 157 B) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs6 he5 hee h79 hfc hbe hff) (RS 220 D) R0 R0 (RS 221 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 h73 hf2 hf9 he7 h9e h5f) R0 R0 R0 (RS 123 B)) (DPNode (MkDag 0 (bs6 hbc hbe h5f h3c hf3 hcf) R0
    (RS 189 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_82 : DagPTree :=
  DPNode (MkDag 0 (bs6 hcf h3f hb9 he5 hf2 hfb) R0 R0 R0 (RS 84 D)) (DPNode (MkDag 0 (bs6 hcf h3e h79 he5 hfe h5f)
    R0 R0 R0 (RS 29 D)) (DPNode (MkDag 0 (bs6 hfc hf2 hf9 he5 he7 hff) (RS 34 D) R0 R0 (RS 204 B)) (DPNode (MkDag 0
    (bs6 h79 h7f hf9 he7 hf3 hcf) (RS 67 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h5f h72 hf9 he5 hf3 hfb) (RS 131 B) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hbe h79 h7c hbe hff) (RS 194 D) R0 R0 (RS 20 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 hb9 h7e h79 hfc hbe hff) R0 (RS 99 C) R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79
    he7 h9e h5f) (RS 27 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf7 hf9 he7 hbe h5f) (RS 227 D) R0
    R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hbe h7e h79 he5 hf3 hfb) R0 R0 (RS 51 E) R0) (DPNode (MkDag 0
    (bs6 h3f h3f hb9 he7 hf2 hfb) R0 R0 R0 (RS 83 A)) (DPNode (MkDag 0 (bs6 h7c hf3 hf9 he7 h9e h5f) (RS 147 D) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7f h9f hf9 he7 h97 hff) R0 R0 R0 (RS 211 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 he7 h9f hb9 he7 hf3 hfb) (RS 114 D) R0 R0 (RS 115 B)) (DPNode (MkDag 0 (bs6 hbb hfc hf9
    he7 hbe h5f) R0 (RS 179 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hfc hf3 hf9 he5 hfe h5f)
    (RS 26 D) R0 R0 (RS 151 B)) (DPNode (MkDag 0 (bs6 h7b hfc hf9 hfc hbe hff) (RS 43 B) R0 R0 R0) (DPNode (MkDag 0
    (bs6 hb9 hee h79 he5 hf3 hfb) R0 (RS 75 C) R0 R0) (DPNode (MkDag 0 (bs6 hcf h9e h79 he5 hf3 hfb) R0 R0 R0 (RS
    139 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf2 hf9 he5 hf2 hfb) R0 (RS 203 B) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h3c hf2 hf9 he7 hf2 hfb) R0 R0 R0 (RS 107 C)) (DPNode (MkDag 0 (bs6 h7f h2f hb9 hfc hf3
    hcf) (RS 171 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf7 h3f h9f h3c hf3 hcf) R0 R0 (RS 235 E) (RS
    236 C)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hbf h2f h9f h3c hf3 hcf) R0 R0 (RS 59 E) R0) (DPNode (MkDag 0
    (bs6 hbb hfc hf9 he5 hf2 hfb) R0 (RS 24 C) R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79 he7 hf3 hcf) (RS 2 D) R0 R0
    R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hb9 he5 hf9 he5 hf3 hfb) R0 (RS 219 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hf9 hff hf9 he5 he7 hff) R0 (RS 14 A) R0 R0) (DPNode (MkDag 0 (bs6 h7c hbe h79 hfc hbe
    hff) R0 R0 R0 (RS 31 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_83 : DagPTree :=
  DPNode (MkDag 0 (bs6 h9f h72 hf9 he7 h9e h5f) R0 R0 R0 (RS 123 C)) (DPNode (MkDag 0 (bs6 he7 hee h79 he7 hfe h5f)
    (RS 22 D) R0 R0 (RS 222 B)) (DPNode (MkDag 0 (bs6 hcb hcf hb9 hfc hf3 hcf) R0 R0 R0 (RS 213 C)) (DPNode (MkDag
    0 (bs6 h5f h3f hb9 he5 hf2 hfb) (RS 71 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hff h9e h79 he5 hf2 hfb) (RS 134 D)
    R0 R0 (RS 135 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf2 hf9 he7 hf3 hcf) (RS 198 D) R0 R0 (RS 199 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7f hfe h79 he7 hfe h5f) (RS 103 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hfc
    hfe h79 he5 hfe h5f) (RS 166 D) R0 R0 (RS 167 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f h2f hb9 hfc hf3
    hcf) R0 (RS 171 B) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hbb he5 hf9 he5 hf3 hcf) R0 (RS 55 C) R0 R0)
    (DPNode (MkDag 0 (bs6 h7b hfc hf9 he7 hbe h5f) (RS 87 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hf3 hf9 he5 hfe
    h5f) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hbc hf9 he5 hf2 hfb) R0 R0 R0 (RS 213 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hf9 hf9 hfc hf3 hcf) R0 (RS 119 B) R0 R0) (DPNode (MkDag 0 (bs6 hcf
    h3f hb9 h7c hbe hff) R0 R0 R0 (RS 30 D)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hcf hef hf9 he5 hfe
    h5f) R0 R0 R0 (RS 183 A)) (DPNode (MkDag 0 (bs6 hb9 hfe h79 h7c hf3 hcf) R0 (RS 47 C) R0 R0) (DPNode (MkDag 0
    (bs6 h79 hfe h79 he5 hf3 hfb) R0 R0 R0 (RS 77 B)) (DPNode (MkDag 0 (bs6 hcf h97 hb9 hfc hf3 hcf) R0 R0 R0 (RS
    143 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hcf h9f hb9 he7 hf3 hfb) R0 R0 R0 (RS 207 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h3c hf2 hf9 hfc hbe hff) R0 R0 R0 (RS 111 C)) (DPNode (MkDag 0 (bs6 h7f h3c hf9 he5 he7
    hff) (RS 175 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbe h7e h79 he7 h9e h5f) R0 (RS 239 C) R0 R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h5f hfe h79 he5 hf3 hfb) (RS 63 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h5f
    h3f hb9 h7c hbe hff) (RS 95 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79 he5 he7 hff) (RS 159 D) R0 R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he5 hee h79 he7 h97 hff) (RS 222 D) R0 R0 (RS 23 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hf9 hf2 hf9 h7c hf3 hcf) R0 R0 R0 (RS 127 A)) (DPNode (MkDag 0 (bs6 h7c hbe h79 he7 hfe
    h5f) R0 R0 R0 (RS 191 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_84 : DagPTree :=
  DPNode (MkDag 0 (bs6 hfe h7f hf9 he7 hf3 hcf) (RS 9 D) R0 R0 (RS 10 D)) (DPNode (MkDag 0 (bs6 hfc hfc hf9 he7 hbe
    h5f) (RS 17 D) R0 R0 (RS 170 B)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 hfc hbe hff) (RS 33 D) R0 R0 (RS 225 B))
    (DPNode (MkDag 0 (bs6 h7f h2f hb9 he7 hf2 hfb) (RS 66 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h79 hf2 hf9 he7 h97
    hff) (RS 130 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbc hbe h79 h7c hbe hff) R0 (RS 194 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7f hfe h79 he7 hf2 hfb) R0 R0 R0 (RS 11 B)) (DPNode (MkDag 0 (bs6 hfc
    hfe h7f h3c hf3 hcf) (RS 161 D) R0 R0 (RS 162 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he5 hf2
    hfb) (RS 225 D) R0 R0 (RS 40 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hf3 hee h79 he5 hf3 hfb) (RS 49 D) R0
    R0 (RS 50 C)) (DPNode (MkDag 0 (bs6 hbf h3f hb9 he7 hf2 hfb) R0 R0 (RS 82 E) R0) (DPNode (MkDag 0 (bs6 h7f h9f
    hb9 he5 hf3 hcf) R0 R0 R0 (RS 7 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f h97 hb9 he5 hfe h5f) R0 (RS 210
    B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 he7 h9e hf9 he7 hfe h5f) (RS 113 D) R0 R0 (RS 114 B)) (DPNode
    (MkDag 0 (bs6 h7e h7e h79 he7 h9e h5f) (RS 18 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6
    hfb h9f hf9 hfc hbe hff) (RS 25 D) R0 R0 (RS 144 A)) (DPNode (MkDag 0 (bs6 he7 h9f hb9 he5 hfe h5f) (RS 41 D)
    R0 R0 (RS 226 B)) (DPNode (MkDag 0 (bs6 h7e h7f hf9 he5 hf3 hcf) (RS 8 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7f
    h9e h79 h7c hf3 hcf) (RS 138 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he5 hf2 hfb) R0
    (RS 202 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he7 hf2 hfb) R0 R0 (RS 106 E) R0) (DPNode
    (MkDag 0 (bs6 hbc hfc hf9 he7 hbe h5f) R0 (RS 17 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f h3c hf9
    he5 he7 hff) R0 R0 R0 (RS 234 C)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hf7 h2f h9f h3c hf3 hcf) (RS 57 D)
    R0 R0 (RS 58 C)) (DPNode (MkDag 0 (bs6 hcf hfc hf9 he7 he7 hff) R0 R0 R0 (RS 90 A)) (DPNode (MkDag 0 (bs6 hbc
    hfe h79 he7 hbe h5f) R0 (RS 6 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf9 h7f hf9 he5 hfe h5f) R0 R0
    R0 (RS 218 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hb9 hff hf9 he5 he7 hff) R0 (RS 122 C) R0 R0) (DPNode
    (MkDag 0 (bs6 h9f he5 hf9 he5 hf3 hfb) R0 (RS 186 B) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_85 : DagPTree :=
  DPNode (MkDag 0 (bs6 he7 he7 hb9 he7 hf3 hcf) (RS 13 D) R0 R0 (RS 116 A)) (DPNode (MkDag 0 (bs6 hcb he7 hf9 he7
    hf3 hcf) R0 R0 R0 (RS 38 D)) (DPNode (MkDag 0 (bs6 he7 h97 hb9 he7 hf3 hfb) (RS 37 D) R0 R0 (RS 41 B)) (DPNode
    (MkDag 0 (bs6 h7f h3c hf9 hfc hbe hff) (RS 70 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbf h9e h79 he5 hf2 hfb) R0
    (RS 134 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf2 hf9 he7 hf3 hcf) R0 R0 R0 (RS 198 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 h7b hfe h79 he7 hfe h5f) (RS 12 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79
    he5 hfe h5f) R0 R0 R0 (RS 166 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hff hf9 he7 hbe h5f) (RS 229 D) R0
    R0 (RS 230 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hcf hef hf9 hfc hbe hff) R0 R0 R0 (RS 54 A)) (DPNode
    (MkDag 0 (bs6 hcb hee h79 he5 hf3 hfb) (RS 85 D) R0 R0 (RS 86 B)) (DPNode (MkDag 0 (bs6 hfc hf3 hf9 h7c hf3
    hcf) R0 (RS 150 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfc hbc hf9 he5 hf2 hfb) R0 R0 (RS 214 E) (RS
    215 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hcf hb9 hfc hf3 hcf) R0 (RS 118 C) R0 R0) (DPNode (MkDag 0
    (bs6 hcf hfc hf9 he5 hf2 hfb) R0 R0 R0 (RS 182 D)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hcf hee
    h79 he5 hf3 hfb) R0 R0 R0 (RS 178 A)) (DPNode (MkDag 0 (bs6 hcf hfc hf9 he5 he7 hff) R0 R0 R0 (RS 46 A))
    (DPNode (MkDag 0 (bs6 hf9 hfe h79 he5 hf3 hfb) R0 R0 (RS 78 E) (RS 79 A)) (DPNode (MkDag 0 (bs6 h7f h9f hb9 he7
    hf2 hfb) (RS 142 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7f h9f hf9 he7 hfe h5f) (RS 206 D) R0 R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 hfc hbe hff) R0 R0 (RS 110 E) R0) (DPNode (MkDag 0 (bs6
    h5f h3c hf9 he5 he7 hff) (RS 174 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3f h3f h9f h3c hf3 hcf)
    R0 R0 R0 (RS 238 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h7b hfe h79 he5 hf3 hfb) (RS 62 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs6 h7f h3c hf9 h7c hf3 hcf) (RS 94 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79 he5 hf2
    hfb) R0 R0 R0 (RS 16 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 hfe h79 he5 hf3 hcf) (RS 221 D) R0 R0 (RS
    22 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h79 hf2 hf9 h7c hf3 hcf) R0 R0 R0 (RS 126 B)) (DPNode (MkDag 0
    (bs6 hfc hbe h5f h3c hf3 hcf) R0 (RS 190 B) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_86 : DagPTree :=
  DPNode (MkDag 0 (bs6 hff hfe h79 he7 hf2 hfb) R0 R0 (RS 97 E) (RS 98 A)) (DPNode (MkDag 0 (bs6 h9f hfc hf9 he7
    hbe h5f) R0 R0 R0 (RS 180 B)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he5 he7 hff) (RS 35 D) R0 R0 (RS 37 B)) (DPNode
    (MkDag 0 (bs6 h79 he5 hf9 hfc hf3 hcf) (RS 68 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7f h72 hf9 he5 hf3 hfb) (RS
    132 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hdc hf2 hf9 he7 hbe h5f) R0 R0 R0 (RS 196 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 h7e h79 hfc hbe hff) R0 (RS 100 D) R0 R0) (DPNode (MkDag 0 (bs6 hbc hfe h79
    h7c hf3 hcf) R0 (RS 164 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hdc hff hf9 he7 hbe h5f) R0 R0 R0 (RS
    228 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h3e h7e h79 he5 hf3 hfb) R0 R0 R0 (RS 52 D)) (DPNode (MkDag 0
    (bs6 hbe h7f hf9 he7 hf3 hcf) R0 (RS 9 C) R0 R0) (DPNode (MkDag 0 (bs6 hdc hf3 hf9 h7c hf3 hcf) R0 R0 R0 (RS
    148 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hff h9f hf9 he7 h97 hff) (RS 211 D) R0 R0 (RS 212 D)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 he7 h9f hf9 he7 h97 hff) (RS 115 D) R0 R0 (RS 36 B)) (DPNode (MkDag 0 (bs6 hfb
    hfc hf9 he7 hbe h5f) R0 (RS 19 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hdc hfe h79 h7c hf3
    hcf) R0 R0 R0 (RS 163 A)) (DPNode (MkDag 0 (bs6 h5f hfc hf9 hfc hbe hff) (RS 44 B) R0 R0 R0) (DPNode (MkDag 0
    (bs6 hf9 hee h79 he5 hf3 hfb) R0 (RS 76 A) R0 R0) (DPNode (MkDag 0 (bs6 hbb h9f hcf h3c hf3 hcf) R0 (RS 140 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf2 hf9 he5 he7 hff) R0 R0 R0 (RS 34 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he7 he7 hff) R0 R0 (RS 108 E) R0) (DPNode (MkDag 0 (bs6 h79 h7f hf9 hfc hbe
    hff) (RS 28 B) R0 R0 (RS 172 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h77 h3f h9f h3c hf3 hcf) R0 R0 R0 (RS
    234 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h3f h2f h9f h3c hf3 hcf) R0 R0 R0 (RS 60 D)) (DPNode (MkDag 0
    (bs6 h9f hfc hf9 he5 hf2 hfb) R0 (RS 92 A) R0 R0) (DPNode (MkDag 0 (bs6 hbc hfe h79 hfc hf3 hcf) R0 (RS 156 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hf9 he5 hf9 he5 hf3 hfb) (RS 219 D) R0 R0 (RS 220 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 hf3 hf2 hf9 he7 h9e h5f) R0 R0 (RS 124 E) (RS 125 B)) (DPNode (MkDag 0 (bs6 h7c
    hbe h79 he5 hf3 hcf) (RS 4 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_34_87 : DagPTree :=
  DPNode (MkDag 0 (bs6 h9f h9f hcf h3c hf3 hcf) R0 R0 R0 (RS 141 B)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he7 hf2 hfb)
    (RS 23 D) R0 R0 (RS 223 B)) (DPNode (MkDag 0 (bs6 h5e h7f hf9 he5 hfe h5f) (RS 96 B) R0 R0 R0) (DPNode (MkDag 0
    (bs6 h7f h3f hb9 he5 hf2 hfb) (RS 72 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7b h9e h79 h7c hf3 hcf) (RS 136 B) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf2 hf9 hfc hf3 hcf) (RS 200 D) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h79 h7e h79 h7c hbe hff) (RS 104 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hfe h79 he5 hf3
    hfb) (RS 168 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hb9 he5 hf9 he5 hf3 hcf) R0 (RS 232 C) R0 R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 hfb he5 hf9 he5 hf3 hcf) (RS 55 D) R0 R0 (RS 56 A)) (DPNode (MkDag 0
    (bs6 h5f hfc hf9 he7 hbe h5f) (RS 88 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c hf3 hf9 he5 hf3 hfb) (RS 152 D) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f hf9 hf9 he5 hf3 hcf) R0 (RS 216 B) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h79 hef hf9 he5 he7 hff) R0 R0 R0 (RS 120 B)) (DPNode (MkDag 0 (bs6 hbb he5 hf9 he5 hf3
    hfb) R0 (RS 184 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hfc hbe h79 hfc hbe hff) (RS 31 D)
    R0 R0 (RS 187 B)) (DPNode (MkDag 0 (bs6 hf9 hfe h79 h7c hf3 hcf) (RS 47 D) R0 R0 (RS 48 A)) (DPNode (MkDag 0
    (bs6 h9f h3c hf9 he7 hbe h5f) R0 (RS 80 C) R0 R0) (DPNode (MkDag 0 (bs6 hbb h9f hf9 hfc hbe hff) R0 (RS 25 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hbb h97 hb9 he5 hfe h5f) R0 (RS 208 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he5 hf3 hcf) R0 R0 (RS 112 E) R0) (DPNode (MkDag 0 (bs6 h5f h3f h9f h3c hf3
    hcf) (RS 1 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 hfe h7e h79 he7 h9e h5f) R0 (RS 85 D) R0 R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h7f hfe h79 he5 hf3 hfb) (RS 64 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7f
    h3f hb9 h7c hbe hff) (RS 39 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hdc hfe h7f h3c hf3 hcf) R0 R0 R0 (RS 160 A))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he7 hf3 hcf) (RS 223 D) R0 R0 (RS 224 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs6 h9f h72 hf9 h7c hbe hff) R0 (RS 128 C) R0 R0) (DPNode (MkDag 0 (bs6 hfc hbe h79 he7 hfe
    h5f) (RS 191 D) R0 R0 (RS 192 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_34 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hfc hf2 hf9 he7 hbe h5f) R0 (RS 197 B) R0 R0) (DPNode (MkDag 0 (bs6 h7f h3f h9f h3c hf3
    hcf) (RS 176 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hdc hfe h79 hfc hf3 hcf) R0 R0 R0 (RS 155 A)) (DPNode (MkDag 0
    (bs6 hdc hbe h5f h3c hf3 hcf) R0 R0 R0 (RS 188 A)) dagSub_34_80 dagSub_34_81) (DPNode (MkDag 0 (bs6 hfc hfe h79
    he7 hbe h5f) (RS 6 D) R0 R0 (RS 154 B)) dagSub_34_82 dagSub_34_83)) (DPNode (MkDag 0 (bs6 hdc hbe h79 h7c hbe
    hff) R0 R0 R0 (RS 193 A)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 hfc hf3 hcf) (RS 5 D) R0 R0 (RS 33 B)) dagSub_34_84
    dagSub_34_85) (DPNode (MkDag 0 (bs6 hff h9f hb9 he5 hf3 hcf) (RS 7 D) R0 R0 (RS 146 B)) dagSub_34_86
    dagSub_34_87))).

Definition dagTree_35 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hff hcf hff h3f h3c hbc) R0 R0 (RS 95 E) (RS 96 C)) (DPNode (MkDag 1 (bs6 hfc hfb h9f
    hf9 hff h9e) R0 (RS 11 D) (RS 94 E) (RS 11 D)) (DPNode (MkDag 2 (bs6 hfe h7b h9f hb9 hfb h9f) R0 (RS 111 C) R0
    R0) (DPNode (MkDag 4 (bs6 h9f hcf h3e h79 he5 hff) R0 R0 R0 (RS 108 A)) (DPNode (MkDag 6 (bs6 hcf he5 hf3 hf9
    hfc hf2) R0 R0 R0 (RS 52 D)) (DPNode (MkDag 10 (bs6 h2f hb9 h7c hbc hfc hff) R0 R0 R0 (RS 17 C)) (DPNode (MkDag
    16 (bs6 h7e h5f h3c hbf h3f h3f) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 29 (bs6 hcf h2f h9e h79 hfb h97) R0 R0 R0
    (RS 65 D)) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs6 hbd hcf he7 h97 he7 h97) R0 R0 (RS 97 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 24 (bs6 hcf hff h3c hf3 hcf h73) R0 R0 R0 (RS 49 D)) (DPNode (MkDag 4 (bs6 hf3 hcf h3e
    h79 he5 hff) R0 (RS 81 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hbc hfb h9f hf9 hff h9e) R0 (RS 1 C) R0
    R0) DPEmpty DPEmpty))) (DPNode (MkDag 13 (bs6 h3c hf9 he7 h9f hdc hfe) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 20
    (bs6 h3e h79 h7f hf9 hfc hbe) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 3 (bs6 hb9 he7 h9f h9f h3c hf3) R0 (RS 73 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h9e h79 hfe h79 hfb h9f) R0 R0 R0 (RS 105 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 1 (bs6 hcf he5 hf3 hf9 hff h9e) R0 R0 R0 (RS 57 D)) (DPNode (MkDag 7 (bs6 h73 hdf h97 hb9 hff
    he7) R0 R0 R0 (RS 87 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs6 he5 hf9 h7c hf3 he5 he7) (RS 12 D)
    R0 R0 (RS 13 C)) (DPNode (MkDag 11 (bs6 h7f hf9 h7c hf3 hcb hff) R0 R0 R0 (RS 21 B)) (DPNode (MkDag 18 (bs6 h7e
    h7f h3c hbf h2f h97) (RS 37 C) R0 R0 R0) (DPNode (MkDag 36 (bs6 hf9 he7 h9f hff hef hf3) R0 (RS 69 A) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 38 (bs6 hbf hcf he7 h97 he7 h97) R0 R0 (RS 101 E) R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs6 hcf he5 hf3 hf9 hfb h9f) R0 R0 R0 (RS 53 D)) (DPNode (MkDag 38 (bs6 h9f hf9 h7e h5e he7 h97) R0
    R0 R0 (RS 85 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs6 h3f hb9 he7 hee h5f h9f) R0 R0 R0 (RS 29 B))
    (DPNode (MkDag 22 (bs6 hbe h5f h3f hbf he7 h9f) R0 R0 (RS 45 E) R0) (DPNode (MkDag 37 (bs6 h7e h5f h9f hcb hdc
    hfe) R0 R0 R0 (RS 75 B)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h97 hcf hee h7f h3c hf3) R0 (RS 3 A) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hcf he5 hf3 hf7 h3c hbc) R0 R0 R0 (RS 61 D)) (DPNode (MkDag 2 (bs6 hee
    h7f h9f hb9 hfb h9f) R0 R0 R0 (RS 93 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 2 (bs6 hfe h7f h9f hb9 hfb
    h9f) R0 (RS 112 C) R0 R0) (DPNode (MkDag 7 (bs6 hf3 hff h97 hb9 hff he7) R0 (RS 89 C) (RS 90 E) (RS 89 C))
    (DPNode (MkDag 10 (bs6 h3f hb9 h7c hbc hfc hff) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 17 (bs6 h3e h5e he5 hf7 h2f
    hf2) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 35 (bs6 hcf h3c hf3 hf9 h7c hf3) R0 R0 R0 (RS 67 A)) DPEmpty DPEmpty)
    (DPNode (MkDag 38 (bs6 haf hcf he7 h97 he7 h97) R0 R0 (RS 99 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 hcf
    he5 hf3 hf9 hff he7) R0 R0 R0 (RS 51 D)) (DPNode (MkDag 38 (bs6 h9e hf9 h7e h5e he7 h97) R0 R0 R0 (RS 83 A))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs6 h2f hb9 he7 hee h5f h9f) R0 R0 R0 (RS 27 C)) (DPNode (MkDag
    21 (bs6 h7e h5f h3c hf9 he7 h97) R0 R0 R0 (RS 43 B)) (DPNode (MkDag 37 (bs6 hbe h5f h9f hcb hdc hfe) R0 R0 R0
    (RS 75 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9e h7e h7e h79 hff h9e) R0 R0 R0 (RS 107 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 30 (bs6 hcf he5 hf3 hf9 h7c hf3) R0 R0 R0 (RS 59 D)) (DPNode (MkDag 7 (bs6 h73 hff h97
    hb9 hff he7) R0 R0 R0 (RS 10 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 9 (bs6 h3c hf9 h7c hbe h7c hbd) R0
    R0 R0 (RS 15 C)) (DPNode (MkDag 12 (bs6 he5 hf9 h7c hfe h7f h9e) R0 R0 R0 (RS 23 C)) (DPNode (MkDag 19 (bs6 h7e
    h7e he7 hf7 h2f h97) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 27 (bs6 hf9 he7 h9f hf9 he7 h9f) R0 R0 (RS 71 E) (RS 72
    A)) DPEmpty DPEmpty) (DPNode (MkDag 40 (bs6 he7 h9f h9f hcb he7 h97) (RS 102 D) R0 R0 (RS 103 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 17 (bs6 hcf he5 hf3 hf9 h7d hf2) R0 R0 R0 (RS 55 D)) (DPNode (MkDag 39 (bs6 h9e h5f
    h7c hf2 hf9 hee) R0 R0 R0 (RS 87 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 15 (bs6 h7f hff hff h3f h2f h9f)
    (RS 31 C) R0 R0 R0) (DPNode (MkDag 23 (bs6 hee h5e h7f h97 he7 he7) (RS 46 D) R0 R0 (RS 47 B)) (DPNode (MkDag
    17 (bs6 h9e h5f h3e h79 h7d hf2) R0 R0 R0 (RS 79 A)) DPEmpty DPEmpty) (DPNode (MkDag 23 (bs6 h9e h79 h7b h97
    hcb he7) R0 (RS 87 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 22 (bs6 hcf he5 hf3 hff h97 h9e) R0 R0 R0 (RS 63
    D)) (DPNode (MkDag 1 (bs6 h7c hfb h9f hf9 hff h9e) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty))))) (DPNode
    (MkDag 3 (bs6 h9f hcf hee h7f h3c hf3) R0 R0 R0 (RS 109 A)) (DPNode (MkDag 0 (bs6 h9f h9f hfe h7f h3c hbc) R0
    R0 R0 (RS 110 A)) (DPNode (MkDag 4 (bs6 hcf he5 hf3 hf9 he5 hff) R0 R0 R0 (RS 60 D)) (DPNode (MkDag 10 (bs6 hbf
    hb9 h7c hbc hfc hff) R0 R0 (RS 18 E) R0) (DPNode (MkDag 17 (bs6 hbe h5e he5 hf7 h2f hf2) R0 R0 (RS 34 E) R0)
    (DPNode (MkDag 34 (bs6 hcf h2f h9e h5e he5 hf7) R0 R0 R0 (RS 66 D)) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs6 h3d
    hcf he7 h97 he7 h97) R0 R0 R0 (RS 98 C)) DPEmpty DPEmpty)) (DPNode (MkDag 25 (bs6 hcf he5 hf3 hf9 hff h73) R0
    R0 R0 (RS 50 D)) (DPNode (MkDag 0 (bs6 hf2 hfb hfe h7f h3c hbc) R0 (RS 82 A) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 14 (bs6 haf hb9 he7 hee h5f h9f) R0 R0 (RS 26 E) R0) (DPNode (MkDag 21 (bs6 hee h5f h3c hf9 he7
    h97) R0 R0 R0 (RS 42 B)) (DPNode (MkDag 3 (bs6 hf9 he7 h9f h9f h3c hf3) R0 (RS 74 A) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 17 (bs6 h9e h7f h3e h79 h7d hf2) R0 (RS 106 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 29 (bs6
    hcf he5 hf3 hf9 hfb h97) R0 R0 R0 (RS 58 D)) (DPNode (MkDag 2 (bs6 hbe h7b h9f hb9 hfb h9f) R0 (RS 2 C) (RS 91
    E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 9 (bs6 hbc hf9 h7c hbe h7c hbd) R0 R0 (RS 14 E) R0) (DPNode
    (MkDag 11 (bs6 hff hf9 h7c hf3 hcb hff) R0 R0 R0 (RS 22 B)) (DPNode (MkDag 19 (bs6 hfe h7e he7 hf7 h2f h97) R0
    R0 (RS 38 E) (RS 39 C)) (DPNode (MkDag 27 (bs6 hb9 he7 h9f hf9 he7 h9f) R0 R0 R0 (RS 70 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 38 (bs6 h3f hcf he7 h97 he7 h97) R0 R0 R0 (RS 102 B)) DPEmpty DPEmpty)) (DPNode (MkDag 27 (bs6
    hcf he5 hf3 hf9 he7 h9f) R0 R0 R0 (RS 54 D)) (DPNode (MkDag 37 (bs6 h9f hcb hf3 hf9 h7c hfe) R0 (RS 86 A) R0
    R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 15 (bs6 hef hff hff h3f h2f h9f) (RS 29 D) R0 R0 (RS 30 B))
    (DPNode (MkDag 22 (bs6 h3e h5f h3f hbf he7 h9f) R0 R0 R0 (RS 46 B)) (DPNode (MkDag 2 (bs6 h9e h79 hee h79 hfb
    h9f) R0 (RS 78 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h97 h9f hfe h7f h3c hbc) R0 (RS 5 A) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 32 (bs6 hcf he5 hf2 hff he5 hee) R0 R0 R0 (RS 62 D)) (DPNode (MkDag 2 (bs6 h7e
    h7f h9f hb9 hfb h9f) (RS 1 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 5 (bs6 hcf hfc hfc hf3 hfc
    hfe) R0 R0 R0 (RS 48 D)) (DPNode (MkDag 3 (bs6 hcb hcf h97 h9f h3c hf3) (RS 11 D) R0 R0 (RS 0 C)) (DPNode
    (MkDag 11 (bs6 hef hf9 h7c hf3 hcb hff) R0 R0 R0 (RS 20 B)) (DPNode (MkDag 18 (bs6 hee h7f h3c hbf h2f h97) (RS
    35 D) R0 R0 (RS 36 B)) (DPNode (MkDag 36 (bs6 hb9 he7 h9f hff hef hf3) R0 (RS 68 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 38 (bs6 h2f hcf he7 h97 he7 h97) R0 R0 R0 (RS 100 C)) DPEmpty DPEmpty)) (DPNode (MkDag 26 (bs6
    hcf he5 hf3 hf9 hfc hbf) R0 R0 R0 (RS 8 D)) (DPNode (MkDag 38 (bs6 h97 hf9 h7e h5e he7 h97) R0 (RS 84 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs6 hbf hb9 he7 hee h5f h9f) R0 R0 (RS 28 E) R0) (DPNode (MkDag
    21 (bs6 hfe h5f h3c hf9 he7 h97) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 37 (bs6 hfe h5f h9f hcb hdc hfe) R0 R0 (RS
    76 E) (RS 77 A)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h97 hcf h3e h79 he5 hff) R0 (RS 4 A) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 31 (bs6 hcf he5 hf3 hf9 h7c hbe) R0 R0 R0 (RS 9 D)) (DPNode (MkDag 2 (bs6 h3e h7b h9f
    hb9 hfb h9f) R0 R0 R0 (RS 92 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 10 (bs6 haf hb9 h7c hbc hfc hff) R0
    R0 (RS 16 E) R0) (DPNode (MkDag 13 (bs6 hbc hf9 he7 h9f hdc hfe) R0 R0 (RS 24 E) R0) (DPNode (MkDag 20 (bs6 hbe
    h79 h7f hf9 hfc hbe) R0 R0 (RS 40 E) R0) (DPNode (MkDag 27 (bs6 h79 he7 h9f hf9 he7 h9f) R0 R0 R0 (RS 70 B))
    DPEmpty DPEmpty) (DPNode (MkDag 41 (bs6 h9f hcf h9f hcf hf9 hff) R0 (RS 104 A) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 28 (bs6 hcf he5 hf3 hf9 h7b h9e) R0 R0 R0 (RS 56 D)) (DPNode (MkDag 7 (bs6 hf3 hdf h97 hb9 hff he7) R0
    (RS 10 C) (RS 88 E) (RS 10 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 16 (bs6 hfe h5f h3c hbf h3f h3f) R0 R0
    (RS 32 E) (RS 33 C)) (DPNode (MkDag 23 (bs6 h7e h5e h7f h97 he7 he7) (RS 7 D) R0 R0 R0) (DPNode (MkDag 1 (bs6
    h9e h5e h7e h79 hff h9e) R0 (RS 80 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbe h7f h9f hb9 hfb h9f) R0
    (RS 6 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 33 (bs6 hcf he5 hff hcb he5 hff) R0 R0 R0 (RS 64 D)) (DPNode
    (MkDag 0 (bs6 h7f hcf hff h3f h3c hbc) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)))))).

Definition dagSub_36_88 : DagPTree :=
  DPNode (MkDag 5 (bs6 h97 hcf h3e he7 h97 hff) R0 R0 R0 (RS 147 A)) (DPNode (MkDag 5 (bs6 hfc hf3 hf9 hfb h9f hff)
    (RS 16 D) R0 R0 (RS 137 B)) (DPNode (MkDag 6 (bs6 hcb he7 hcf h3c hbf hfc) R0 R0 R0 (RS 19 D)) (DPNode (MkDag 2
    (bs6 hbf h2f hff h3f h73 hfc) R0 (RS 65 C) (RS 66 E) R0) (DPNode (MkDag 5 (bs6 h73 hf3 hf2 hfc hbe hff) R0 R0
    R0 (RS 21 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h3f hf3 hf2 hfc hbe hff) R0 R0 R0 (RS 193 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 h3c hf3 hf9 hfb h9f hff) R0 R0 R0 (RS 97 C)) (DPNode (MkDag 2 (bs6 h9f he7 hf7
    h3f h73 hfc) R0 R0 R0 (RS 3 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 h7c hf9 hef hf3 hdf) R0 R0
    (RS 49 E) (RS 50 A)) (DPNode (MkDag 0 (bs6 hbf hfb h9f he5 hf3 hff) R0 R0 (RS 81 E) R0) (DPNode (MkDag 2 (bs6
    hf2 hfc hf2 hf9 hff hdc) R0 (RS 145 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hf3 hff h3e he7 h97 hff)
    R0 R0 (RS 209 E) (RS 210 B)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h9f hf2 hf9 he5 hf3 hcf) R0 (RS 113 B) R0
    R0) (DPNode (MkDag 6 (bs6 hcf h3e h5f h3c hf7 hfc) R0 R0 R0 (RS 177 D)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 5 (bs6 hfb hf3 hf2 hfc hbe hff) (RS 24 D) R0 R0 (RS 108 A)) (DPNode (MkDag 9 (bs6 h7b hfe h7f h3e h7f
    h7f) (RS 41 B) R0 R0 R0) (DPNode (MkDag 5 (bs6 he7 hf3 hf9 hfb h9f hff) (RS 72 D) R0 R0 (RS 73 B)) (DPNode
    (MkDag 5 (bs6 h7c hf3 hf9 hfb h9f hff) R0 R0 R0 (RS 16 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 he5 hf3 hf9
    h7f he7 hdc) (RS 200 D) R0 R0 (RS 201 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hfb h9f he5 hf3 hff) R0
    (RS 105 C) (RS 106 E) R0) (DPNode (MkDag 2 (bs6 hcf h3f hf2 hf9 hff hdc) (RS 168 D) R0 R0 (RS 169 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6 hee h5f h3e he7 h97 hff) (RS 56 D) R0 R0 (RS 57 B)) (DPNode (MkDag 2
    (bs6 hbf h3f hff h3f h73 hfc) R0 (RS 89 C) (RS 90 E) R0) (DPNode (MkDag 2 (bs6 hf7 h3f h9f he5 hff hdc) R0 R0
    (RS 153 E) (RS 154 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hcb hff hfe h5f h97 hff) R0 R0 R0 (RS 217 D))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h5f h72 hf9 hff hf3 hdf) (RS 140 B) R0 R0 R0) (DPNode (MkDag 5 (bs6 hcf
    h2f h3e he7 h97 hff) R0 R0 R0 (RS 82 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_36_89 : DagPTree :=
  DPNode (MkDag 0 (bs6 hcf hfb h9f he5 hf3 hff) R0 R0 R0 (RS 124 D)) (DPNode (MkDag 2 (bs6 hff hdc hf2 hf9 hff hdc)
    R0 (RS 207 A) R0 R0) (DPNode (MkDag 7 (bs6 hbe h5f h97 hcf h7f hcb) R0 R0 (RS 37 E) R0) (DPNode (MkDag 5 (bs6
    he7 hf2 hf9 he5 he7 hff) (RS 68 D) R0 R0 (RS 69 B)) (DPNode (MkDag 2 (bs6 h2f h3d hff h3f h73 hfc) R0 R0 R0 (RS
    133 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 he5 hf2 hf9 he5 he7 hff) (RS 196 D) R0 R0 (RS 197 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hf2 hf9 hef hf3 hdf) R0 R0 R0 (RS 101 C)) (DPNode (MkDag 0 (bs6 hcf h3d hcf
    h3f hf2 hff) R0 R0 R0 (RS 32 D)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 6 (bs6 hbf h97 h9e h7c hfe h7c) R0
    R0 (RS 53 E) R0) (DPNode (MkDag 5 (bs6 hb9 he5 hf7 h3f h9f hff) R0 (RS 23 C) R0 R0) (DPNode (MkDag 5 (bs6 h9f
    hcf he7 he7 h97 hff) R0 (RS 149 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hb9 hfc hbf h3c hf2 hfb) R0
    (RS 213 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 hb9 hf3 hf9 h7f he7 hdc) R0 (RS 22 C) R0 R0) (DPNode
    (MkDag 2 (bs6 h9f hfe h79 he7 hff hdc) R0 (RS 181 B) R0 (RS 181 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    0 (bs6 hdc hf3 hf9 hfc hf3 hdf) R0 R0 R0 (RS 93 A)) (DPNode (MkDag 10 (bs6 he5 he7 hcb hff hcb he7) R0 R0 R0
    (RS 45 A)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 hef hf3 hdf) (RS 76 D) R0 R0 (RS 7 B)) (DPNode (MkDag 0 (bs6 h7f
    h72 hf9 hff hf3 hdf) (RS 141 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he5 hf2 hf9 hff hf3 hdf) (RS
    204 D) R0 R0 (RS 205 B)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h9f hf3 hf2 hfc hbe hff) R0 (RS 109 B) R0 R0)
    (DPNode (MkDag 2 (bs6 h5f h3c hf7 h3f h73 hfc) (RS 173 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5
    (bs6 hfb he5 hf7 h3f h9f hff) R0 (RS 61 A) R0 R0) (DPNode (MkDag 5 (bs6 h3c hf2 hf9 he5 he7 hff) R0 R0 R0 (RS
    93 C)) (DPNode (MkDag 3 (bs6 hbf h3f h3f h3c hf2 hfb) R0 (RS 157 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3
    (bs6 hf9 h7c hbf h3c hf2 hfb) (RS 220 D) R0 R0 (RS 84 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hcf hff h3e
    he7 h97 hff) R0 R0 R0 (RS 125 A)) (DPNode (MkDag 0 (bs6 h3f h9f h9f he5 hf3 hff) R0 R0 R0 (RS 189 C)) DPEmpty
    DPEmpty) DPEmpty))).

Definition dagSub_36_90 : DagPTree :=
  DPNode (MkDag 0 (bs6 he5 hf3 hf9 hfc hf3 hdf) (RS 10 D) R0 R0 (RS 198 B)) (DPNode (MkDag 2 (bs6 h9f h3f h9e he5
    hff hdc) R0 R0 R0 (RS 152 C)) (DPNode (MkDag 5 (bs6 h7b hf3 hf2 hfc hbe hff) R0 R0 R0 (RS 24 B)) (DPNode (MkDag
    2 (bs6 h3f h2f hff h3f h73 hfc) R0 R0 R0 (RS 67 B)) (DPNode (MkDag 3 (bs6 h3e h7c hbf h3c hf2 hfb) R0 R0 R0 (RS
    131 C)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hbf he5 hf7 h3f h9f hff) R0 R0 (RS 195 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 5 (bs6 h3c hf3 hf9 h79 he7 hff) R0 R0 R0 (RS 99 C)) (DPNode (MkDag 5 (bs6 h79 hef hf9 hfb h9f
    hff) (RS 163 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hb9 h79 hf9 hff hf3 hdf) R0 (RS 51
    C) R0 R0) (DPNode (MkDag 1 (bs6 hbf hf2 hf7 hfc hbc hfc) R0 R0 (RS 83 E) R0) (DPNode (MkDag 0 (bs6 h9e h7f h9f
    he5 hf3 hff) R0 (RS 8 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h79 hf3 hf2 hfc hbe hff) R0 R0 R0 (RS
    211 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7f hf3 hf9 hfc hf3 hdf) (RS 115 D) R0 R0 R0) (DPNode (MkDag 2
    (bs6 hbb hfe h79 he7 hff hdc) R0 (RS 179 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 1 (bs6 hff hf2
    hf7 hfc hbc hfc) R0 R0 (RS 218 E) (RS 219 A)) (DPNode (MkDag 9 (bs6 h7f hfe h7f h3e h7f h7f) (RS 43 E) R0 R0
    R0) (DPNode (MkDag 5 (bs6 he7 hf3 hf9 h79 he7 hff) (RS 74 D) R0 R0 (RS 75 B)) (DPNode (MkDag 0 (bs6 hdc hf2 hf9
    hef hf3 hdf) R0 R0 R0 (RS 99 A)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 he5 hf3 hcf h3c hbf hfc) (RS 202 D) R0
    R0 (RS 203 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hfb h9f he5 hf3 hff) R0 R0 R0 (RS 185 C)) (DPNode
    (MkDag 5 (bs6 h79 h7c hf3 hdc hbe hff) (RS 171 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6
    hcf hf3 hf2 hfc hbe hff) R0 R0 R0 (RS 59 A)) (DPNode (MkDag 2 (bs6 h3f h3f hff h3f h73 hfc) R0 R0 R0 (RS 91 C))
    (DPNode (MkDag 2 (bs6 hbf h3f h9f he5 hff hdc) R0 R0 (RS 155 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f
    hf2 hf7 hfc hbc hfc) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h9f h72 hf9 hff hf3 hdf) R0
    (RS 27 C) R0 R0) (DPNode (MkDag 0 (bs6 h2f h9f h9f he5 hf3 hff) R0 R0 R0 (RS 187 C)) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_36_91 : DagPTree :=
  DPNode (MkDag 3 (bs6 h7f h2f h9f h2f hf3 hfb) (RS 175 B) R0 R0 R0) (DPNode (MkDag 1 (bs6 hf9 hf3 hf9 h7f he7 hdc)
    (RS 22 D) (RS 117 A) R0 (RS 117 A)) (DPNode (MkDag 8 (bs6 hb3 hcf hf9 h7d hcf hcf) R0 (RS 39 C) R0 R0) (DPNode
    (MkDag 0 (bs6 he7 hf3 hf9 hfc hf3 hdf) (RS 70 D) R0 R0 (RS 71 B)) (DPNode (MkDag 2 (bs6 h3f h3d hff h3f h73
    hfc) R0 R0 R0 (RS 88 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 he5 hf3 hf9 hfc hf2 hfb) (RS 198 D) R0 R0 (RS
    199 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbe h7c hf2 hf9 hff hdc) R0 (RS 103 C) R0 R0) (DPNode (MkDag 6
    (bs6 hb9 he7 h9e h7c hfe h7c) R0 (RS 167 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hbf hff h9e
    he5 hf3 hff) R0 R0 (RS 55 E) R0) (DPNode (MkDag 2 (bs6 hf7 h3f hff h3f h73 hfc) (RS 86 D) R0 (RS 87 E) (RS 88
    C)) (DPNode (MkDag 5 (bs6 hbf h3c hf2 hfc hbe hff) R0 (RS 151 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6
    hcf h3f hff h3f h73 hfc) R0 R0 R0 (RS 91 C)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hf3 hf3 hf9 h79 he7 hff)
    (RS 118 D) R0 (RS 119 E) (RS 15 B)) (DPNode (MkDag 3 (bs6 hcf h73 hcf h3f h73 hfb) R0 R0 R0 (RS 9 D)) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs6 h2f he5 hf7 h3f h9f hff) R0 R0 R0 (RS 194 C)) (DPNode (MkDag 11 (bs6
    hff hcf hcf h2f hcf h2f) R0 (RS 47 A) R0 R0) (DPNode (MkDag 2 (bs6 h9f hdc hf2 hf9 hff hdc) R0 (RS 79 C) R0 R0)
    (DPNode (MkDag 2 (bs6 hbf hf3 hf2 hfc hf3 hfc) R0 (RS 143 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hbf
    hdc hf2 hf9 hff hdc) R0 (RS 20 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 h9f h2f hff h3f h73 hfc) R0
    (RS 111 A) R0 R0) (DPNode (MkDag 3 (bs6 h5f h2f h9f h2f hf3 hfb) (RS 14 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 2 (bs6 hf7 h2f hff h3f h73 hfc) R0 R0 (RS 63 E) (RS 64 C)) (DPNode (MkDag 0 (bs6 hfc hf3 hf9 hfc
    hf3 hdf) R0 (RS 136 B) R0 R0) (DPNode (MkDag 2 (bs6 h9e he7 hf7 h3f h73 hfc) R0 R0 R0 (RS 159 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 hf9 hf2 hf7 hfc hbc hfc) R0 (RS 127 A) R0 R0) (DPNode (MkDag 5 (bs6 h2f
    hf3 hf2 hfc hbe hff) R0 R0 R0 (RS 191 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_36_92 : DagPTree :=
  DPNode (MkDag 3 (bs6 hcf hf3 hcf h3f h73 hfb) R0 R0 R0 (RS 183 D)) (DPNode (MkDag 2 (bs6 h7c hf3 hf2 hfc hf3 hfc)
    (RS 139 B) R0 R0 R0) (DPNode (MkDag 5 (bs6 h79 he5 hff h3f h9e hff) (RS 172 B) R0 R0 R0) (DPNode (MkDag 2 (bs6
    hff h2f hff h3f h73 hfc) (RS 65 D) R0 R0 (RS 196 B)) (DPNode (MkDag 3 (bs6 hbe h7c hbf h3c hf2 hfb) R0 R0 (RS
    130 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 haf he5 hf7 h3f h9f hff) R0 R0 (RS 30 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 hbc hf3 hf9 h79 he7 hff) R0 R0 (RS 98 E) R0) (DPNode (MkDag 3 (bs6 h73 hcf hff
    h2f hf3 hfb) R0 R0 R0 (RS 3 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 h79 h7c hf9 hef hf3 hdf) R0 R0
    R0 (RS 48 B)) (DPNode (MkDag 0 (bs6 h3f hfb h9f he5 hf3 hff) R0 R0 R0 (RS 82 C)) (DPNode (MkDag 0 (bs6 h9e h7b
    h9f he5 hf3 hff) R0 R0 R0 (RS 146 A)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h73 hff h3e he7 h97 hff) R0 R0 R0
    (RS 208 B)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h7f h72 hf7 h3c hf3 hcf) R0 R0 R0 (RS 29 B)) (DPNode (MkDag
    4 (bs6 hcf hee h5f h3c hf3 hcf) R0 R0 R0 (RS 178 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs6 h97 hcf
    he7 he7 h97 hff) R0 R0 R0 (RS 148 A)) (DPNode (MkDag 9 (bs6 h5f hfe h7f h3e h7f h7f) (RS 42 B) R0 R0 R0)
    (DPNode (MkDag 1 (bs6 he7 hf3 hf9 h7f he7 hdc) (RS 73 D) R0 R0 (RS 74 B)) (DPNode (MkDag 5 (bs6 h7c hf3 hf9 h79
    he7 hff) (RS 138 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 he5 hf3 hf9 h79 he7 hff) (RS 201 D) R0 R0
    (RS 202 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hfc hfb h9f he5 hf3 hff) R0 (RS 34 B) (RS 107 E) (RS 34 B))
    (DPNode (MkDag 6 (bs6 h79 he7 hbf hdc hbe h7c) (RS 170 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5
    (bs6 h7e h5f h3e he7 h97 hff) (RS 58 D) R0 R0 R0) (DPNode (MkDag 2 (bs6 hff h3f hff h3f h73 hfc) (RS 89 D) R0
    R0 (RS 135 B)) (DPNode (MkDag 2 (bs6 h77 h3f h9f he5 hff hdc) R0 R0 R0 (RS 152 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 3 (bs6 hcf h3c hbf hfc hf3 hfb) R0 R0 R0 (RS 0 D)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 hf2 hf9
    hef hf3 hdf) R0 R0 R0 (RS 122 A)) (DPNode (MkDag 0 (bs6 haf h9f h9f he5 hf3 hff) R0 R0 (RS 186 E) R0) DPEmpty
    DPEmpty) DPEmpty))).

Definition dagSub_36_93 : DagPTree :=
  DPNode (MkDag 0 (bs6 hfc hf2 hf9 hef hf3 hdf) (RS 13 D) R0 R0 (RS 17 B)) (DPNode (MkDag 5 (bs6 hf3 hf3 hf2 hfc
    hbe hff) R0 R0 (RS 128 E) (RS 129 C)) (DPNode (MkDag 7 (bs6 h3e h5f h97 hcf h7f hcb) R0 R0 R0 (RS 38 A))
    (DPNode (MkDag 4 (bs6 he7 hf2 hf7 h3c hf3 hcf) (RS 69 D) R0 R0 (RS 70 B)) (DPNode (MkDag 2 (bs6 hbf h3d hff h3f
    h73 hfc) R0 R0 (RS 134 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 he5 hf2 hf7 h3c hf3 hcf) (RS 197 D) R0 R0
    (RS 10 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hbc hf3 hf2 hfc hf3 hfc) R0 R0 (RS 5 E) R0) (DPNode (MkDag 5
    (bs6 hcf h2f h3e h5f h97 hff) R0 R0 R0 (RS 166 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 6 (bs6 h3f h97 h9e
    h7c hfe h7c) R0 R0 R0 (RS 54 C)) (DPNode (MkDag 2 (bs6 h9f h3d hff h3f h73 hfc) R0 (RS 86 C) R0 (RS 86 C))
    (DPNode (MkDag 5 (bs6 hf7 h3c hf2 hfc hbe hff) R0 (RS 150 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hf9
    hfc hbf h3c hf2 hfb) (RS 213 D) R0 R0 (RS 214 D)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h9f h73 hf9 h79 he7
    hff) R0 (RS 118 C) R0 (RS 118 C)) (DPNode (MkDag 1 (bs6 h79 h7e h79 h7f he7 hdc) (RS 182 D) R0 R0 (RS 1 B))
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 4 (bs6 hff h72 hf7 h3c hf3 hcf) (RS 29 D) R0 R0 (RS 114 B)) (DPNode
    (MkDag 11 (bs6 hbf hcf hcf h2f hcf h2f) R0 (RS 46 C) R0 R0) (DPNode (MkDag 2 (bs6 he7 hf3 hf2 hfc hf3 hfc) (RS
    77 D) R0 R0 (RS 78 A)) (DPNode (MkDag 2 (bs6 hdf hf3 hf2 hfc hf3 hfc) R0 R0 R0 (RS 142 A)) DPEmpty DPEmpty)
    (DPNode (MkDag 2 (bs6 he5 hf3 hf2 hfc hf3 hfc) (RS 205 D) R0 R0 (RS 206 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5
    (bs6 h7f he5 hf7 h3f h9f hff) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 2 (bs6 h7f h3c hf7 h3f h73 hfc) (RS 174 B) R0
    R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6 h9f he5 hf7 h3f h9f hff) R0 R0 R0 (RS 62 C)) (DPNode
    (MkDag 0 (bs6 hbc hf3 hf9 hfc hf3 hdf) R0 (RS 94 C) (RS 11 E) R0) (DPNode (MkDag 3 (bs6 hff h3f h3f h3c hf2
    hfb) R0 (RS 158 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 hb9 hf2 hf7 hfc hbc hfc) R0 (RS 126
    C) R0 R0) (DPNode (MkDag 5 (bs6 haf hf3 hf2 hfc hbe hff) R0 R0 (RS 190 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_36_94 : DagPTree :=
  DPNode (MkDag 0 (bs6 h3c hf3 hf9 hfc hf3 hdf) R0 R0 R0 (RS 95 C)) (DPNode (MkDag 2 (bs6 hcb hcf hcf h2f hbf hdc)
    R0 R0 R0 (RS 165 D)) (DPNode (MkDag 5 (bs6 hcf hf3 hf9 hfb h9f hff) R0 R0 R0 (RS 116 A)) (DPNode (MkDag 4 (bs6
    he7 hf2 hf9 he5 hf3 hcf) (RS 67 D) R0 R0 (RS 68 B)) (DPNode (MkDag 2 (bs6 haf h3d hff h3f h73 hfc) R0 R0 (RS
    132 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h3f he5 hf7 h3f h9f hff) R0 R0 R0 (RS 64 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 hef hf3 hdf) R0 (RS 13 C) (RS 100 E) R0) (DPNode (MkDag 5 (bs6 h79
    hff hf9 hfb h9f hff) (RS 164 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hf9 h79 hf9 hff hf3
    hdf) (RS 51 D) R0 R0 (RS 52 C)) (DPNode (MkDag 1 (bs6 h3f hf2 hf7 hfc hbc hfc) R0 R0 R0 (RS 84 A)) (DPNode
    (MkDag 5 (bs6 h9f hcf h3e he7 h97 hff) R0 (RS 25 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hf9 hf3 hf2
    hfc hbe hff) R0 R0 R0 (RS 212 A)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hcf h73 hf9 hfb h9f hff) R0 R0 R0 (RS
    35 D)) (DPNode (MkDag 2 (bs6 hfb hfe h79 he7 hff hdc) (RS 179 D) (RS 180 A) R0 (RS 180 A)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs6 hf3 hf2 hf9 hff hf3 hdf) (RS 27 D) R0 R0 (RS 123 D)) (DPNode (MkDag 10 (bs6
    h65 he7 hcb hff hcb he7) R0 R0 R0 (RS 44 B)) (DPNode (MkDag 6 (bs6 he7 hf3 hcf h3c hbf hfc) (RS 75 D) R0 R0 (RS
    76 B)) (DPNode (MkDag 2 (bs6 h5e h7c hf2 hf9 hff hdc) (RS 2 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6
    he5 hf2 hf9 hef hf3 hdf) (RS 203 D) R0 R0 (RS 204 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h7c hfb h9f he5
    hf3 hff) R0 R0 R0 (RS 105 B)) (DPNode (MkDag 2 (bs6 h79 h7c hbe he5 hff hdc) (RS 33 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6 hbb he5 hf7 h3f h9f hff) R0 (RS 60 C) R0 R0) (DPNode (MkDag 5 (bs6 hbc
    hf2 hf9 he5 he7 hff) R0 R0 (RS 92 E) R0) (DPNode (MkDag 2 (bs6 h3f h3f h9f he5 hff hdc) R0 R0 R0 (RS 156 A))
    DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hb9 h7c hbf h3c hf2 hfb) R0 (RS 220 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs6 hcb hdc hf2 hf9 hff hdc) R0 R0 R0 (RS 12 D)) (DPNode (MkDag 0 (bs6 hbf h9f h9f he5 hf3 hff) R0 R0
    (RS 188 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_36_95 : DagPTree :=
  DPNode (MkDag 0 (bs6 h79 hf2 hf9 hef hf3 hdf) (RS 120 B) R0 R0 (RS 121 B)) (DPNode (MkDag 5 (bs6 hf9 he5 hf7 h3f
    h9f hff) (RS 23 D) (RS 85 A) R0 (RS 85 A)) (DPNode (MkDag 8 (bs6 hf3 hcf hf9 h7d hcf hcf) (RS 39 D) R0 R0 (RS
    40 B)) (DPNode (MkDag 3 (bs6 he7 hf3 hf9 hfc hf2 hfb) (RS 71 D) R0 R0 (RS 72 B)) (DPNode (MkDag 5 (bs6 h7c hf2
    hf9 he5 he7 hff) (RS 28 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 he5 hf3 hf9 hfb h9f hff) (RS 199 D)
    R0 R0 (RS 200 B)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hfe h7c hf2 hf9 hff hdc) (RS 103 D) (RS 104 C) R0 (RS
    104 C)) (DPNode (MkDag 6 (bs6 hf9 he7 h9e h7c hfe h7c) R0 (RS 168 D) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 h3f hff h9e he5 hf3 hff) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 2 (bs6 h77 h3f hff h3f h73 hfc) R0 R0
    R0 (RS 86 B)) (DPNode (MkDag 5 (bs6 hff h3c hf2 hfc hbe hff) R0 (RS 18 A) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 3 (bs6 hcb hf3 hcf h3f h73 hfb) R0 R0 R0 (RS 216 D)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h73 hf3 hf9
    h79 he7 hff) R0 R0 R0 (RS 118 B)) (DPNode (MkDag 5 (bs6 hcf hff hfe h5f h97 hff) R0 R0 R0 (RS 6 D)) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs6 hff he5 hf7 h3f h9f hff) (RS 31 D) R0 R0 (RS 110 A)) (DPNode (MkDag 0
    (bs6 hb9 h7c hf9 hef hf3 hdf) R0 R0 R0 (RS 48 C)) (DPNode (MkDag 0 (bs6 hf7 hfb h9f he5 hf3 hff) (RS 79 D) R0
    R0 (RS 80 C)) (DPNode (MkDag 2 (bs6 hff hf3 hf2 hfc hf3 hfc) R0 (RS 144 C) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 h9f hfb h9f he5 hf3 hff) R0 R0 R0 (RS 208 C)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs6 h97 hf2 hf9
    he5 hf3 hcf) R0 R0 R0 (RS 112 A)) (DPNode (MkDag 4 (bs6 h79 h7e h79 he5 hf3 hcf) (RS 176 D) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs6 h77 h2f hff h3f h73 hfc) R0 R0 R0 (RS 62 B)) (DPNode (MkDag 5 (bs6 hbc
    hf3 hf9 hfb h9f hff) R0 R0 (RS 96 E) R0) (DPNode (MkDag 2 (bs6 h97 he7 hf7 h3f h73 hfc) R0 (RS 160 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 h9f h73 hf2 hfc hbe hff) R0 R0 R0 (RS 21 C)) (DPNode (MkDag 5
    (bs6 hbf hf3 hf2 hfc hbe hff) R0 R0 (RS 192 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_36 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hcf h2f h9f he5 hf3 hff) R0 R0 R0 (RS 26 C)) (DPNode (MkDag 1 (bs6 hf9 h7e h79 h7f he7
    hdc) (RS 1 D) R0 R0 (RS 215 D)) (DPNode (MkDag 2 (bs6 h7e h7c hf2 hf9 hff hdc) (RS 105 C) R0 R0 R0) (DPNode
    (MkDag 4 (bs6 hcb hdc hbf h3c hf3 hcf) R0 R0 R0 (RS 162 B)) dagSub_36_88 dagSub_36_89) (DPNode (MkDag 0 (bs6
    hcf h2f h9e he5 hf3 hff) R0 R0 R0 (RS 184 D)) dagSub_36_90 dagSub_36_91)) (DPNode (MkDag 3 (bs6 hf3 hcf hff h2f
    hf3 hfb) R0 R0 (RS 161 E) (RS 4 D)) (DPNode (MkDag 2 (bs6 h3c hf3 hf2 hfc hf3 hfc) R0 R0 R0 (RS 102 A))
    dagSub_36_92 dagSub_36_93) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 hff hf3 hdf) (RS 7 D) R0 R0 (RS 77 B))
    dagSub_36_94 dagSub_36_95))).

Definition dagSub_37_96 : DagPTree :=
  DPNode (MkDag 5 (bs6 hdc hbe h7f hff hf3 hcf) R0 R0 R0 (RS 9 A)) (DPNode (MkDag 10 (bs6 h3c hfb hf2 hf9 hfb h9f)
    R0 R0 R0 (RS 17 C)) (DPNode (MkDag 18 (bs6 hcf h3e he5 hef hf7 h2f) R0 R0 R0 (RS 33 D)) (DPNode (MkDag 24 (bs6
    hbe hff h9f h9f h9f hff) R0 (RS 65 C) R0 R0) (DPNode (MkDag 29 (bs6 hbc hf3 hcf hf3 hf9 hff) R0 R0 (RS 129 E)
    R0) DPEmpty DPEmpty) (DPNode (MkDag 14 (bs6 hf7 h3f hb9 h79 hf3 hee) (RS 192 D) R0 R0 (RS 80 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs6 h7c hbd hcf hf3 hf9 hf3) (RS 97 D) R0 R0 (RS 98 B)) (DPNode (MkDag 29 (bs6 hfd
    hf3 hcf hf3 hf9 hff) R0 (RS 162 B) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6 hbf h73 hfe h5e h7c
    hf7) R0 R0 (RS 49 E) R0) (DPNode (MkDag 14 (bs6 hbf h3f hb9 h79 hf3 hee) R0 (RS 81 C) (RS 82 E) R0) (DPNode
    (MkDag 5 (bs6 hff h3f h9f hff h9f hcf) (RS 144 D) (RS 145 A) R0 (RS 145 A)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 33 (bs6 hcf h3f hcf h2f he5 hfe) R0 R0 R0 (RS 113 C)) (DPNode (MkDag 5 (bs6 h5f hfb h9f hff h9f hcf) (RS
    177 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 13 (bs6 hf2 hf9 hfd hfe he5 hf3) R0 (RS 25 A) R0
    R0) (DPNode (MkDag 12 (bs6 h3f hcb he7 hfe h7e h7d) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 21 (bs6 hfe h7f hcf h3e
    h5e he5) R0 (RS 3 D) R0 R0) (DPNode (MkDag 10 (bs6 hbf h2f h3c hf9 hfb h9f) R0 (RS 137 C) (RS 138 E) R0)
    DPEmpty DPEmpty) (DPNode (MkDag 15 (bs6 h3f h73 hf3 hee h7f h3e) R0 R0 R0 (RS 91 C)) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs6 h73 hff he5 hff he5 hee) R0 R0 R0 (RS 103 B)) (DPNode (MkDag 5 (bs6 h77 h3f h9e hff h9f hcf) R0
    R0 R0 (RS 5 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs6 he7 hcb hdf he7 hcf h9e) (RS 56 D) R0 R0 (RS
    57 B)) (DPNode (MkDag 15 (bs6 h7f h73 hf3 hee h7f h3e) (RS 89 D) R0 R0 (RS 90 B)) (DPNode (MkDag 26 (bs6 hbf
    h3f h3c hf2 hf9 h79) R0 R0 (RS 153 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 14 (bs6 hff h2f hb9 h79 hf3
    hee) R0 (RS 121 A) R0 (RS 121 A)) (DPNode (MkDag 16 (bs6 hf9 he7 h9f hfc hfc hbf) R0 (RS 185 B) R0 R0) DPEmpty
    DPEmpty) DPEmpty))).

Definition dagSub_37_97 : DagPTree :=
  DPNode (MkDag 9 (bs6 hbf hcf h7c hf3 hcf hf3) R0 R0 R0 (RS 13 C)) (DPNode (MkDag 10 (bs6 h3f h9f hf2 hf9 hfb h9f)
    R0 R0 R0 (RS 21 A)) (DPNode (MkDag 9 (bs6 hf9 hf2 hfc hf3 hcf hf3) (RS 36 D) R0 R0 (RS 37 A)) (DPNode (MkDag 25
    (bs6 hdc hff hf9 hee h7e he7) R0 R0 R0 (RS 69 A)) (DPNode (MkDag 4 (bs6 he7 hbe h5f hfe h7f h3f) (RS 132 D) R0
    R0 (RS 4 B)) DPEmpty DPEmpty) (DPNode (MkDag 29 (bs6 h3f hf3 hcf hf3 hf9 hff) R0 R0 R0 (RS 197 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 30 (bs6 hfc hff hb9 hf9 he7 hff) (RS 100 D) (RS 102 A) R0 (RS 102 A)) (DPNode (MkDag
    15 (bs6 h9f h73 hf3 hee h7f h3e) R0 (RS 165 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 21 (bs6 haf hfc
    hfb h9e h7e he5) R0 R0 (RS 53 E) R0) (DPNode (MkDag 2 (bs6 h97 hff hfc hff h3c hbe) R0 (RS 85 A) R0 (RS 85 A))
    (DPNode (MkDag 3 (bs6 haf h7e h7f h73 hcf he5) R0 R0 (RS 149 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 22
    (bs6 h7f hff h3f hb9 h7c hf3) (RS 117 D) R0 R0 (RS 118 B)) (DPNode (MkDag 31 (bs6 he7 hcf h9e h7c hf2 hf3) (RS
    180 D) R0 R0 (RS 181 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 15 (bs6 h9f hcb hcf h97 hcb hf9) R0 (RS 29
    B) R0 R0) (DPNode (MkDag 1 (bs6 hbf h9f h3c hbf h3c hfe) R0 R0 (RS 45 E) R0) (DPNode (MkDag 28 (bs6 hbb h97 hcf
    hfc hbf hff) R0 (RS 77 C) R0 R0) (DPNode (MkDag 11 (bs6 hff h3c hf2 hfb h9f hcf) (RS 140 D) R0 R0 (RS 141 A))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h73 hff he5 hff h3c hbd) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 21 (bs6 h97 hcf hcf h3e h5e he5) R0 R0 R0 (RS 109 A)) (DPNode (MkDag 19 (bs6 hdc hbe h79 h7d hcf hff) R0
    R0 R0 (RS 173 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs6 hbc hf7 hcb hf3 hf3 hf3) R0 R0 (RS 61 E)
    R0) (DPNode (MkDag 18 (bs6 hff hff hfe h7e h5f h2f) R0 (RS 94 B) R0 R0) (DPNode (MkDag 14 (bs6 h9f h3f hb9 h79
    hf3 hee) R0 (RS 157 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hbf h3c hbc hf7 h3c hbe) R0 R0
    (RS 125 E) R0) (DPNode (MkDag 26 (bs6 hcf hff h3c hf2 hf9 h79) R0 R0 R0 (RS 189 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_37_98 : DagPTree :=
  DPNode (MkDag 5 (bs6 hfc hbe h7f hff hf3 hcf) (RS 10 D) R0 R0 (RS 11 A)) (DPNode (MkDag 10 (bs6 h2f h9f hf2 hf9
    hfb h9f) R0 R0 R0 (RS 19 C)) (DPNode (MkDag 19 (bs6 hcf hff h9e h5f hcb hff) R0 R0 R0 (RS 35 A)) (DPNode (MkDag
    13 (bs6 he5 hf2 hfc hbe he5 hf3) R0 R0 R0 (RS 2 B)) (DPNode (MkDag 15 (bs6 hbc hf3 hf3 hee h7f h3e) R0 R0 (RS
    131 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 29 (bs6 h2f hf3 hcf hf3 hf9 hff) R0 R0 R0 (RS 195 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs6 hfc hbd hcf hf3 hf9 hf3) (RS 98 D) R0 R0 (RS 175 B)) (DPNode (MkDag 35 (bs6 h79
    hf3 hf9 hf3 hf3 hf3) R0 R0 R0 (RS 163 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 15 (bs6 hbf hee h7f h97 hcb
    hf9) R0 R0 (RS 51 E) R0) (DPNode (MkDag 14 (bs6 h3f h3f hb9 h79 hf3 hee) R0 R0 R0 (RS 158 A)) (DPNode (MkDag 21
    (bs6 hf6 h7f hcf h3e h5e he5) R0 (RS 71 C) (RS 147 E) (RS 71 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 28
    (bs6 h3f hbf hcf h7c hbf hff) R0 R0 R0 (RS 115 B)) (DPNode (MkDag 5 (bs6 hbe h7c hf2 hff hdc hff) R0 R0 (RS 179
    E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 14 (bs6 h97 he7 he7 h97 hcf h3e) R0 (RS 27 A) R0 R0) (DPNode
    (MkDag 14 (bs6 h7d hdf h2f h97 hcf h3e) (RS 43 D) R0 R0 R0) (DPNode (MkDag 26 (bs6 hcf h3f h3c hf2 hf9 h79) R0
    R0 R0 (RS 75 D)) (DPNode (MkDag 10 (bs6 h3f h2f h3c hf9 hfb h9f) R0 R0 R0 (RS 139 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 5 (bs6 hbf hfb h9f hff h9f hcf) R0 (RS 203 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 31 (bs6 h97 hcf
    h9e h7c hf2 hf3) R0 R0 R0 (RS 107 A)) (DPNode (MkDag 5 (bs6 h3f h3f h9e hff h9f hcf) R0 R0 R0 (RS 143 A))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 3 (bs6 he7 hf2 hf9 hfc hf9 he5) (RS 58 D) R0 R0 (RS 59 B)) (DPNode
    (MkDag 15 (bs6 hff h73 hf3 hee h7f h3e) (RS 90 D) R0 R0 (RS 171 B)) (DPNode (MkDag 22 (bs6 he7 h9f h3f hb9 h7c
    hf3) (RS 154 D) R0 R0 (RS 155 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hf7 h3c hbc hf7 h3c hbe) (RS
    122 D) R0 (RS 123 E) (RS 124 C)) (DPNode (MkDag 33 (bs6 he7 hf7 hcf h2f he5 hfe) (RS 186 D) R0 R0 (RS 187 B))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_37_99 : DagPTree :=
  DPNode (MkDag 9 (bs6 h7f hcf h7c hf3 hcf hf3) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 11 (bs6 hf2 hff hf3 hfb h9f hcf)
    R0 (RS 23 C) R0 R0) (DPNode (MkDag 20 (bs6 hf9 h7f hf3 hcf hfc hbc) (RS 38 D) R0 R0 (RS 39 C)) (DPNode (MkDag
    25 (bs6 hfc hff hf9 hee h7e he7) R0 (RS 71 C) R0 R0) (DPNode (MkDag 6 (bs6 h9f hcf hcf hf3 hf9 hf3) R0 (RS 135
    C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs6 h2f h73 hf3 hee h7f h3e) R0 R0 R0 (RS 199 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 h9f hfb h9f hff h9f hcf) R0 (RS 103 C) R0 (RS 103 C)) (DPNode (MkDag 14 (bs6
    h7f h2f hb9 h79 hf3 hee) R0 R0 R0 (RS 120 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 21 (bs6 hbf hfc hfb h9e
    h7e he5) R0 R0 (RS 55 E) R0) (DPNode (MkDag 29 (bs6 h97 hf3 hcf hf3 hf9 hff) R0 (RS 87 A) R0 (RS 87 A)) (DPNode
    (MkDag 3 (bs6 hbf h7e h7f h73 hcf he5) R0 R0 (RS 151 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 22 (bs6
    hff hff h3f hb9 h7c hf3) R0 R0 R0 (RS 166 B)) (DPNode (MkDag 21 (bs6 hcf hcf hcf h3e h5e he5) R0 R0 R0 (RS 183
    A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 16 (bs6 hff h73 hcf hf3 hfc hbf) (RS 30 D) R0 R0 (RS 31 B))
    (DPNode (MkDag 5 (bs6 haf h73 hfe h5e h7c hf7) R0 R0 (RS 47 E) R0) (DPNode (MkDag 28 (bs6 h9f h97 hcf hfc hbf
    hff) R0 R0 R0 (RS 79 B)) (DPNode (MkDag 5 (bs6 hf7 h3f h9f hff h9f hcf) R0 (RS 143 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 3 (bs6 h9f h9e h7f h73 hcf he5) R0 R0 R0 (RS 111 B)) (DPNode (MkDag 19 (bs6 h3c hbe h79
    h7d hcf hff) R0 R0 R0 (RS 201 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs6 hbc hff hcb hf3 hf3 hf3) R0
    R0 (RS 63 E) R0) (DPNode (MkDag 19 (bs6 h7c hbe h79 h7d hcf hff) R0 R0 R0 (RS 95 B)) (DPNode (MkDag 1 (bs6 hbf
    h3f h3f hf7 h3f h3e) R0 (RS 1 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 34 (bs6 hbc hbe h5f h9f he7
    hf9) R0 R0 (RS 127 E) R0) (DPNode (MkDag 22 (bs6 h3f hbf h3f hb9 h7c hf3) R0 R0 R0 (RS 191 A)) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_37_100 : DagPTree :=
  DPNode (MkDag 5 (bs6 hbc hbe h7f hff hf3 hcf) R0 (RS 10 C) R0 R0) (DPNode (MkDag 10 (bs6 haf h9f hf2 hf9 hfb h9f)
    R0 R0 (RS 18 E) R0) (DPNode (MkDag 18 (bs6 hcf he7 he5 hef hf7 h2f) R0 R0 R0 (RS 34 D)) (DPNode (MkDag 24 (bs6
    hfe hff h9f h9f h9f hff) R0 (RS 66 B) R0 R0) (DPNode (MkDag 29 (bs6 h3c hf3 hcf hf3 hf9 hff) R0 R0 R0 (RS 130
    C)) DPEmpty DPEmpty) (DPNode (MkDag 29 (bs6 haf hf3 hcf hf3 hf9 hff) R0 R0 (RS 194 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 30 (bs6 hdc hff hb9 hf9 he7 hff) R0 R0 R0 (RS 99 A)) (DPNode (MkDag 29 (bs6 h3d hf3 hcf hf3 hf9
    hff) R0 R0 R0 (RS 193 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs6 h3f h73 hfe h5e h7c hf7) R0 R0 R0
    (RS 50 C)) (DPNode (MkDag 14 (bs6 hff h3f hb9 h79 hf3 hee) (RS 81 D) (RS 83 A) R0 (RS 83 A)) (DPNode (MkDag 2
    (bs6 h9f h3f he5 hff he5 hee) R0 (RS 146 C) R0 (RS 146 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 28 (bs6 hbf
    hbf hcf h7c hbf hff) R0 R0 (RS 114 E) R0) (DPNode (MkDag 5 (bs6 h7f hfb h9f hff h9f hcf) (RS 178 C) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 14 (bs6 h9e he7 he7 h97 hcf h3e) R0 R0 R0 (RS 26 A)) (DPNode (MkDag
    13 (bs6 he7 hcb hcf hfe he5 hf3) R0 R0 R0 (RS 42 B)) (DPNode (MkDag 21 (bs6 h3e h7f hcf h3e h5e he5) R0 R0 R0
    (RS 148 C)) (DPNode (MkDag 10 (bs6 hff h2f h3c hf9 hfb h9f) R0 (RS 167 A) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 6 (bs6 hbc hbd hcf hf3 hf9 hf3) R0 R0 (RS 6 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h9e h7c hf2
    hff hdc hff) R0 (RS 106 A) R0 R0) (DPNode (MkDag 5 (bs6 hbf h3f h9e hff h9f hcf) R0 R0 (RS 170 E) R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 22 (bs6 he7 hfc hf3 hcf h3f hf3) (RS 57 D) R0 R0 (RS 58 B)) (DPNode (MkDag 18
    (bs6 hdf hff hfe h7e h5f h2f) R0 R0 R0 (RS 91 A)) (DPNode (MkDag 26 (bs6 h3f h3f h3c hf2 hf9 h79) R0 R0 R0 (RS
    154 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 h9f h2f h3f hf7 h3f h3e) R0 (RS 122 C) R0 (RS 122 C))
    (DPNode (MkDag 32 (bs6 he7 h9f hdf hee h5f h3d) R0 R0 R0 (RS 186 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_37_101 : DagPTree :=
  DPNode (MkDag 9 (bs6 hff hcf h7c hf3 hcf hf3) R0 R0 (RS 14 E) (RS 15 C)) (DPNode (MkDag 11 (bs6 hb2 hff hf3 hfb
    h9f hcf) R0 (RS 22 C) R0 R0) (DPNode (MkDag 20 (bs6 hb9 h7f hf3 hcf hfc hbc) R0 (RS 38 C) R0 R0) (DPNode (MkDag
    25 (bs6 hbc hff hf9 hee h7e he7) R0 (RS 70 C) R0 R0) (DPNode (MkDag 6 (bs6 he7 he7 hcf h73 hf9 hf3) (RS 133 D)
    R0 R0 (RS 134 A)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs6 haf h73 hf3 hee h7f h3e) R0 R0 (RS 198 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 30 (bs6 h3c hff hb9 hf9 he7 hff) R0 R0 R0 (RS 202 A)) (DPNode (MkDag 15 (bs6 hf3 hf3
    hf3 hee h7f h3e) (RS 165 D) R0 R0 (RS 95 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 21 (bs6 h2f hfc hfb h9e
    h7e he5) R0 R0 R0 (RS 54 C)) (DPNode (MkDag 2 (bs6 h9f hff hfc hff h3c hbe) R0 (RS 86 A) R0 (RS 86 A)) (DPNode
    (MkDag 3 (bs6 h2f h7e h7f h73 hcf he5) R0 R0 R0 (RS 150 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 14 (bs6
    hdf h2f hb9 h79 hf3 hee) R0 R0 R0 (RS 119 A)) (DPNode (MkDag 21 (bs6 h7d hcf hcf h3e h5e he5) (RS 182 D) R0 R0
    R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 16 (bs6 h7f h73 hcf hf3 hfc hbf) R0 R0 R0 (RS 30 B)) (DPNode
    (MkDag 1 (bs6 h3f h9f h3c hbf h3c hfe) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 28 (bs6 hfb h97 hcf hfc hbf hff) R0
    (RS 78 A) R0 R0) (DPNode (MkDag 5 (bs6 h9f h3f h9e hff h9f hcf) R0 (RS 142 C) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 21 (bs6 h9f hcf hcf h3e h5e he5) R0 (RS 110 A) R0 R0) (DPNode (MkDag 19 (bs6 hbc hbe h79 h7d hcf
    hff) R0 (RS 95 C) (RS 174 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs6 h3c hf7 hcb hf3 hf3 hf3) R0
    R0 R0 (RS 62 C)) (DPNode (MkDag 18 (bs6 h3f hff hfe h7e h5f h2f) R0 R0 R0 (RS 173 C)) (DPNode (MkDag 1 (bs6 hf7
    h3f h3f hf7 h3f h3e) R0 (RS 158 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h3f h3c hbc hf7 h3c
    hbe) R0 R0 R0 (RS 126 C)) (DPNode (MkDag 22 (bs6 hbf hbf h3f hb9 h7c hf3) R0 R0 (RS 190 E) R0) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_37_102 : DagPTree :=
  DPNode (MkDag 8 (bs6 h9f hff h2f h97 hb9 he7) R0 (RS 12 A) R0 R0) (DPNode (MkDag 10 (bs6 hbf h9f hf2 hf9 hfb h9f)
    R0 R0 (RS 20 E) R0) (DPNode (MkDag 9 (bs6 hb9 hf2 hfc hf3 hcf hf3) R0 (RS 36 C) R0 R0) (DPNode (MkDag 25 (bs6
    h7c hf7 hf9 hee h7e he7) (RS 68 D) R0 R0 R0) (DPNode (MkDag 15 (bs6 h3c hf3 hf3 hee h7f h3e) R0 R0 R0 (RS 132
    B)) DPEmpty DPEmpty) (DPNode (MkDag 29 (bs6 hbf hf3 hcf hf3 hf9 hff) R0 R0 (RS 196 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 30 (bs6 hbc hff hb9 hf9 he7 hff) R0 (RS 100 C) (RS 101 E) R0) (DPNode (MkDag 35 (bs6 hf9 hf3 hf9
    hf3 hf3 hf3) (RS 163 D) R0 R0 (RS 164 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 15 (bs6 h3f hee h7f h97 hcb
    hf9) R0 R0 R0 (RS 52 C)) (DPNode (MkDag 1 (bs6 h9f h3f h3f hf7 h3f h3e) R0 (RS 84 A) R0 (RS 84 A)) (DPNode
    (MkDag 21 (bs6 h76 h7f hcf h3e h5e he5) R0 R0 R0 (RS 146 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 22 (bs6
    hef hff h3f hb9 h7c hf3) R0 R0 R0 (RS 116 B)) (DPNode (MkDag 5 (bs6 h3e h7c hf2 hff hdc hff) R0 R0 R0 (RS 180
    B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 14 (bs6 h9f he7 he7 h97 hcf h3e) R0 R0 R0 (RS 28 A)) (DPNode
    (MkDag 14 (bs6 hcf hdf h2f h97 hcf h3e) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 27 (bs6 hcf he7 h9f h2f hcf h3f) R0
    R0 R0 (RS 76 A)) (DPNode (MkDag 11 (bs6 hbf h3c hf2 hfb h9f hcf) R0 (RS 140 C) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 5 (bs6 hff hfb h9f hff h9f hcf) (RS 203 D) R0 R0 (RS 0 C)) DPEmpty DPEmpty)) (DPNode (MkDag 31 (bs6 h9f
    hcf h9e h7c hf2 hf3) R0 (RS 108 A) R0 R0) (DPNode (MkDag 18 (bs6 h7f hff hfe h7e h5f h2f) (RS 172 D) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 4 (bs6 he7 hf2 hf9 hf9 hf7 h3f) (RS 59 D) R0 R0 (RS 60 C)) (DPNode
    (MkDag 18 (bs6 hbf hff hfe h7e h5f h2f) R0 (RS 92 C) (RS 93 E) R0) (DPNode (MkDag 15 (bs6 he7 hf3 hef hf9 h7c
    hbe) (RS 155 D) R0 R0 (RS 156 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h77 h3c hbc hf7 h3c hbe) R0
    R0 R0 (RS 122 B)) (DPNode (MkDag 26 (bs6 h7d hff h3c hf2 hf9 h79) (RS 188 D) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_37_103 : DagPTree :=
  DPNode (MkDag 10 (bs6 hbc hfb hf2 hf9 hfb h9f) R0 R0 (RS 16 E) R0) (DPNode (MkDag 12 (bs6 hf2 hf9 he7 hfe h7e
    h7d) R0 (RS 24 C) R0 R0) (DPNode (MkDag 12 (bs6 hbf hcb he7 hfe h7e h7d) R0 R0 (RS 40 E) R0) (DPNode (MkDag 21
    (bs6 hbe h7f hcf h3e h5e he5) R0 (RS 72 C) (RS 73 E) R0) (DPNode (MkDag 10 (bs6 hf7 h2f h3c hf9 hfb h9f) (RS
    135 D) (RS 136 C) R0 (RS 136 C)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs6 hbf h73 hf3 hee h7f h3e) R0 R0 (RS 200
    E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs6 hf3 hff he5 hff he5 hee) (RS 103 D) R0 (RS 104 E) (RS 105 A))
    (DPNode (MkDag 11 (bs6 h9f h3c hf2 hfb h9f hcf) R0 R0 R0 (RS 5 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 21
    (bs6 h3f hfc hfb h9e h7e he5) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 29 (bs6 h9f hf3 hcf hf3 hf9 hff) R0 (RS 88 B)
    R0 (RS 88 B)) (DPNode (MkDag 3 (bs6 h3f h7e h7f h73 hcf he5) R0 R0 R0 (RS 152 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 14 (bs6 hbf h2f hb9 h79 hf3 hee) R0 (RS 120 C) R0 R0) (DPNode (MkDag 16 (bs6 hb9 he7 h9f hfc hfc
    hbf) R0 (RS 184 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 17 (bs6 h7f hf3 hf9 he7 hcf h9e) (RS 32 D)
    R0 R0 R0) (DPNode (MkDag 5 (bs6 h2f h73 hfe h5e h7c hf7) R0 R0 R0 (RS 48 C)) (DPNode (MkDag 15 (bs6 he5 hf3 hef
    hf9 h7c hbe) (RS 79 D) R0 R0 (RS 80 A)) (DPNode (MkDag 5 (bs6 hbf h3f h9f hff h9f hcf) R0 (RS 144 C) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 32 (bs6 h7f h9f hdf hee h5f h3d) (RS 112 D) R0 R0 R0) (DPNode (MkDag
    30 (bs6 h7c hff hb9 hf9 he7 hff) (RS 176 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 23 (bs6 h3c hff
    hcb hf3 hf3 hf3) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 19 (bs6 hfc hbe h79 h7d hcf hff) (RS 95 D) (RS 96 B) (RS 94
    E) (RS 96 B)) (DPNode (MkDag 29 (bs6 hbd hf3 hcf hf3 hf9 hff) R0 (RS 160 C) (RS 161 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 34 (bs6 h3c hbe h5f h9f he7 hf9) R0 R0 R0 (RS 128 C)) (DPNode (MkDag 33 (bs6 h9f h3c
    hf9 h7c hf9 hfe) R0 (RS 192 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_37 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hf3 hff he5 hff h3c hbd) R0 R0 (RS 204 E) (RS 178 C)) (DPNode (MkDag 1 (bs6 hff h3f h3f
    hf7 h3f h3e) (RS 1 D) (RS 159 C) R0 (RS 159 C)) (DPNode (MkDag 2 (bs6 he7 h97 he5 hff he5 hee) (RS 2 D) R0 R0
    (RS 67 B)) (DPNode (MkDag 4 (bs6 he7 hfe h5f hfe h7f h3f) (RS 4 D) R0 R0 (RS 133 B)) dagSub_37_96 dagSub_37_97)
    (DPNode (MkDag 6 (bs6 h3c hbd hcf hf3 hf9 hf3) R0 R0 R0 (RS 99 C)) dagSub_37_98 dagSub_37_99)) (DPNode (MkDag 3
    (bs6 hcb hfe h7f h73 hcf he5) (RS 3 D) R0 R0 (RS 74 D)) (DPNode (MkDag 5 (bs6 hf7 h3f h9e hff h9f hcf) R0 R0
    (RS 168 E) (RS 169 C)) dagSub_37_100 dagSub_37_101) (DPNode (MkDag 7 (bs6 h7c hbe h7c hff he7 h97) (RS 8 D) R0
    R0 R0) dagSub_37_102 dagSub_37_103))).

Definition dagTree_38 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 he5 hf9 hee h5f hcb he5) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 0 (bs6 hef hf9 h7e h5f hcb
    he5) (RS 1 D) R0 R0 (RS 34 B)) (DPNode (MkDag 0 (bs6 h3f hb9 h7e h5f hcb he5) R0 R0 R0 (RS 12 B)) (DPNode
    (MkDag 0 (bs6 h7f hf9 hee h5f hcb he5) (RS 48 E) R0 R0 R0) (DPNode (MkDag 1 (bs6 hfc hbf hcf h2f hcb hf3) (RS 8
    D) R0 R0 (RS 9 B)) (DPNode (MkDag 2 (bs6 h9f he5 hf3 hfe h7d hcf) R0 (RS 17 C) R0 R0) (DPNode (MkDag 0 (bs6 hbf
    hb9 hfe h5f hcb he5) R0 R0 (RS 33 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h65 hf9 h7e h5f hcb he5) R0 R0
    R0 (RS 9 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 hcf hdf hee h5f hcb he5) R0 R0 R0 (RS 25 B)) (DPNode
    (MkDag 0 (bs6 hbf hb9 hee h5f hcb he5) R0 R0 (RS 11 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6 hef
    hf9 hee h5f hcb he5) (RS 12 D) R0 R0 (RS 4 B)) (DPNode (MkDag 5 (bs6 h7f hfe h7e h5f h9f he5) R0 R0 R0 (RS 19
    B)) (DPNode (MkDag 0 (bs6 hff hf9 h7e h5f hcb he5) R0 R0 R0 (RS 6 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    1 (bs6 hdc hbf hcf h2f hcb hf3) R0 R0 R0 (RS 29 A)) (DPNode (MkDag 0 (bs6 hbc hf9 hfe h5f hcb he5) R0 R0 (RS 5
    E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf9 hfe h5f hcb he5) R0 R0 R0 (RS 37 C)) (DPNode
    (MkDag 0 (bs6 h2f hb9 hfe h5f hcb he5) R0 R0 R0 (RS 32 C)) (DPNode (MkDag 4 (bs6 hcf h2f h9f hdc hbe h7e) (RS
    18 D) R0 R0 (RS 19 C)) (DPNode (MkDag 0 (bs6 h7f hf9 h7e h5f hcb he5) (RS 35 E) R0 R0 (RS 36 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 h5f h97 hff h2f hcb hf3) (RS 27 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h65
    hf9 hee h5f hcb he5) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs6 h9e he5 hf3 hfe h7d
    hcf) R0 (RS 15 A) R0 R0) (DPNode (MkDag 6 (bs6 hfe h5f hfe h7f h2f hff) (RS 22 D) R0 R0 (RS 23 D)) (DPNode
    (MkDag 0 (bs6 h3c hf9 h7e h5f hcb he5) R0 R0 R0 (RS 39 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbc
    hf9 hee h5f hcb he5) R0 R0 (RS 13 E) R0) (DPNode (MkDag 0 (bs6 h2f hb9 h7e h5f hcb he5) R0 R0 R0 (RS 47 C))
    DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs6 h2f hb9 hee h5f hcb he5) R0 R0 R0 (RS 40 C)) (DPNode (MkDag
    0 (bs6 h3c hf9 hfe h5f hcb he5) R0 R0 R0 (RS 45 C)) (DPNode (MkDag 0 (bs6 he5 hf9 h7e h5f hcb he5) (RS 9 D) R0
    R0 (RS 30 C)) (DPNode (MkDag 3 (bs6 hf3 he5 he7 he5 he7 hff) R0 (RS 18 D) R0 R0) (DPNode (MkDag 0 (bs6 h3f hb9
    hfe h5f hcb he5) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 h7b h97 hff h2f hcb hf3)
    (RS 26 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hef hf9 hfe h5f hcb he5) (RS 41 D) R0 R0 (RS 7 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs6 h3c hf9 hee h5f hcb he5) R0 R0 R0 (RS 31 C)) (DPNode (MkDag 6 (bs6 hbe h5f hfe
    h7f h2f hff) R0 (RS 22 C) R0 R0) (DPNode (MkDag 0 (bs6 hbc hf9 h7e h5f hcb he5) R0 R0 (RS 38 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 hbc hbf hcf h2f hcb hf3) R0 (RS 8 C) R0 R0) (DPNode (MkDag 0 (bs6 haf
    hb9 h7e h5f hcb he5) R0 R0 (RS 46 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h7f hf9 hfe h5f hcb
    he5) (RS 42 E) R0 R0 (RS 43 B)) (DPNode (MkDag 0 (bs6 h3f hb9 hee h5f hcb he5) R0 R0 R0 (RS 41 B)) (DPNode
    (MkDag 5 (bs6 hff hfe h7e h5f h9f he5) R0 R0 (RS 20 E) (RS 21 A)) (DPNode (MkDag 0 (bs6 h65 hf9 hfe h5f hcb
    he5) R0 R0 R0 (RS 6 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 h7f h97 hff h2f hcb hf3) (RS 28 D) R0
    R0 R0) (DPNode (MkDag 0 (bs6 hff hf9 hfe h5f hcb he5) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 2 (bs6 h97 he5 hf3 hfe h7d hcf) R0 R0 R0 (RS 16 A)) (DPNode (MkDag 1 (bs6 hcf he7 hff h2f hcb hf3) R0 R0
    R0 (RS 24 D)) (DPNode (MkDag 0 (bs6 haf hb9 hee h5f hcb he5) R0 R0 (RS 3 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 haf hb9 hfe h5f hcb he5) R0 R0 (RS 10 E) R0) (DPNode (MkDag 0 (bs6 hbf hb9 h7e h5f hcb
    he5) R0 R0 (RS 2 E) R0) DPEmpty DPEmpty) DPEmpty))))).

Definition dagSub_39_104 : DagPTree :=
  DPNode (MkDag 7 (bs4 hcf h3c hfe h79) R0 R0 R0 (RS 9 D)) (DPNode (MkDag 10 (bs4 hbd hff h3f h3f) R0 R0 (RS 17 E)
    R0) (DPNode (MkDag 9 (bs4 h7c hf3 hff h9f) R0 R0 R0 (RS 33 B)) (DPNode (MkDag 7 (bs4 h9f hf9 h7e h79) R0 (RS 65
    A) R0 R0) (DPNode (MkDag 1 (bs4 h7f h9f hf3 hcb) R0 R0 R0 (RS 129 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    3 (bs4 h9f hff hfe h7f) R0 (RS 97 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4 hfc hf9 hee h7f) R0 (RS 49
    B) R0 R0) (DPNode (MkDag 2 (bs4 hf2 hfb hfe h5f) (RS 80 D) R0 (RS 81 E) (RS 82 C)) (DPNode (MkDag 4 (bs4 h9f
    hcf hee h5e) R0 (RS 145 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs4 hbe h7f hfe h5f) R0 (RS 113
    C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 11 (bs4 hbf h97 he7 hf7) R0 R0 (RS 25 E) R0) (DPNode (MkDag 11 (bs4
    h3f h9f h7c hbf) R0 R0 R0 (RS 41 C)) (DPNode (MkDag 5 (bs4 h9e hf9 h7e h7f) R0 (RS 73 A) R0 R0) (DPNode (MkDag
    4 (bs4 he7 hf9 h7e h7e) R0 R0 R0 (RS 137 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hf3 hcb hee h79)
    R0 (RS 105 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 hbe he7 hee h7f) R0 R0 (RS 57 E) R0) (DPNode
    (MkDag 3 (bs4 h9e h7b hfe h5f) R0 (RS 89 A) R0 R0) (DPNode (MkDag 1 (bs4 h97 h9f hfd hcb) R0 (RS 153 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs4 h9e h7b hfd hcb) R0 R0 R0 (RS 121 A)) DPEmpty DPEmpty))).

Definition dagSub_39_105 : DagPTree :=
  DPNode (MkDag 4 (bs4 hcf h3c hfe h5e) R0 R0 R0 (RS 0 D)) (DPNode (MkDag 10 (bs4 hbf hff h3f h3f) R0 R0 (RS 21 E)
    R0) (DPNode (MkDag 6 (bs4 h3c hf9 hfd hf9) R0 R0 R0 (RS 37 C)) (DPNode (MkDag 6 (bs4 hf3 hcf h3e h7b) R0 R0 (RS
    69 E) (RS 70 C)) (DPNode (MkDag 5 (bs4 hf3 hfb hfe h7f) (RS 132 D) R0 (RS 133 E) (RS 134 C)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs4 hbe h5f hfd hcb) R0 (RS 101 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4
    hff h3f hee h5f) R0 (RS 53 A) R0 R0) (DPNode (MkDag 5 (bs4 h9e h7b hfe h7f) R0 (RS 85 A) R0 R0) (DPNode (MkDag
    2 (bs4 h97 hcf h3e h7f) R0 (RS 149 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs4 hbe hff hfe h7f)
    R0 (RS 117 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs4 hbf hcf h2f hfe) R0 R0 (RS 29 E) R0) (DPNode
    (MkDag 2 (bs4 h3f h73 hfe h5f) R0 R0 R0 (RS 45 A)) (DPNode (MkDag 4 (bs4 h9f hcb hee h7e) R0 (RS 77 A) R0 R0)
    (DPNode (MkDag 6 (bs4 h3f hcf hee h5f) R0 R0 R0 (RS 141 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hfe
    h7f hfe h7f) R0 (RS 109 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs4 hf3 he7 hfe h7f) (RS 60 D) R0 R0 (RS
    61 C)) (DPNode (MkDag 6 (bs4 hf2 hfb hee h7f) (RS 92 D) R0 (RS 93 E) (RS 94 A)) DPEmpty DPEmpty) (DPNode (MkDag
    5 (bs4 h97 hcf hee h5f) R0 R0 R0 (RS 125 A)) DPEmpty DPEmpty))).

Definition dagSub_39_106 : DagPTree :=
  DPNode (MkDag 5 (bs4 hcf h3c hbe h7f) R0 R0 R0 (RS 11 D)) (DPNode (MkDag 10 (bs4 haf hff h3f h3f) R0 R0 (RS 19 E)
    R0) (DPNode (MkDag 10 (bs4 he5 hf9 he7 hf7) R0 R0 R0 (RS 35 C)) (DPNode (MkDag 2 (bs4 h9f hcb hee h5f) R0 (RS
    67 A) R0 R0) (DPNode (MkDag 0 (bs4 hf3 hcf hee h79) R0 R0 (RS 131 E) (RS 132 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 4 (bs4 hbf hcb hee h7e) R0 (RS 99 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4 hf9 hf9 hfe
    h7f) (RS 50 D) R0 R0 (RS 51 A)) (DPNode (MkDag 6 (bs4 hf3 hf9 h7e h7f) R0 R0 (RS 83 E) (RS 84 A)) (DPNode
    (MkDag 6 (bs4 h9f h9f hee h7f) R0 (RS 147 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs4 hf3 hcf hee
    h5e) R0 (RS 115 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 9 (bs4 hbf hcb hcf h9f) R0 (RS 27 C) R0 R0) (DPNode
    (MkDag 2 (bs4 h2f h73 hfe h5f) R0 R0 R0 (RS 43 C)) (DPNode (MkDag 5 (bs4 h9f hf9 h7e h7f) R0 (RS 75 A) R0 R0)
    (DPNode (MkDag 1 (bs4 hcf hcf h3f hcb) R0 R0 R0 (RS 139 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hfe
    h7b hfe h7f) R0 (RS 107 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 he7 he7 hee h7f) (RS 58 D) R0 R0 (RS
    59 A)) (DPNode (MkDag 2 (bs4 hf3 hcf h3e h5f) R0 R0 (RS 91 E) (RS 92 C)) (DPNode (MkDag 5 (bs4 h9e h5e h7e h5f)
    R0 (RS 155 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs4 h97 hcf h3e h79) R0 R0 R0 (RS 123 A))
    DPEmpty DPEmpty))).

Definition dagSub_39_107 : DagPTree :=
  DPNode (MkDag 9 (bs4 h65 hf7 h3f h9f) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 11 (bs4 haf h97 he7 hf7) R0 R0 (RS 23 E)
    R0) (DPNode (MkDag 11 (bs4 h2f h9f h7c hbf) R0 R0 R0 (RS 39 C)) (DPNode (MkDag 3 (bs4 hf2 hfb hfe h7f) (RS 70
    D) R0 (RS 71 E) (RS 72 A)) (DPNode (MkDag 4 (bs4 hbe hf9 h7e h7e) R0 R0 (RS 135 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 5 (bs4 hf3 hcf hee h5f) R0 (RS 103 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs4
    hf3 he7 hf3 hcb) R0 R0 (RS 55 E) (RS 56 C)) (DPNode (MkDag 1 (bs4 hf3 hcf h3d hcb) R0 R0 (RS 87 E) (RS 88 A))
    (DPNode (MkDag 4 (bs4 h97 hcf hee h7e) R0 (RS 151 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hbc
    hf9 h7e h7f) R0 (RS 119 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 12 (bs4 he7 hb9 hfd hcf) R0 R0 R0 (RS 31
    B)) (DPNode (MkDag 6 (bs4 hfe h7f hee h7f) R0 (RS 47 C) R0 R0) (DPNode (MkDag 7 (bs4 hf3 hcf h3e h79) R0 R0 (RS
    79 E) (RS 80 C)) (DPNode (MkDag 2 (bs4 h9f hcf h3e h5f) R0 (RS 143 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 3 (bs4 hbe h7b hfe h5f) R0 (RS 111 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs4 h3e he7 he7 hcf)
    R0 R0 R0 (RS 63 B)) (DPNode (MkDag 3 (bs4 h9e hff hfe h7f) R0 (RS 95 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag
    2 (bs4 h97 h9f hfe h5f) R0 R0 R0 (RS 127 A)) DPEmpty DPEmpty))).

Definition dagSub_39_108 : DagPTree :=
  DPNode (MkDag 6 (bs4 hcf h3c hbe h7b) R0 R0 R0 (RS 10 D)) (DPNode (MkDag 10 (bs4 h3d hff h3f h3f) R0 R0 R0 (RS 18
    C)) (DPNode (MkDag 9 (bs4 hfc hf3 hff h9f) R0 R0 R0 (RS 34 B)) (DPNode (MkDag 2 (bs4 h97 hcb hee h5f) R0 R0 R0
    (RS 66 A)) (DPNode (MkDag 1 (bs4 hff h9f hf3 hcb) (RS 129 D) R0 R0 (RS 130 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 4 (bs4 hf7 hcb hee h7e) R0 (RS 98 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4 h79 hf9 hfe
    h7f) R0 R0 R0 (RS 50 B)) (DPNode (MkDag 2 (bs4 h72 hfb hfe h5f) R0 R0 R0 (RS 80 B)) (DPNode (MkDag 6 (bs4 h97
    h9f hee h7f) R0 R0 R0 (RS 146 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs4 hfe h7f hfe h5f) R0 (RS 114
    C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 11 (bs4 h3f h97 he7 hf7) R0 R0 R0 (RS 26 A)) (DPNode (MkDag 2 (bs4
    haf h73 hfe h5f) R0 R0 (RS 42 E) R0) (DPNode (MkDag 5 (bs4 h97 hf9 h7e h7f) R0 R0 R0 (RS 74 A)) (DPNode (MkDag
    1 (bs4 h7d hcf h3f hcb) (RS 138 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hbe h7b hfe h7f)
    R0 (RS 106 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 h3e he7 hee h7f) R0 R0 R0 (RS 58 B)) (DPNode
    (MkDag 3 (bs4 h9e h7f hfe h5f) R0 R0 R0 (RS 90 C)) (DPNode (MkDag 1 (bs4 h9f h9f hfd hcb) R0 R0 R0 (RS 154 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs4 h9e h7f hfd hcb) R0 (RS 122 A) R0 R0) DPEmpty DPEmpty))).

Definition dagSub_39_109 : DagPTree :=
  DPNode (MkDag 8 (bs4 h7c hbf h3c hf2) (RS 14 E) R0 R0 R0) (DPNode (MkDag 10 (bs4 h3f hff h3f h3f) R0 R0 R0 (RS 22
    C)) (DPNode (MkDag 11 (bs4 haf h9f h7c hbf) R0 R0 (RS 38 E) R0) (DPNode (MkDag 6 (bs4 h73 hcf h3e h7b) R0 R0 R0
    (RS 68 B)) (DPNode (MkDag 5 (bs4 h73 hfb hfe h7f) R0 R0 R0 (RS 132 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    1 (bs4 hfe h5f hfd hcb) R0 (RS 102 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs4 h9f h3f hfe h5f) R0 R0 R0
    (RS 54 C)) (DPNode (MkDag 5 (bs4 h9e h7f hfe h7f) R0 R0 R0 (RS 86 C)) (DPNode (MkDag 2 (bs4 h9f hcf h3e h7f) R0
    R0 R0 (RS 150 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs4 hfe hff hfe h7f) R0 (RS 118 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 7 (bs4 h3f hcf h2f hfe) R0 R0 R0 (RS 30 B)) (DPNode (MkDag 6 (bs4 hbe h7f hee h7f) R0
    (RS 46 C) R0 R0) (DPNode (MkDag 1 (bs4 h9e h5f hfd hcb) R0 R0 R0 (RS 78 C)) (DPNode (MkDag 3 (bs4 he7 h9f hfe
    h5f) R0 R0 R0 (RS 142 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs4 hf3 hcb hee h5f) R0 (RS 110 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs4 hbe he7 he7 hcf) R0 R0 (RS 62 E) R0) (DPNode (MkDag 6 (bs4 h72 hfb hee
    h7f) R0 R0 R0 (RS 92 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs4 h9f hcf hee h5f) R0 (RS 126 A) R0 R0) DPEmpty
    DPEmpty))).

Definition dagSub_39_110 : DagPTree :=
  DPNode (MkDag 3 (bs4 hcf h3c hfe h5f) R0 R0 R0 (RS 12 D)) (DPNode (MkDag 10 (bs4 h2f hff h3f h3f) R0 R0 R0 (RS 20
    C)) (DPNode (MkDag 6 (bs4 hbc hf9 hfd hf9) R0 R0 (RS 36 E) R0) (DPNode (MkDag 4 (bs4 h9e h5f hfe h5e) R0 R0 R0
    (RS 68 C)) (DPNode (MkDag 0 (bs4 h73 hcf hee h79) R0 R0 R0 (RS 130 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    4 (bs4 hff hcb hee h7e) R0 (RS 100 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4 hbf h3f hee h5f) R0 (RS 52
    C) R0 R0) (DPNode (MkDag 6 (bs4 h73 hf9 h7e h7f) R0 R0 R0 (RS 82 B)) (DPNode (MkDag 5 (bs4 h9e h79 h7e h7f) R0
    R0 R0 (RS 148 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs4 hf3 hfb hee h7f) R0 (RS 116 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 9 (bs4 hff hcb hcf h9f) (RS 27 D) R0 R0 (RS 28 C)) (DPNode (MkDag 2 (bs4 hbf h73 hfe
    h5f) R0 R0 (RS 44 E) R0) (DPNode (MkDag 4 (bs4 h97 hcb hee h7e) R0 R0 R0 (RS 76 A)) (DPNode (MkDag 6 (bs4 hbf
    hcf hee h5f) R0 R0 (RS 140 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hbe h7f hfe h7f) R0 (RS 108
    C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs4 h9f he5 hee h7f) R0 (RS 60 C) R0 R0) (DPNode (MkDag 2 (bs4
    h73 hcf h3e h5f) R0 R0 R0 (RS 90 B)) (DPNode (MkDag 4 (bs4 hf3 hcf h3e h5e) R0 (RS 0 D) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 7 (bs4 h9f hcf h3e h79) R0 (RS 124 A) R0 R0) DPEmpty DPEmpty))).

Definition dagSub_39_111 : DagPTree :=
  DPNode (MkDag 9 (bs4 he5 hf7 h3f h9f) R0 R0 R0 (RS 16 C)) (DPNode (MkDag 11 (bs4 h2f h97 he7 hf7) R0 R0 R0 (RS 24
    C)) (DPNode (MkDag 11 (bs4 hbf h9f h7c hbf) R0 R0 (RS 40 E) R0) (DPNode (MkDag 3 (bs4 h72 hfb hfe h7f) R0 R0 R0
    (RS 70 B)) (DPNode (MkDag 4 (bs4 h3e hf9 h7e h7e) R0 R0 R0 (RS 136 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    2 (bs4 hf3 hfb hfe h5f) R0 (RS 104 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs4 h73 he7 hf3 hcb) R0 R0 R0
    (RS 54 B)) (DPNode (MkDag 1 (bs4 h73 hcf h3d hcb) R0 R0 R0 (RS 86 B)) (DPNode (MkDag 4 (bs4 h9f hcf hee h7e) R0
    R0 R0 (RS 152 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs4 hfc hf9 h7e h7f) R0 (RS 120 A) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 12 (bs4 he7 hf9 hfd hcf) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 5 (bs4 hbc hf9 hee h7f)
    R0 (RS 48 C) R0 R0) (DPNode (MkDag 7 (bs4 h73 hcf h3e h79) R0 R0 R0 (RS 78 B)) (DPNode (MkDag 4 (bs4 h97 hcf
    hee h5e) R0 R0 R0 (RS 144 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs4 hfe h7b hfe h5f) R0 (RS 112 C) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs4 he7 he7 he7 hcf) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 3 (bs4 h97 hff
    hfe h7f) R0 R0 R0 (RS 96 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs4 h9f h9f hfe h5f) R0 (RS 128 B) R0 R0)
    DPEmpty DPEmpty))).

Definition dagTree_39 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 hcf h3c hbe h79) (RS 0 D) R0 R0 (RS 1 D)) (DPNode (MkDag 1 (bs4 hcf h3c hbd hcb) R0 R0
    R0 (RS 2 D)) (DPNode (MkDag 2 (bs4 hcf h3c hfe h5f) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 4 (bs4 hcf h3c hbe h7e)
    R0 R0 R0 (RS 5 D)) dagSub_39_104 dagSub_39_105) (DPNode (MkDag 6 (bs4 hcf h3c hbe h7f) R0 R0 R0 (RS 7 D))
    dagSub_39_106 dagSub_39_107)) (DPNode (MkDag 3 (bs4 hcf h3c hbe h7f) R0 R0 R0 (RS 4 D)) (DPNode (MkDag 5 (bs4
    hcf h3c hfe h5f) R0 R0 R0 (RS 6 D)) dagSub_39_108 dagSub_39_109) (DPNode (MkDag 2 (bs4 hcf h3c hbe h7f) R0 R0
    R0 (RS 8 D)) dagSub_39_110 dagSub_39_111))).

Definition dagTree_40 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 R0 R0 (RS 0 D)) DPEmpty.

Definition dagSub_41_112 : DagPTree :=
  DPNode (MkDag 0 (bs5 h7f h3c hf2 hf9 h7d) (RS 125 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 he7 hdc hfe h79 he7) R0 R0
    R0 (RS 92 B)) (DPNode (MkDag 0 (bs5 hf2 hfc hf2 hf9 hfd) (RS 32 D) (RS 170 B) R0 (RS 170 B)) (DPNode (MkDag 0
    (bs5 hbf h2f h9e h79 he7) R0 (RS 66 C) (RS 67 E) R0) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hcf h2f) (RS 129 B) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h7f h3c hbe h5f h7f) (RS 47 B) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h97 hdc hf2 hf9 he7) R0 R0 R0 (RS 97 A)) (DPNode (MkDag 0 (bs5 h3f hfc hf3 hff h2f) R0 R0
    R0 (RS 161 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf3 hfc hf3 hf9 he7) (RS 48 D) R0 (RS 88 E) (RS
    89 C)) (DPNode (MkDag 0 (bs5 h79 h7c hf2 hf9 he7) (RS 4 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h77 h3c hf3 hcf h2f)
    R0 R0 R0 (RS 143 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hf3 hf3 hff) R0 (RS 209 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs5 hcf h3c hbe h79 he7) R0 R0 R0 (RS 27 D)) (DPNode (MkDag 0 (bs5 hff h3c hfe h5f
    h7f) R0 (RS 178 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hfb hfc hf3 hdf h2f) (RS 24 D) (RS
    85 A) R0 (RS 85 A)) (DPNode (MkDag 0 (bs5 hfe h7c hf2 hf9 h7d) (RS 40 D) R0 R0 (RS 157 C)) (DPNode (MkDag 0
    (bs5 h3f h3c hf3 hf9 hfd) R0 R0 R0 (RS 73 A)) (DPNode (MkDag 0 (bs5 h9e h7c hf3 hf3 hff) R0 (RS 28 A) R0 R0)
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h9f h2f h9e h79 he7) R0 (RS 49 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hb9 h7c hbe h79 he7) R0 (RS 105 C) R0 R0) (DPNode (MkDag 0 (bs5 hff hfc hf2 hff h2f) R0 (RS 32 C)
    R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h7e h7c hf3 hdf h2f) (RS 134 C) R0 R0 R0) (DPNode
    (MkDag 0 (bs5 h73 hfc hf3 hf9 he7) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 0 (bs5 hbc hfc hf3 hf9 h7d) R0 R0 (RS 153
    E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hcb hfc hf3 hff h2f) R0 R0 R0 (RS 12 D)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h5f h3c hf3 hdf h2f) (RS 121 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h3c hf3 hf3 hff) (RS
    53 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_113 : DagPTree :=
  DPNode (MkDag 0 (bs5 hcb hdc hf3 hf9 hfd) R0 R0 R0 (RS 217 D)) (DPNode (MkDag 0 (bs5 hcf he7 h9e h79 he7) R0 R0
    R0 (RS 113 D)) (DPNode (MkDag 0 (bs5 hf9 h7c hf2 hff h2f) (RS 36 D) R0 R0 (RS 109 A)) (DPNode (MkDag 0 (bs5 h9f
    h3c hf3 hff h2f) R0 R0 R0 (RS 18 C)) (DPNode (MkDag 0 (bs5 h5f h3c hf2 hf9 hfd) (RS 22 B) R0 R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 h7c hfc hf2 hf9 he7) R0 R0 R0 (RS 195 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs5 hf9 h7c hf3 hcf h2f) R0 R0 (RS 101 E) (RS 102 A)) (DPNode (MkDag 0 (bs5 h97 hdc hbe h5f h7f) R0 (RS 165 A)
    R0 (RS 165 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h7f h3c hbe h79 he7) (RS 131 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 hbb hfc hf3 hdf h2f) R0 (RS 24 C) R0 R0) (DPNode (MkDag 0 (bs5 h77 h3c hf2 hf9 hfd) R0 R0
    R0 (RS 30 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hf2 hf9 h7d) R0 (RS 213 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs5 h79 hfc hf3 hcf h2f) (RS 117 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hff h3c hf3 hff
    h2f) (RS 180 D) R0 R0 (RS 182 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h97 hdc hfe h79 he7) R0 R0
    R0 (RS 137 A)) (DPNode (MkDag 0 (bs5 h79 hfc hbe h79 he7) (RS 118 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79 h7c
    hf3 hf9 h7d) (RS 77 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hff hfc hfe h5f h7f) R0 (RS 17 C) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 h3f h3c hf3 hcb hff) R0 R0 R0 (RS 205 A)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs5 hb9 h7c hf2 hff h2f) R0 (RS 36 C) R0 R0) (DPNode (MkDag 0 (bs5 hff h3c hf3 hf9 h7d) (RS 172 D) R0 R0 (RS
    173 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h72 hfe h5e hf9 h7d) R0 R0 R0 (RS 59 B)) (DPNode
    (MkDag 0 (bs5 h7c hfc hfe h79 he7) (RS 93 B) R0 R0 (RS 94 B)) (DPNode (MkDag 0 (bs5 hbe h7c hf2 hf9 h7d) R0 (RS
    40 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h7f hfc hf3 hdf h2f) (RS 136 A) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h5f h3c hf2 hf9 h7d) (RS 8 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h2f h9e h79 he7) (RS 33
    B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_114 : DagPTree :=
  DPNode (MkDag 0 (bs5 h79 h7c hf2 hf9 h7d) (RS 80 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf7 h3c hf3 hf9 hfd) R0 R0
    (RS 69 E) (RS 70 C)) (DPNode (MkDag 0 (bs5 hcf hfc hf3 hcb hff) R0 R0 R0 (RS 84 A)) (DPNode (MkDag 0 (bs5 hff
    h2f h9e h79 he7) R0 (RS 68 A) R0 R0) (DPNode (MkDag 0 (bs5 h5f h3c hbe h79 he7) (RS 52 B) R0 R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 h7e h7c hf2 hf9 h7d) (RS 195 C) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs5 hbf hfc hf2 hf3 hff) R0 (RS 99 C) R0 R0) (DPNode (MkDag 0 (bs5 hf2 hfc hf3 hf9 hfd) R0 (RS 163 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hf3 hf9 h7d) (RS 50 D) R0 R0 (RS 206 A)) (DPNode
    (MkDag 0 (bs5 hcf hdc hf3 hf9 hfd) R0 R0 R0 (RS 83 D)) (DPNode (MkDag 0 (bs5 hbf h3c hbe h79 he7) R0 (RS 147 C)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hfe h79 he7) R0 (RS 51 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 hcb hdc hfe h79 he7) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 0 (bs5 h9f h3c hf2 hf9 he7) R0 R0
    R0 (RS 23 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hcf h3c hf2 hf9 h7d) R0 R0 R0 (RS 37 D))
    (DPNode (MkDag 0 (bs5 hf9 h7c hf2 hf9 hfd) R0 R0 (RS 111 E) (RS 43 D)) (DPNode (MkDag 0 (bs5 hff h3c hbe h5f
    h7f) R0 (RS 75 A) R0 R0) (DPNode (MkDag 0 (bs5 hf7 hfc hfe h5f h7f) R0 (RS 139 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 hf7 h3c hf3 hcb hff) (RS 202 D) R0 R0 (RS 203 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5
    hf9 h7c hbe h5f h7f) R0 R0 (RS 107 E) (RS 108 A)) (DPNode (MkDag 0 (bs5 h7f h3c hf3 hf9 h7d) (RS 171 B) R0 R0
    (RS 172 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hf2 hf3 hff) (RS 58 D) R0 R0 (RS 216 D))
    (DPNode (MkDag 0 (bs5 hfe h7c hf3 hf3 hff) (RS 90 D) R0 R0 (RS 154 C)) (DPNode (MkDag 0 (bs5 hbc hfc hfe h79
    he7) R0 R0 (RS 155 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h7b hfc hf3 hdf h2f) (RS 219 B) R0 R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hf9 he7) (RS 45 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h5f h3c
    hf2 hf9 he7) (RS 187 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_115 : DagPTree :=
  DPNode (MkDag 0 (bs5 hcf hfc hf3 hff h2f) R0 R0 R0 (RS 82 D)) (DPNode (MkDag 0 (bs5 h7f h3c hf2 hf9 hfd) (RS 133
    B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf hdc hf2 hf9 he7) R0 R0 R0 (RS 115 B)) (DPNode (MkDag 0 (bs5 hbf h3c hf3
    hf9 hfd) R0 (RS 71 C) (RS 72 E) R0) (DPNode (MkDag 0 (bs5 hfc hfc hf3 hf9 h7d) R0 R0 (RS 135 E) (RS 136 A))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hbf h3c hf2 hf9 he7) R0 (RS 199 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hb9 h7c hf3 hf9 hfd) R0 (RS 103 C) R0 R0) (DPNode (MkDag 0 (bs5 hbf hfc hf2 hff h2f) R0 (RS 168
    C) (RS 15 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hf2 hf9 he7) (RS 54 D) R0 R0 (RS 215
    A)) (DPNode (MkDag 0 (bs5 hf3 hdc hf3 hf9 he7) (RS 86 D) R0 (RS 87 E) (RS 48 C)) (DPNode (MkDag 0 (bs5 h3f h3c
    hf2 hf9 hfd) R0 R0 R0 (RS 151 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hf2 hf9 he7) R0 (RS 54 C) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h79 hfc hbe h5f h7f) (RS 0 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h9f
    h3c hf3 hf9 hfd) R0 (RS 183 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hf7 h3c hf2 hf9 hfd) R0
    R0 (RS 148 E) (RS 149 C)) (DPNode (MkDag 0 (bs5 h7f h3c hf2 hff h2f) (RS 132 B) R0 R0 R0) (DPNode (MkDag 0 (bs5
    h79 h7c hf3 hf3 hff) (RS 79 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h97 hcf h9e h79 he7) R0 (RS 2 A) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hf3 hf9 he7) R0 (RS 207 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs5 hf9 h7c hf3 hcb hff) R0 (RS 55 A) R0 R0) (DPNode (MkDag 0 (bs5 hf7 h3c hfe h5f h7f) (RS 174 D) (RS 175 C)
    R0 (RS 175 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h97 hcf h3c hf3 hff) R0 R0 R0 (RS 63 A))
    (DPNode (MkDag 0 (bs5 hfc hfc hfe h79 he7) R0 R0 R0 (RS 95 A)) (DPNode (MkDag 0 (bs5 h3c hfc hf2 hf9 he7) R0 R0
    R0 (RS 159 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7f h3c hf2 hf3 hff) (RS 127 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 h5f h3c hf3 hf9 hfd) (RS 191 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_116 : DagPTree :=
  DPNode (MkDag 0 (bs5 h3f h3c hf3 hcf h2f) R0 R0 R0 (RS 146 A)) (DPNode (MkDag 0 (bs5 hf2 hfc hf2 hf9 he7) R0 (RS
    141 A) R0 R0) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hff h2f) (RS 189 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h77 h2f h9e
    h79 he7) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 0 (bs5 h7f h3c hf3 hcf h2f) (RS 130 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h7f h3c hf3 hcb hff) (RS 13 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h9f hdc
    hf2 hf9 he7) R0 (RS 35 C) R0 R0) (DPNode (MkDag 0 (bs5 hb2 hfc hf3 hf9 hfd) R0 (RS 162 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf7 h3c hf3 hff h2f) (RS 49 D) R0 R0 (RS 179 C)) (DPNode (MkDag 0 (bs5
    hcf h7c hf3 hff h2f) R0 R0 R0 (RS 14 D)) (DPNode (MkDag 0 (bs5 hbf h3c hf3 hcf h2f) R0 R0 (RS 9 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs5 hf9 h7c hf3 hf3 hff) (RS 209 D) R0 R0 (RS 210 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hcf hdc hf3 hf9 h7d) R0 R0 R0 (RS 114 D)) (DPNode (MkDag 0 (bs5 h3f h3c hfe h5f h7f) R0 R0 R0 (RS
    198 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hb9 h7c hf3 hcf h2f) R0 R0 R0 (RS 100 C)) (DPNode
    (MkDag 0 (bs5 hb9 h7c hbe h5f h7f) R0 R0 R0 (RS 106 C)) (DPNode (MkDag 0 (bs5 hbf h3c hbe h5f h7f) R0 (RS 74 C)
    R0 R0) (DPNode (MkDag 0 (bs5 h9f hdc hfe h79 he7) R0 (RS 138 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5
    h9f h3c hbe h5f h7f) R0 (RS 202 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hbe h79 he7) R0 (RS
    41 A) R0 R0) (DPNode (MkDag 0 (bs5 hb2 hfc hf2 hf9 hfd) R0 (RS 32 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs5 hf9 h7c hfe h5f h7f) (RS 57 D) R0 R0 (RS 212 A)) (DPNode (MkDag 0 (bs5 hbe h7c hf3 hf3 hff) R0
    (RS 90 C) (RS 91 E) R0) (DPNode (MkDag 0 (bs5 h3c hfc hf3 hf9 h7d) R0 R0 R0 (RS 89 A)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs5 hcf hfc hbe h79 he7) R0 R0 R0 (RS 1 D)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h7f h3c hf3 hdf
    h2f) (RS 122 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h3c hfe h5f h7f) (RS 186 B) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty))).

Definition dagSub_41_117 : DagPTree :=
  DPNode (MkDag 0 (bs5 h79 h7c hf3 hdf h2f) (RS 76 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h3f h9e h79 he7) (RS 128
    B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf h3f h9e h79 he7) R0 R0 R0 (RS 112 D)) (DPNode (MkDag 0 (bs5 h77 h3c hf3
    hf9 hfd) R0 R0 R0 (RS 18 B)) (DPNode (MkDag 0 (bs5 h5e h7c hf3 hdf h2f) (RS 56 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h7f hfc hf3 hff h2f) (RS 163 A) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h79 h7c
    hf3 hcf h2f) R0 R0 R0 (RS 100 B)) (DPNode (MkDag 0 (bs5 h9f hdc hbe h5f h7f) R0 (RS 5 C) R0 (RS 5 C)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h5f h3c hfe h5f h7f) (RS 185 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h9f
    hfc hf3 hdf h2f) R0 (RS 86 C) R0 (RS 86 C)) (DPNode (MkDag 0 (bs5 hbf h3c hf2 hf9 hfd) R0 R0 (RS 150 E) R0)
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hf9 h7c hf2 hf9 h7d) (RS 213 D) R0 R0 (RS 214 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h79 hfc hf3 hf9 hfd) (RS 44 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h3f h3c hf3 hff h2f) R0 R0
    R0 (RS 70 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 h9f h3c hf2 hff h2f) R0 R0 R0 (RS 30 C))
    (DPNode (MkDag 0 (bs5 h7f h3c hf3 hf9 he7) (RS 123 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79 h7c hf3 hf9 he7) (RS
    78 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h9e h7c hf2 hf3 hff) R0 R0 R0 (RS 142 A)) DPEmpty DPEmpty) (DPNode (MkDag
    0 (bs5 hb9 h7c hf3 hf9 h7d) R0 (RS 50 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hb9 h7c hf3 hcb hff) R0
    (RS 110 C) R0 R0) (DPNode (MkDag 0 (bs5 h9f h3c hf3 hf3 hff) R0 (RS 174 C) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs5 h9e h79 hff hcf h2f) R0 (RS 62 A) R0 R0) (DPNode (MkDag 0 (bs5 h5e h7c hf2 hf9 h7d) (RS
    194 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hbc hfc hf2 hf9 he7) R0 R0 (RS 158 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs5 h5f h3c hf2 hf3 hff) (RS 126 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h3c hf3 hff h2f) (RS
    190 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_118 : DagPTree :=
  DPNode (MkDag 0 (bs5 h7f h3c hfe h79 he7) (RS 124 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79 h7c hfe h5f h7f) (RS 10
    B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf7 hfc hf2 hf3 hff) R0 (RS 98 C) R0 R0) (DPNode (MkDag 0 (bs5 h3f h2f h9e
    h79 he7) R0 R0 R0 (RS 179 A)) (DPNode (MkDag 0 (bs5 h5f h3c hf2 hff h2f) (RS 46 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 hfc hfc hf2 hf9 he7) R0 R0 (RS 196 E) (RS 197 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5
    hff hfc hf2 hf3 hff) R0 (RS 25 A) R0 R0) (DPNode (MkDag 0 (bs5 h9e h7c hbe h79 he7) R0 (RS 164 A) R0 (RS 164
    A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hfe h79 he7) (RS 51 D) R0 R0 (RS 211 A)) (DPNode
    (MkDag 0 (bs5 hcb hdc hf2 hff h2f) R0 R0 R0 (RS 34 D)) (DPNode (MkDag 0 (bs5 hff h3c hbe h79 he7) R0 (RS 29 A)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hfe h5f h7f) R0 (RS 57 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h79 hfc hf3 hff h2f) (RS 116 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hbf h3c hf3 hff h2f) R0
    (RS 180 C) (RS 181 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hcf h3c hf2 hf9 hfd) R0 R0 R0 (RS
    20 D)) (DPNode (MkDag 0 (bs5 hcf h3c hf3 hf9 he7) R0 R0 R0 (RS 26 D)) (DPNode (MkDag 0 (bs5 h9f h3c hf3 hcb
    hff) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 0 (bs5 hbf hfc hfe h5f h7f) R0 (RS 140 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 hbf h3c hf3 hcb hff) R0 R0 (RS 204 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h79 h7c
    hbe h5f h7f) R0 R0 R0 (RS 106 B)) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hf3 hff) (RS 184 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hf2 hfe h5e hf9 h7d) R0 R0 (RS 60 E) (RS 61 A)) (DPNode (MkDag 0 (bs5
    h3e h7c hf3 hf3 hff) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 0 (bs5 h3c hfc hfe h79 he7) R0 R0 R0 (RS 156 A))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h5f hfc hf3 hdf h2f) (RS 220 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 h5f h3c hfe h79 he7) (RS 11 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7f h3c hf2 hf9 he7) (RS 3 B) R0
    R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_41_119 : DagPTree :=
  DPNode (MkDag 0 (bs5 h3f hfc hf2 hff h2f) R0 R0 R0 (RS 169 A)) (DPNode (MkDag 0 (bs5 hf7 h2f h9e h79 he7) R0 (RS
    64 C) (RS 65 E) (RS 64 C)) (DPNode (MkDag 0 (bs5 h79 hfc hf2 hf9 hfd) (RS 120 B) R0 R0 R0) (DPNode (MkDag 0
    (bs5 hff h3c hf3 hf9 hfd) (RS 71 D) R0 R0 (RS 201 A)) (DPNode (MkDag 0 (bs5 h7c hfc hf3 hf9 h7d) R0 R0 R0 (RS
    134 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hff h3c hf2 hf9 he7) (RS 199 D) R0 R0 (RS 200 A)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs5 hf9 h7c hf3 hf9 hfd) (RS 103 D) R0 R0 (RS 104 A)) (DPNode (MkDag 0 (bs5 h77 hfc
    hf2 hff h2f) R0 R0 R0 (RS 5 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hb9 h7c hf2 hf9 hfd) R0 R0 R0
    (RS 42 C)) (DPNode (MkDag 0 (bs5 h73 hdc hf3 hf9 he7) R0 R0 R0 (RS 86 B)) (DPNode (MkDag 0 (bs5 hbe h7c hf3 hdf
    h2f) R0 (RS 31 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hb9 h7c hf2 hf3 hff) R0 (RS 58 C) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 h79 hfc hf3 hcb hff) (RS 39 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf7 h3c
    hbe h5f h7f) R0 (RS 73 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hfe h7c hf3 hdf h2f) (RS 31
    D) R0 R0 (RS 152 C)) (DPNode (MkDag 0 (bs5 h5f h3c hf3 hcb hff) (RS 193 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h79
    h7c hfe h79 he7) (RS 19 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hf7 h3c hf3 hcf h2f) R0 R0 (RS 144 E) (RS 145 C))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hf9 h7c hf3 hf9 he7) (RS 207 D) R0 R0 (RS 208 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 h79 h7c hf2 hf9 hfd) R0 R0 R0 (RS 42 B)) (DPNode (MkDag 0 (bs5 hbf h3c hfe h5f h7f) R0
    (RS 176 C) (RS 177 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 h9f hcf h3c hf3 hff) R0 (RS 23 C) R0
    R0) (DPNode (MkDag 0 (bs5 h9e h7c hf2 hf9 h7d) R0 (RS 96 A) R0 R0) (DPNode (MkDag 0 (bs5 hbf hfc hf3 hff h2f)
    R0 R0 (RS 160 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h5f h3f h9e h79 he7) (RS 21 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 h7f h3c hf3 hf9 hfd) (RS 7 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_41 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h79 hfc hf2 hff h2f) (RS 119 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 hcf hdc hf2 hff h2f) R0
    R0 R0 (RS 218 B)) (DPNode (MkDag 0 (bs5 h9f hcf h9e h79 he7) R0 R0 R0 (RS 143 C)) (DPNode (MkDag 0 (bs5 h79 h7c
    hf2 hf3 hff) (RS 81 D) R0 R0 R0) dagSub_41_112 dagSub_41_113) (DPNode (MkDag 0 (bs5 hcf hfc hfe h5f h7f) R0 R0
    R0 (RS 38 D)) dagSub_41_114 dagSub_41_115)) (DPNode (MkDag 0 (bs5 h5f h2f h9e h79 he7) (RS 188 B) R0 R0 R0)
    (DPNode (MkDag 0 (bs5 hf7 hfc hf2 hff h2f) R0 (RS 166 C) (RS 167 E) (RS 166 C)) dagSub_41_116 dagSub_41_117)
    (DPNode (MkDag 0 (bs5 h5f h3c hbe h5f h7f) (RS 192 B) R0 R0 R0) dagSub_41_118 dagSub_41_119))).

Definition dagSub_42_120 : DagPTree :=
  DPNode (MkDag 5 (bs5 hcf hdc hbe h79 he7) R0 R0 R0 (RS 20 D)) (DPNode (MkDag 12 (bs5 hcf he5 hee h7f h73) R0 R0
    R0 (RS 1 D)) (DPNode (MkDag 21 (bs5 hff hdc hfe he7 h9e) R0 R0 (RS 33 E) (RS 34 A)) (DPNode (MkDag 35 (bs5 hcf
    he7 h9e hff hfc) R0 R0 R0 (RS 65 D)) (DPNode (MkDag 24 (bs5 hcf hff hf7 hf9 hf3) R0 R0 R0 (RS 130 D)) DPEmpty
    DPEmpty) (DPNode (MkDag 50 (bs5 haf hcb he5 hf3 hf3) R0 R0 (RS 193 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 45
    (bs5 h7e h5f h9f hcf h3e) R0 R0 R0 (RS 95 B)) (DPNode (MkDag 7 (bs5 hff h3f h9e h79 hee) R0 (RS 188 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 8 (bs5 hfd hcb hf2 hfb hfe) R0 R0 (RS 49 E) (RS 50 A)) (DPNode (MkDag
    31 (bs5 h72 hf9 he7 hcf hcf) R0 R0 R0 (RS 79 B)) (DPNode (MkDag 15 (bs5 h3f hb9 hfc hff h2f) R0 R0 R0 (RS 145
    C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 47 (bs5 h97 hdc hfe h5f h3e) R0 R0 R0 (RS 113 A)) (DPNode (MkDag
    58 (bs5 h79 hfc hbe h79 hf3) R0 R0 R0 (RS 174 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 18 (bs5 he5 hf9
    h7c hf7 hf9) (RS 24 D) R0 R0 (RS 25 C)) (DPNode (MkDag 25 (bs5 hbe h7b h9f hcf hcf) R0 R0 (RS 41 E) R0) (DPNode
    (MkDag 39 (bs5 h9f he7 hfe h5e h7e) R0 (RS 73 C) R0 R0) (DPNode (MkDag 13 (bs5 hbf h9f h9e h5e h7e) R0 R0 (RS
    137 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hbf hf3 he5 hff h9f) R0 (RS 201 C) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 30 (bs5 hbe hff h97 hcb he7) R0 (RS 105 C) R0 R0) (DPNode (MkDag 49 (bs5 he7 hf3 hcb hcf h73) R0
    R0 R0 (RS 169 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 30 (bs5 hf3 hfb h97 hcf he7) (RS 56 D) R0 (RS 57 E)
    (RS 58 C)) (DPNode (MkDag 42 (bs5 h97 hcf h3e h79 he5) R0 (RS 89 A) R0 R0) (DPNode (MkDag 11 (bs5 hbf h3c hfd
    hcf hee) R0 (RS 17 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 50 (bs5 h9f hcf h73 hf3 hf3) R0 R0 R0 (RS
    121 A)) (DPNode (MkDag 50 (bs5 hbd hcb he5 hf3 hf3) R0 (RS 185 C) (RS 186 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_121 : DagPTree :=
  DPNode (MkDag 11 (bs5 hcb hdc hfd hcf hee) R0 R0 R0 (RS 132 D)) (DPNode (MkDag 7 (bs5 hcb hcf h9e h79 hee) R0 R0
    R0 (RS 182 C)) (DPNode (MkDag 23 (bs5 h9f hb9 hff h2f he5) R0 (RS 37 A) R0 R0) (DPNode (MkDag 38 (bs5 hbf he5
    hf3 hcb hff) R0 (RS 69 C) R0 R0) (DPNode (MkDag 52 (bs5 hcf hfc hf3 hcf hee) R0 R0 R0 (RS 133 D)) DPEmpty
    DPEmpty) (DPNode (MkDag 12 (bs5 hb9 h7c hbe h7f h73) R0 (RS 197 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 46
    (bs5 h97 hff h72 hfb hfe) R0 R0 R0 (RS 101 A)) (DPNode (MkDag 16 (bs5 hf7 h2f h73 hcb he5) R0 (RS 165 C) (RS
    166 E) (RS 165 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs5 h9f hff h97 hcf h3f) R0 (RS 53 A) R0 R0)
    (DPNode (MkDag 5 (bs5 h72 hf9 hf9 hf9 he7) R0 R0 R0 (RS 83 B)) (DPNode (MkDag 55 (bs5 h3f h3c hbf hf7 h2f) R0
    R0 R0 (RS 149 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 13 (bs5 hff hfc hfe h5e h7e) R0 (RS 117 C) R0 R0)
    (DPNode (MkDag 20 (bs5 hcb hfc hbd hcf hcf) (RS 180 D) R0 R0 (RS 181 D)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 19 (bs5 h3c hff h97 hff h9e) R0 R0 R0 (RS 29 A)) (DPNode (MkDag 26 (bs5 hfc hf9 hf3 hf9 h7f) R0 R0 (RS
    45 E) (RS 46 B)) (DPNode (MkDag 21 (bs5 hff he7 he7 hf9 h7e) R0 R0 (RS 77 E) (RS 10 C)) (DPNode (MkDag 16 (bs5
    hf3 hcb hf3 hcb he5) R0 R0 (RS 141 E) (RS 142 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 h7e h5f h9e
    h79 he7) R0 R0 R0 (RS 107 B)) (DPNode (MkDag 57 (bs5 hf9 hfc hf2 hff hf3) (RS 172 D) (RS 173 A) R0 (RS 173 A))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 31 (bs5 he7 hff h97 hcf hcf) R0 R0 R0 (RS 61 A)) (DPNode (MkDag 43
    (bs5 h97 h9f hfe h7f h3f) R0 (RS 93 A) R0 R0) (DPNode (MkDag 2 (bs5 h3f h3c hff hcf h3f) R0 R0 R0 (RS 157 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 51 (bs5 h9f hb9 hfe h7f h73) R0 R0 R0 (RS 125 B)) (DPNode (MkDag 13
    (bs5 h9f h3f h9e h5e h7e) R0 R0 R0 (RS 4 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_122 : DagPTree :=
  DPNode (MkDag 9 (bs5 hf3 hcb hff hcf h3f) R0 R0 (RS 78 E) (RS 79 C)) (DPNode (MkDag 13 (bs5 hff h3f h9e h5e h7e)
    (RS 18 D) (RS 163 A) R0 (RS 163 A)) (DPNode (MkDag 22 (bs5 h9f hf9 hff he7 h9e) R0 (RS 35 A) R0 R0) (DPNode
    (MkDag 37 (bs5 hbc hbf h2f hfe h7d) R0 R0 (RS 67 E) R0) (DPNode (MkDag 20 (bs5 hcf hfc hbd hcf hcf) R0 R0 R0
    (RS 131 D)) DPEmpty DPEmpty) (DPNode (MkDag 50 (bs5 hbf hcb he5 hf3 hf3) R0 R0 (RS 195 E) R0) DPEmpty DPEmpty))
    (DPNode (MkDag 8 (bs5 h72 hfb h9f h9f hfe) R0 R0 R0 (RS 97 B)) (DPNode (MkDag 13 (bs5 hbf h3f h9e h5e h7e) R0
    (RS 18 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs5 h9e hff h97 hcf h3f) R0 (RS 51 A) R0 R0)
    (DPNode (MkDag 40 (bs5 h72 hf9 hfc hf9 he7) R0 R0 R0 (RS 81 B)) (DPNode (MkDag 55 (bs5 h2f h3c hbf hf7 h2f) R0
    R0 R0 (RS 147 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 13 (bs5 hf7 hfc hfe h5e h7e) R0 (RS 115 C) R0 R0)
    (DPNode (MkDag 1 (bs5 hb9 hfc hbc hff hf3) R0 (RS 127 C) R0 (RS 127 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 18 (bs5 h3c hf9 h7c hff hf9) R0 R0 R0 (RS 27 C)) (DPNode (MkDag 25 (bs5 hee h7f h9f hcf hcf) R0 R0 R0
    (RS 43 B)) (DPNode (MkDag 8 (bs5 hfe he7 hf3 hfb hfe) R0 (RS 75 A) R0 R0) (DPNode (MkDag 14 (bs5 hb2 hff hf2
    hf7 h2f) R0 (RS 19 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 hbe h5f h9e h79 he7) R0 R0 R0 (RS
    107 C)) (DPNode (MkDag 50 (bs5 hcf hcb he5 hf3 hf3) R0 R0 R0 (RS 171 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 31 (bs5 hbe hff h97 hcf hcf) R0 R0 (RS 59 E) R0) (DPNode (MkDag 43 (bs5 h97 hcf hee h7f h3d) R0 (RS 91
    A) R0 R0) (DPNode (MkDag 2 (bs5 h77 h3c hff hcf h3f) R0 R0 R0 (RS 14 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 50 (bs5 h9f hcf hf3 hf3 hf3) R0 R0 R0 (RS 123 A)) (DPNode (MkDag 50 (bs5 h3d hcb he5 hf3 hf3) R0 R0 R0
    (RS 192 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_123 : DagPTree :=
  DPNode (MkDag 2 (bs5 hf7 h3c hff hcf h3f) R0 R0 (RS 154 E) (RS 155 C)) (DPNode (MkDag 16 (bs5 hff h2f h73 hcb
    he5) (RS 22 D) (RS 184 C) R0 (RS 184 C)) (DPNode (MkDag 16 (bs5 hf3 hff h9e h7e h79) R0 R0 (RS 39 E) (RS 40 C))
    (DPNode (MkDag 39 (bs5 h9e he7 hfe h5e h7e) R0 (RS 71 A) R0 R0) (DPNode (MkDag 5 (bs5 hcb hdc hbe h79 he7) R0
    R0 R0 (RS 135 D)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hb9 h7c hbc hff hf3) R0 (RS 199 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs5 hf3 hcf h97 hcf h3f) R0 (RS 103 C) R0 R0) (DPNode (MkDag 16 (bs5 h77 h2f h73
    hcb he5) R0 R0 R0 (RS 164 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 29 (bs5 hf3 hcf h97 hcf he7) R0 R0 (RS
    55 E) (RS 56 C)) (DPNode (MkDag 10 (bs5 h9f hfc hfe h79 h7e) R0 (RS 87 A) R0 R0) (DPNode (MkDag 0 (bs5 h9f h3c
    hfe h5f hfe) R0 (RS 151 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 49 (bs5 h9e h7f hf3 hcf hf3) R0 R0
    R0 (RS 119 A)) (DPNode (MkDag 13 (bs5 hff h9f h9e h5e h7e) R0 R0 (RS 183 E) (RS 19 C)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 20 (bs5 hfe he7 h9f hff h3d) R0 (RS 31 A) R0 R0) (DPNode (MkDag 27 (bs5 h79 hf3 hf3
    hcf he7) (RS 47 B) R0 R0 R0) (DPNode (MkDag 9 (bs5 h73 hcb hff hcf h3f) R0 R0 R0 (RS 10 B)) (DPNode (MkDag 54
    (bs5 hcf he5 hf3 hcb hf3) R0 R0 R0 (RS 16 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h72 hfc hf3 hff
    hee) R0 R0 R0 (RS 109 B)) (DPNode (MkDag 58 (bs5 hf9 hfc hbe h79 hf3) R0 (RS 175 A) (RS 176 E) (RS 175 A))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 33 (bs5 hf3 hcf h3f hfb hfe) (RS 62 D) R0 R0 (RS 63 D)) (DPNode
    (MkDag 44 (bs5 h7f hff h9e h79 hfe) (RS 95 C) R0 R0 R0) (DPNode (MkDag 7 (bs5 hf7 h3f h9e h79 hee) R0 (RS 7 C)
    (RS 159 E) (RS 7 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 15 (bs5 h7e h79 h7c hf7 h2f) (RS 128 D) R0 R0 (RS
    129 B)) (DPNode (MkDag 4 (bs5 hbf h3f h72 hfb hfe) R0 R0 (RS 191 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_124 : DagPTree :=
  DPNode (MkDag 8 (bs5 hbe he7 hf3 hfb hfe) R0 (RS 74 C) R0 R0) (DPNode (MkDag 11 (bs5 hff h3c hfd hcf hee) R0 (RS
    153 A) R0 R0) (DPNode (MkDag 21 (bs5 h7f hdc hfe he7 h9e) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 36 (bs5 hcf he7
    hff hf9 h7f) R0 R0 R0 (RS 66 C)) (DPNode (MkDag 15 (bs5 hfe h79 h7c hf7 h2f) (RS 129 D) (RS 180 D) (RS 126 E)
    (RS 180 D)) DPEmpty DPEmpty) (DPNode (MkDag 50 (bs5 h2f hcb he5 hf3 hf3) R0 R0 R0 (RS 194 C)) DPEmpty DPEmpty))
    (DPNode (MkDag 8 (bs5 hf2 hfb h9f h9f hfe) R0 R0 (RS 98 E) (RS 99 A)) (DPNode (MkDag 7 (bs5 h3f h3f h9e h79
    hee) R0 R0 R0 (RS 162 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 8 (bs5 h7d hcb hf2 hfb hfe) R0 R0 R0 (RS 48
    B)) (DPNode (MkDag 40 (bs5 hf2 hf9 hfc hf9 he7) R0 R0 (RS 82 E) (RS 83 C)) (DPNode (MkDag 55 (bs5 haf h3c hbf
    hf7 h2f) R0 R0 (RS 146 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 47 (bs5 h9f hdc hfe h5f h3e) R0 (RS 114
    C) R0 R0) (DPNode (MkDag 12 (bs5 hf9 hfc hbe h7f h73) R0 (RS 178 A) (RS 179 E) (RS 178 A)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 18 (bs5 hbc hf9 h7c hff hf9) R0 R0 (RS 26 E) R0) (DPNode (MkDag 25 (bs5 h3e h7b h9f
    hcf hcf) R0 R0 R0 (RS 42 B)) (DPNode (MkDag 11 (bs5 hf3 he7 hf3 hcf hee) R0 (RS 9 C) R0 R0) (DPNode (MkDag 13
    (bs5 h3f h9f h9e h5e h7e) R0 R0 R0 (RS 138 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hff hf3 he5 hff h9f) R0
    (RS 21 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 30 (bs5 hfe hff h97 hcb he7) R0 (RS 106 A) R0 R0) (DPNode
    (MkDag 50 (bs5 h7d hcb he5 hf3 hf3) (RS 170 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 30 (bs5 h73
    hfb h97 hcf he7) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 42 (bs5 h9f hcf h3e h79 he5) R0 R0 R0 (RS 90 A)) (DPNode
    (MkDag 56 (bs5 h9f h3c hbe hf9 h7e) R0 R0 R0 (RS 14 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 50 (bs5 h97
    hcf hf3 hf3 hf3) R0 (RS 122 A) R0 R0) (DPNode (MkDag 50 (bs5 hfd hcb he5 hf3 hf3) R0 (RS 187 B) R0 R0) DPEmpty
    DPEmpty) DPEmpty))).

Definition dagSub_42_125 : DagPTree :=
  DPNode (MkDag 7 (bs5 hcf hcf h9e h79 hee) R0 R0 R0 (RS 136 C)) (DPNode (MkDag 15 (bs5 hbe h79 h7c hf7 h2f) R0 (RS
    129 C) R0 (RS 129 C)) (DPNode (MkDag 24 (bs5 h9f h97 h9e h79 hf3) R0 R0 R0 (RS 38 C)) (DPNode (MkDag 38 (bs5
    hff he5 hf3 hcb hff) (RS 69 D) R0 R0 (RS 70 A)) (DPNode (MkDag 17 (bs5 hcf hdc hbd hcf h3c) R0 R0 R0 (RS 134
    D)) DPEmpty DPEmpty) (DPNode (MkDag 12 (bs5 hf9 h7c hbe h7f h73) (RS 197 D) R0 R0 (RS 198 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 46 (bs5 h9f hff h72 hfb hfe) R0 (RS 102 C) R0 R0) (DPNode (MkDag 16 (bs5 hbf h2f h73 hcb he5) R0
    (RS 22 C) (RS 167 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 9 (bs5 h9e h5f h97 hcf h3f) R0 R0 R0 (RS 54
    C)) (DPNode (MkDag 10 (bs5 h9e hfc hfe h79 h7e) R0 (RS 11 A) R0 R0) (DPNode (MkDag 6 (bs5 hbf h3c hff hb9 hfd)
    R0 (RS 6 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 48 (bs5 hf2 hfc hf3 hcb he5) R0 (RS 118 A) R0 R0)
    (DPNode (MkDag 38 (bs5 hcb hdc hff hf3 hff) R0 R0 R0 (RS 0 D)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 20
    (bs5 hbe he7 h9f hff h3d) R0 (RS 30 C) R0 R0) (DPNode (MkDag 26 (bs5 h7c hf9 hf3 hf9 h7f) R0 R0 R0 (RS 44 B))
    (DPNode (MkDag 21 (bs5 h7f he7 he7 hf9 h7e) R0 R0 R0 (RS 76 B)) (DPNode (MkDag 16 (bs5 h73 hcb hf3 hcb he5) R0
    R0 R0 (RS 140 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 hf2 hfc hf3 hff hee) R0 R0 (RS 110 E) (RS 111
    A)) (DPNode (MkDag 58 (bs5 hb9 hfc hbe h79 hf3) R0 (RS 174 C) R0 (RS 174 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 32 (bs5 h9e h5f h9f hf9 hfd) R0 (RS 62 C) R0 R0) (DPNode (MkDag 43 (bs5 h9f h9f hfe h7f h3f) R0 R0 R0
    (RS 94 B)) (DPNode (MkDag 5 (bs5 hbf h3c hbe h79 he7) R0 (RS 5 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs5 h79 hfc hbc hff hf3) (RS 126 B) R0 R0 (RS 127 B)) (DPNode (MkDag 4 (bs5 h77 h3f h72 hfb hfe) R0
    R0 R0 (RS 4 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_126 : DagPTree :=
  DPNode (MkDag 10 (bs5 h97 hfc hfe h79 h7e) R0 R0 R0 (RS 86 A)) (DPNode (MkDag 14 (bs5 hf2 hff hf2 hf7 h2f) (RS 19
    D) R0 (RS 139 E) (RS 140 C)) (DPNode (MkDag 23 (bs5 h97 hb9 hff h2f he5) R0 R0 R0 (RS 36 A)) (DPNode (MkDag 37
    (bs5 h3c hbf h2f hfe h7d) R0 R0 R0 (RS 68 A)) (DPNode (MkDag 38 (bs5 hcf hdc hff hf3 hff) R0 R0 R0 (RS 12 D))
    DPEmpty DPEmpty) (DPNode (MkDag 50 (bs5 h3f hcb he5 hf3 hf3) R0 R0 R0 (RS 196 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 46 (bs5 h9e hff h72 hfb hfe) R0 (RS 100 A) R0 R0) (DPNode (MkDag 4 (bs5 h9f h3f h72 hfb hfe) R0 (RS 164
    C) R0 (RS 164 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs5 h97 hff h97 hcf h3f) R0 R0 R0 (RS 52 A))
    (DPNode (MkDag 5 (bs5 hf2 hf9 hf9 hf9 he7) R0 R0 (RS 84 E) (RS 85 A)) (DPNode (MkDag 55 (bs5 hbf h3c hbf hf7
    h2f) R0 R0 (RS 148 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 13 (bs5 hbf hfc hfe h5e h7e) R0 (RS 116 C)
    R0 R0) (DPNode (MkDag 12 (bs5 h79 hfc hbe h7f h73) R0 R0 R0 (RS 177 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 19 (bs5 hbc hff h97 hff h9e) R0 R0 (RS 28 E) R0) (DPNode (MkDag 25 (bs5 h7e h7f h9f hcf hcf) (RS 44 C)
    R0 R0 R0) (DPNode (MkDag 21 (bs5 hbf he7 he7 hf9 h7e) R0 R0 R0 (RS 76 C)) (DPNode (MkDag 14 (bs5 h72 hff hf2
    hf7 h2f) R0 R0 R0 (RS 19 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs5 hfe h5f h9e h79 he7) R0 R0 (RS 108
    E) (RS 109 C)) (DPNode (MkDag 57 (bs5 hb9 hfc hf2 hff hf3) R0 (RS 172 C) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 31 (bs5 h3e hff h97 hcf hcf) R0 R0 R0 (RS 60 B)) (DPNode (MkDag 43 (bs5 h9f hcf hee h7f h3d) R0
    R0 R0 (RS 92 A)) (DPNode (MkDag 2 (bs5 hbf h3c hff hcf h3f) R0 R0 (RS 156 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 51 (bs5 h97 hb9 hfe h7f h73) R0 (RS 124 A) R0 R0) (DPNode (MkDag 57 (bs5 h79 hfc hf2 hff hf3) R0
    R0 R0 (RS 172 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_42_127 : DagPTree :=
  DPNode (MkDag 11 (bs5 hcf hdc hfd hcf hee) R0 R0 R0 (RS 23 D)) (DPNode (MkDag 17 (bs5 hcb hdc hbd hcf h3c) R0 R0
    R0 (RS 2 D)) (DPNode (MkDag 16 (bs5 h73 hff h9e h7e h79) R0 R0 R0 (RS 38 B)) (DPNode (MkDag 39 (bs5 h97 he7 hfe
    h5e h7e) R0 R0 R0 (RS 72 A)) (DPNode (MkDag 53 (bs5 hcf hfc hbe h5f h7e) R0 R0 R0 (RS 13 D)) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs5 hf9 h7c hbc hff hf3) R0 (RS 200 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 29 (bs5 hf3
    hfb h97 hcb he7) R0 (RS 104 C) R0 R0) (DPNode (MkDag 16 (bs5 h3f h2f h73 hcb he5) R0 R0 R0 (RS 168 B)) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 29 (bs5 h73 hcf h97 hcf he7) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 41 (bs5 h9e
    h79 h7e h7f h2f) R0 R0 R0 (RS 88 A)) (DPNode (MkDag 11 (bs5 hf7 h3c hfd hcf hee) R0 (RS 152 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 50 (bs5 h97 hcf h73 hf3 hf3) R0 (RS 120 A) R0 R0) (DPNode (MkDag 13 (bs5 h7f
    h9f h9e h5e h7e) R0 R0 R0 (RS 182 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 21 (bs5 hbf hdc hfe he7 h9e)
    R0 R0 R0 (RS 32 C)) (DPNode (MkDag 6 (bs5 h79 hf9 hf2 hf9 hfd) (RS 48 C) R0 R0 R0) (DPNode (MkDag 31 (bs5 hf2
    hf9 he7 hcf hcf) R0 R0 (RS 80 E) (RS 81 C)) (DPNode (MkDag 15 (bs5 hbf hb9 hfc hff h2f) R0 R0 (RS 144 E) R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs5 h9e h7c hfe h79 hee) R0 (RS 112 A) R0 R0) (DPNode (MkDag 12
    (bs5 hb9 hfc hbe h7f h73) R0 (RS 177 C) R0 (RS 177 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 34 (bs5 hcf
    h3c hf2 hf9 hfd) R0 R0 R0 (RS 64 D)) (DPNode (MkDag 45 (bs5 hfe h5f h9f hcf h3e) R0 R0 (RS 96 E) (RS 97 C))
    (DPNode (MkDag 7 (bs5 h77 h3f h9e h79 hee) R0 R0 R0 (RS 158 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5
    hf9 hfc hbc hff hf3) R0 (RS 21 A) (RS 125 E) (RS 21 A)) (DPNode (MkDag 4 (bs5 h3f h3f h72 hfb hfe) R0 R0 R0 (RS
    165 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_42 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hcf hfc hfe h5f hfe) R0 R0 R0 (RS 15 D)) (DPNode (MkDag 1 (bs5 hcf he7 hfc hff hf3) R0
    R0 R0 (RS 143 C)) (DPNode (MkDag 2 (bs5 hcf hfc hff hcf h3f) R0 R0 R0 (RS 8 D)) (DPNode (MkDag 4 (bs5 hf7 h3f
    h72 hfb hfe) R0 R0 (RS 189 E) (RS 190 C)) dagSub_42_120 dagSub_42_121) (DPNode (MkDag 6 (bs5 hff h3c hff hb9
    hfd) (RS 6 D) R0 R0 (RS 150 A)) dagSub_42_122 dagSub_42_123)) (DPNode (MkDag 3 (bs5 h9f h3c hf2 hff hee) R0 (RS
    158 C) R0 (RS 158 C)) (DPNode (MkDag 5 (bs5 hff h3c hbe h79 he7) (RS 5 D) (RS 3 A) R0 (RS 3 A)) dagSub_42_124
    dagSub_42_125) (DPNode (MkDag 7 (bs5 hbf h3f h9e h79 hee) R0 (RS 160 C) (RS 161 E) R0) dagSub_42_126
    dagSub_42_127))).

Definition dagTree_43 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf9 he7 hf9 h7b h9f) (RS 0 D) R0 R0 (RS 107 A)) (DPNode (MkDag 1 (bs5 hf9 h7c hff hf9
    hff) (RS 1 D) R0 R0 (RS 91 C)) (DPNode (MkDag 2 (bs5 h79 hf9 hf9 hfb h9f) (RS 85 B) R0 R0 (RS 16 B)) (DPNode
    (MkDag 4 (bs5 h73 hcb hff hcf he7) R0 R0 R0 (RS 70 B)) (DPNode (MkDag 2 (bs5 h3f h9f hf9 h7b h9f) R0 R0 R0 (RS
    99 C)) (DPNode (MkDag 2 (bs5 hf9 hf9 hf9 hfb h9f) R0 R0 (RS 2 E) (RS 110 A)) (DPNode (MkDag 14 (bs5 hbf h9e h7c
    hbf hf9) R0 R0 (RS 33 E) R0) (DPNode (MkDag 21 (bs5 h7f h97 hcf hcb hdc) R0 R0 R0 (RS 63 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h3f h97 hb9 hfb h9f) R0 R0 R0 (RS 97 C)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs5 h97 h9f
    h97 hb9 he7) R0 R0 R0 (RS 49 A)) (DPNode (MkDag 15 (bs5 hf9 he7 hf9 h7b h97) (RS 80 D) R0 R0 (RS 81 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 6 (bs5 hbf h3f hb9 hfb h9f) R0 R0 (RS 113 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 11
    (bs5 h73 hcb hf2 hf3 he7) R0 R0 R0 (RS 23 B)) (DPNode (MkDag 18 (bs5 hbd hcf he7 hff hcf) R0 R0 (RS 41 E) R0)
    (DPNode (MkDag 21 (bs5 hf2 hf9 hff hf9 hfc) (RS 72 D) (RS 14 B) (RS 74 E) (RS 14 B)) DPEmpty DPEmpty) (DPNode
    (MkDag 22 (bs5 h7f h3c hbe h7f hcf) (RS 78 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5 hfe h5f h3f hb9
    hfd) (RS 56 D) R0 (RS 57 E) (RS 58 C)) (DPNode (MkDag 7 (bs5 h7f h3f h3d hcf h3c) (RS 89 E) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs5 hf9 hf9 hf9 hfb h97) (RS 12 D) (RS 5 A) R0 (RS 5 A)) (DPNode (MkDag 9
    (bs5 h72 hf9 hfc hff hfc) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 16 (bs5 hbc hfb he7 h9f hcf) R0 (RS 37 C) R0 R0)
    (DPNode (MkDag 1 (bs5 h7f h9f hb9 h7c hff) R0 R0 R0 (RS 69 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h2f h9f
    hb9 h7c hff) R0 R0 R0 (RS 101 C)) DPEmpty DPEmpty)) (DPNode (MkDag 17 (bs5 hbe hff h9f hcb hdc) R0 (RS 53 C) R0
    R0) (DPNode (MkDag 15 (bs5 h79 hfc hf9 hff h9f) (RS 2 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1
    (bs5 hbc hf3 hf2 hfb h9f) R0 R0 (RS 29 E) R0) (DPNode (MkDag 18 (bs5 hbf hcf he7 hff hcf) R0 R0 (RS 45 E) R0)
    (DPNode (MkDag 1 (bs5 hff h3c hbe h79 hff) (RS 76 D) R0 R0 (RS 77 A)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5
    hf9 hfc hf9 hff h9f) R0 (RS 109 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hee h79 hff he7 h97) R0 R0 R0
    (RS 61 B)) (DPNode (MkDag 21 (bs5 h3f h97 hcf hcb hdc) R0 R0 R0 (RS 93 C)) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 6 (bs5 h5f h3f hb9 hfb h9f) (RS 13 B) R0 R0 R0) (DPNode (MkDag 2 (bs5 h2f h9f hf9 h7b h9f) R0 R0 R0 (RS
    98 C)) (DPNode (MkDag 9 (bs5 h72 hf9 he7 hdf hfc) R0 R0 R0 (RS 17 B)) (DPNode (MkDag 15 (bs5 hbe h7f hee h7e
    h7d) R0 (RS 35 C) R0 R0) (DPNode (MkDag 2 (bs5 hfb h9f hf9 h7b h9f) R0 R0 R0 (RS 67 A)) DPEmpty DPEmpty)
    (DPNode (MkDag 2 (bs5 hbf h9f hf9 h7b h9f) R0 R0 (RS 8 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 16 (bs5 hf3 hcf
    h9f hcb hff) R0 (RS 51 C) R0 R0) (DPNode (MkDag 23 (bs5 hf9 hfc hf9 hff h97) (RS 82 D) R0 R0 (RS 83 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 7 (bs5 hbf h3f h3d hcf h3c) R0 (RS 9 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 13
    (bs5 h65 hf9 hff h9f h97) R0 R0 R0 (RS 27 B)) (DPNode (MkDag 18 (bs5 haf hcf he7 hff hcf) R0 R0 (RS 43 E) R0)
    (DPNode (MkDag 21 (bs5 h72 hf9 hff hf9 hfc) R0 R0 R0 (RS 72 B)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs5 h7f h3c
    hf3 hf7 h2f) (RS 7 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 20 (bs5 hbe h5e h7f hf3 hff) R0 R0 (RS 59 E)
    R0) (DPNode (MkDag 21 (bs5 h9e h79 hfc hf9 hfc) R0 (RS 62 B) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag
    1 (bs5 h7f h3c hbe h79 hff) (RS 75 B) R0 R0 (RS 76 B)) (DPNode (MkDag 10 (bs5 h72 hf9 hfb h9f he5) R0 R0 R0 (RS
    21 B)) (DPNode (MkDag 17 (bs5 h79 hf3 he5 hf7 h3c) R0 R0 R0 (RS 39 B)) (DPNode (MkDag 4 (bs5 hf3 hcb hff hcf
    he7) (RS 70 D) (RS 71 C) (RS 4 E) (RS 71 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h3f h9f hb9 h7c hff) R0 R0
    R0 (RS 103 A)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 hfe h5f h9f h9f h97) R0 R0 (RS 55 E) (RS 56 C)) (DPNode
    (MkDag 1 (bs5 h7f h3c hf9 hfc hff) (RS 6 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs5 haf h9e
    h7c hbf hf9) R0 R0 (RS 31 E) R0) (DPNode (MkDag 15 (bs5 he7 h9f h97 hcf h3f) R0 R0 R0 (RS 47 A)) (DPNode (MkDag
    15 (bs5 h79 he7 hf9 h7b h97) (RS 79 B) R0 R0 (RS 80 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h9f h3c hf9 hfc
    hff) R0 (RS 111 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs5 h79 h7c hff hf9 hff) (RS 63 C) R0 R0 (RS 1
    B)) (DPNode (MkDag 0 (bs5 h2f h97 hb9 hfb h9f) R0 R0 R0 (RS 95 C)) DPEmpty DPEmpty) DPEmpty))))) (DPNode (MkDag
    3 (bs5 hbe h5f h9f h9f h97) R0 R0 R0 (RS 54 C)) (DPNode (MkDag 5 (bs5 h9f h3c hf3 hf7 h2f) R0 (RS 7 B) R0 (RS 7
    B)) (DPNode (MkDag 7 (bs5 hff h3f h3d hcf h3c) (RS 9 D) R0 R0 (RS 15 B)) (DPNode (MkDag 9 (bs5 hf2 hf9 he7 hdf
    hfc) R0 R0 (RS 18 E) (RS 19 C)) (DPNode (MkDag 14 (bs5 h3f h9e h7c hbf hf9) R0 R0 R0 (RS 34 A)) (DPNode (MkDag
    2 (bs5 h7b h9f hf9 h7b h9f) R0 R0 R0 (RS 66 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 haf h9f hf9 h7b h9f) R0
    R0 (RS 10 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs5 h9f h9f h97 hb9 he7) R0 (RS 50 C) R0 R0) (DPNode
    (MkDag 23 (bs5 hb9 hfc hf9 hff h97) R0 (RS 82 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5 h3f h3f hb9 hfb
    h9f) R0 R0 R0 (RS 114 A)) DPEmpty DPEmpty))) (DPNode (MkDag 12 (bs5 h7f hff hfe h7b h97) (RS 26 E) R0 R0 R0)
    (DPNode (MkDag 18 (bs5 h3d hcf he7 hff hcf) R0 R0 R0 (RS 42 C)) (DPNode (MkDag 21 (bs5 h72 hf9 hef hf9 hfc) R0
    R0 R0 (RS 71 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs5 h79 hf9 hf9 hfb h97) (RS 11 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 8 (bs5 h7e h5f h3f hb9 hfd) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 4 (bs5 h67 h9f hcf hcf
    he7) R0 R0 R0 (RS 15 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 6 (bs5 h7f h3f hb9 hfb h9f) (RS 87 B) R0 R0
    R0) (DPNode (MkDag 10 (bs5 hf2 hf9 hfb h9f he5) R0 R0 (RS 22 E) (RS 23 C)) (DPNode (MkDag 16 (bs5 hfc hfb he7
    h9f hcf) R0 (RS 38 B) R0 R0) (DPNode (MkDag 1 (bs5 hff h9f hb9 h7c hff) R0 R0 R0 (RS 70 C)) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs5 hbf h9f hb9 h7c hff) R0 R0 (RS 102 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 17 (bs5 hfe
    hff h9f hcb hdc) R0 (RS 3 A) R0 R0) (DPNode (MkDag 1 (bs5 h5f h3c hf9 hfc hff) (RS 86 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 h3c hf3 hf2 hfb h9f) R0 R0 R0 (RS 30 C)) (DPNode (MkDag 18 (bs5 h3f
    hcf he7 hff hcf) R0 R0 R0 (RS 46 B)) (DPNode (MkDag 22 (bs5 h9f h3c hbe h7f hcf) R0 (RS 78 B) R0 R0) DPEmpty
    DPEmpty) (DPNode (MkDag 2 (bs5 hb9 hf9 hf9 hfb h9f) R0 R0 R0 (RS 16 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5
    h7e h79 hff he7 h97) (RS 62 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 haf h97 hb9 hfb h9f) R0 R0 (RS 94 E) R0) DPEmpty
    DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs5 h79 he7 hf9 h7b h9f) (RS 84 B) R0 R0 (RS 0 B)) (DPNode (MkDag 5 (bs5
    h5f h3c hf3 hf7 h2f) (RS 106 B) R0 R0 R0) (DPNode (MkDag 9 (bs5 hf2 hf9 hfc hff hfc) (RS 19 D) R0 (RS 20 E) (RS
    21 C)) (DPNode (MkDag 15 (bs5 hfe h7f hee h7e h7d) R0 (RS 36 C) R0 R0) (DPNode (MkDag 2 (bs5 h9f h9f hf9 h7b
    h9f) R0 (RS 68 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 haf h9f hb9 h7c hff) R0 R0 (RS 100 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs5 hf3 hfb h9f hcb he7) R0 (RS 52 C) R0 R0) (DPNode (MkDag 8 (bs5 hb9 hf9
    hf9 hfb h97) R0 (RS 12 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 13 (bs5 he5 hf9 hff h9f h97) R0 R0
    R0 (RS 28 C)) (DPNode (MkDag 18 (bs5 h2f hcf he7 hff hcf) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 22 (bs5 h5f h3c
    hbe h7f hcf) (RS 104 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5 hb9 hfc hf9 hff h9f) R0 (RS 108 C) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 20 (bs5 h3e h5e h7f hf3 hff) R0 R0 R0 (RS 60 B)) (DPNode (MkDag 21 (bs5
    hbf h97 hcf hcb hdc) R0 R0 (RS 92 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 4 (bs5 he7 h9f hcf hcf he7)
    (RS 15 D) R0 R0 (RS 90 A)) (DPNode (MkDag 11 (bs5 hf3 hcb hf2 hf3 he7) (RS 23 D) R0 (RS 24 E) (RS 25 B))
    (DPNode (MkDag 17 (bs5 hf9 hf3 he5 hf7 h3c) (RS 39 D) R0 R0 (RS 40 C)) (DPNode (MkDag 21 (bs5 hf2 hf9 hef hf9
    hfc) R0 (RS 72 C) (RS 73 E) (RS 72 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs5 hb3 hcb hff hcf he7) R0 (RS 70 C)
    R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5 h7e h5f h9f h9f h97) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 7 (bs5
    h5f h3f h3d hcf h3c) (RS 88 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 14 (bs5 h2f h9e h7c hbf hf9)
    R0 R0 R0 (RS 32 C)) (DPNode (MkDag 2 (bs5 h9f hcf h97 hcf hcf) R0 (RS 48 A) R0 R0) (DPNode (MkDag 23 (bs5 h79
    hfc hf9 hff h97) (RS 105 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5 hf7 h3f hb9 hfb h9f) (RS 111 D) R0
    R0 (RS 112 C)) DPEmpty DPEmpty)) (DPNode (MkDag 21 (bs5 hff h97 hcf hcb hdc) R0 R0 (RS 64 E) (RS 65 B)) (DPNode
    (MkDag 0 (bs5 hbf h97 hb9 hfb h9f) R0 R0 (RS 96 E) R0) DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_44 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf7 h3c hbe h7f h3e) R0 R0 (RS 45 E) (RS 46 C)) (DPNode (MkDag 1 (bs5 hb9 hfd hcb hf3
    hcb) R0 (RS 3 C) R0 (RS 3 C)) (DPNode (MkDag 2 (bs5 he5 hf9 hfe h7f hfe) (RS 2 D) R0 R0 (RS 49 C)) (DPNode
    (MkDag 3 (bs5 h9f h2f hf2 hf3 hcf) R0 (RS 5 A) R0 R0) (DPNode (MkDag 5 (bs5 hff h3e hf9 h7f h2f) (RS 8 D) R0 R0
    (RS 9 A)) (DPNode (MkDag 9 (bs5 hf2 hf9 hf9 he7 h97) R0 R0 (RS 17 E) (RS 18 B)) (DPNode (MkDag 2 (bs5 hbf hf9
    hfe h7f hfe) R0 (RS 33 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h79 hfd hcb hf3 hcb) R0 R0 R0 (RS 3 B))
    DPEmpty DPEmpty)) (DPNode (MkDag 12 (bs5 hcb hcf hfe h7f hf3) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 9 (bs5 hff h3f
    hf3 hcf h3f) R0 (RS 42 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 13 (bs5 hfe h7d hcf hfb h9e) R0 (RS 1 A) R0
    R0) DPEmpty DPEmpty))) (DPNode (MkDag 7 (bs5 h7f h97 hf3 hcb hee) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 11 (bs5
    hb9 h7f hfe h5f h9e) R0 (RS 21 C) R0 R0) (DPNode (MkDag 16 (bs5 h9f h2f h72 hf9 h79) R0 (RS 37 C) R0 (RS 37 C))
    DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5 h3c hff hf9 hfc hf3) R0 R0 R0 (RS 53 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 14 (bs5 hb9 h7e h5f h7f hfe) R0 (RS 29 C) R0 R0) (DPNode (MkDag 13 (bs5 h9f hcf hcf hfb h9e) R0 R0 R0
    (RS 0 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 4 (bs5 h9f hf3 hcf hee h5f) R0 (RS 7 B) R0 R0) (DPNode
    (MkDag 6 (bs5 h97 he7 he7 hcb hee) R0 R0 R0 (RS 11 A)) (DPNode (MkDag 10 (bs5 h7f h2f hb9 hf9 hff) R0 R0 R0 (RS
    19 B)) (DPNode (MkDag 15 (bs5 h7c hbf hf9 hfc hf3) R0 R0 R0 (RS 35 B)) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs5
    h3c hf9 hff he7 h9f) R0 R0 R0 (RS 51 C)) DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs5 h7c hbf hf7 h3f h9e) R0 R0 R0
    (RS 25 B)) (DPNode (MkDag 13 (bs5 h9e h7d hcf hfb h9e) R0 R0 R0 (RS 43 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 8 (bs5 hf2 hf9 h7f he7 h9f) R0 R0 (RS 15 E) (RS 16 C)) (DPNode (MkDag 9 (bs5 hf3 hcf hf3 hcf h3f) R0 R0
    (RS 23 E) (RS 24 D)) (DPNode (MkDag 9 (bs5 hbf h3f hf3 hcf h3f) R0 (RS 40 C) (RS 41 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 1 (bs5 hff h3c hf2 hf3 hf9) (RS 54 D) (RS 36 A) R0 (RS 36 A)) DPEmpty DPEmpty)) (DPNode (MkDag 2
    (bs5 hb9 h79 hee h7f hfe) R0 (RS 31 C) R0 R0) (DPNode (MkDag 0 (bs5 hbf h3c hbe h7f h3e) R0 R0 (RS 47 E) R0)
    DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 1 (bs5 hf9 hfd hcb hf3 hcb) (RS 3 D) R0 (RS 48 E) (RS 2 B)) (DPNode
    (MkDag 4 (bs5 h97 hf3 hcf hee h5f) R0 R0 R0 (RS 6 A)) (DPNode (MkDag 6 (bs5 h9e he7 he7 hcb hee) R0 (RS 10 A)
    R0 R0) (DPNode (MkDag 9 (bs5 h72 hf9 hf9 he7 h97) R0 R0 R0 (RS 16 B)) (DPNode (MkDag 2 (bs5 hff hf9 hfe h7f
    hfe) R0 (RS 34 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 8 (bs5 hbc hf9 hff he7 h9f) R0 R0 (RS 50 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 13 (bs5 hfc hbf hf7 h3f h9e) R0 R0 (RS 26 E) (RS 27 B)) (DPNode (MkDag 9 (bs5
    h3f h3f hf3 hcf h3f) R0 R0 R0 (RS 55 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 7 (bs5 hff h97 hf3 hcb hee)
    (RS 13 D) R0 R0 (RS 14 C)) (DPNode (MkDag 11 (bs5 hf9 h7f hfe h5f h9e) (RS 21 D) R0 R0 (RS 22 C)) (DPNode
    (MkDag 9 (bs5 hf7 h3f hf3 hcf h3f) R0 (RS 38 C) (RS 39 E) (RS 38 C)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hbf
    h3c hf2 hf3 hf9) R0 (RS 54 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 14 (bs5 hf9 h7e h5f h7f hfe) (RS 29 D) R0
    R0 (RS 30 A)) (DPNode (MkDag 0 (bs5 h77 h3c hbe h7f h3e) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 5 (bs5 h7f h3e hf9 h7f h2f) R0 R0 R0 (RS 8 B)) (DPNode (MkDag 6 (bs5 h9f he7 he7 hcb hee) R0 (RS 12 B)
    R0 R0) (DPNode (MkDag 10 (bs5 hff h2f hb9 hf9 hff) R0 R0 R0 (RS 20 A)) (DPNode (MkDag 15 (bs5 hfc hbf hf9 hfc
    hf3) (RS 35 D) R0 R0 (RS 36 A)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs5 hbc hff hf9 hfc hf3) R0 R0 (RS 52 E)
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 he7 he5 hf9 h7c hfd) R0 R0 R0 (RS 28 A)) (DPNode (MkDag 13 (bs5 h97
    hcf hcf hfb h9e) R0 (RS 44 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 8 (bs5 h72 hf9 h7f he7 h9f) R0
    R0 R0 (RS 14 B)) (DPNode (MkDag 9 (bs5 h73 hcf hf3 hcf h3f) R0 R0 R0 (RS 22 B)) (DPNode (MkDag 9 (bs5 h77 h3f
    hf3 hcf h3f) R0 R0 R0 (RS 37 B)) DPEmpty DPEmpty) (DPNode (MkDag 13 (bs5 hbe h7d hcf hfb h9e) R0 (RS 56 C) R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hf9 h79 hee h7f hfe) R0 (RS 32 C) R0 R0) (DPNode (MkDag 0 (bs5 h3f
    h3c hbe h7f h3e) R0 R0 R0 (RS 1 A)) DPEmpty DPEmpty) DPEmpty))))).

Definition dagTree_45 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hb3 hcb hef hcb he7) R0 (RS 5 C) R0 R0) (DPNode (MkDag 1 (bs5 hbe h5f h3f hcb hff) R0
    (RS 2 C) R0 R0) (DPNode (MkDag 1 (bs5 hfe h5f h3f hcb hff) (RS 2 D) (RS 3 C) (RS 66 E) (RS 3 C)) (DPNode (MkDag
    0 (bs5 hfe h5e h7f hcb he7) R0 (RS 5 C) R0 R0) (DPNode (MkDag 2 (bs5 hbe h7f he5 hff hcf) R0 (RS 9 C) R0 R0)
    (DPNode (MkDag 1 (bs5 hbe h7f h3f hcb hff) R0 (RS 17 C) (RS 71 E) R0) (DPNode (MkDag 1 (bs5 h97 h9f h3d hcb
    hff) R0 (RS 33 A) R0 R0) (DPNode (MkDag 1 (bs5 hfc hbf h3f hcb hff) (RS 64 D) R0 (RS 65 E) (RS 1 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbf hfe h7f hcb he7) R0 R0 (RS 49 E) R0) (DPNode (MkDag 0 (bs5 h7e h7e
    h7f hcb he7) (RS 21 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs5 hfe h79 h7f hcb he7) R0 (RS
    25 C) R0 R0) (DPNode (MkDag 1 (bs5 h5f h3f h2f hcb hff) (RS 41 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h7d hcb hef
    hcb he7) R0 R0 R0 (RS 21 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbf hcf hef hcb he7) R0 R0 (RS 59
    E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 hbe h79 he5 hff hcf) R0 (RS 13 C) (RS 70 E) R0) (DPNode (MkDag
    0 (bs5 hbd hcb hef hcb he7) R0 (RS 21 C) R0 R0) (DPNode (MkDag 1 (bs5 h7f hcf h3f hcb hff) (RS 37 C) R0 R0 R0)
    (DPNode (MkDag 2 (bs5 h3e h7b he5 hff hcf) R0 R0 R0 (RS 75 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5
    h7f h9f he5 hff hcf) R0 R0 R0 (RS 51 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 hf7 h2f hff hcb he7) R0 (RS 29
    C) R0 R0) (DPNode (MkDag 0 (bs5 hbd hfe h7f hcb he7) R0 R0 (RS 45 E) R0) (DPNode (MkDag 2 (bs5 h7e h7f he5 hff
    hcf) (RS 11 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 he7 h9f he5 hff hcf) R0 R0 R0 (RS 61
    B)) DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs5 hbe h7b he5 hff hcf) R0 (RS 7 C) (RS 68 E) R0) (DPNode (MkDag 1
    (bs5 hbe h7f h2f hcb hff) R0 (RS 11 C) R0 R0) (DPNode (MkDag 0 (bs5 hbe h7e h7f hcb he7) R0 (RS 19 C) R0 R0)
    (DPNode (MkDag 1 (bs5 h7f h3f h3f hcb hff) (RS 35 B) R0 R0 R0) (DPNode (MkDag 1 (bs5 h7e h5f h3f hcb hff) R0 R0
    R0 (RS 2 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hfd hcf hef hcb he7) R0 R0 R0 (RS 51 C)) (DPNode
    (MkDag 1 (bs5 h7e h5f h3d hcb hff) (RS 2 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 hfe h5f
    h3d hcb hff) R0 (RS 1 C) R0 R0) (DPNode (MkDag 1 (bs5 h65 hf7 h3f hcb hff) R0 R0 R0 (RS 43 B)) (DPNode (MkDag 0
    (bs5 h3e h79 h7f hcb he7) R0 R0 R0 (RS 81 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7d hcf hef hcb
    he7) R0 R0 R0 (RS 50 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs5 hbe h7f h3d hcb hff) R0 (RS 15 C) R0 R0)
    (DPNode (MkDag 1 (bs5 hfe h5f h2f hcb hff) R0 (RS 23 C) (RS 73 E) (RS 23 C)) (DPNode (MkDag 2 (bs5 h7c hfb he5
    hff hcf) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 2 (bs5 h3e h79 he5 hff hcf) R0 R0 R0 (RS 77 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs5 h7f h9f h3d hcb hff) R0 R0 R0 (RS 53 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5
    hff h2f hff hcb he7) R0 (RS 31 A) R0 R0) (DPNode (MkDag 0 (bs5 haf hfe h7f hcb he7) R0 R0 (RS 47 E) R0) (DPNode
    (MkDag 1 (bs5 h7e h7f h3d hcb hff) R0 R0 R0 (RS 15 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 h7d hf9
    he5 hff hcf) R0 R0 R0 (RS 63 B)) DPEmpty DPEmpty))))) (DPNode (MkDag 0 (bs5 hbe h5e h7f hcb he7) R0 (RS 4 C)
    (RS 67 E) R0) (DPNode (MkDag 0 (bs5 hf3 hcb hef hcb he7) (RS 5 D) (RS 6 C) R0 (RS 6 C)) (DPNode (MkDag 2 (bs5
    hfe h7f he5 hff hcf) R0 (RS 10 C) R0 R0) (DPNode (MkDag 1 (bs5 hfe h7f h3f hcb hff) R0 (RS 18 C) R0 R0) (DPNode
    (MkDag 1 (bs5 h9f h9f h3d hcb hff) R0 R0 R0 (RS 34 B)) (DPNode (MkDag 1 (bs5 h7c hbf h3f hcb hff) R0 R0 R0 (RS
    64 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3f hfe h7f hcb he7) R0 R0 R0 (RS 57 B)) (DPNode (MkDag
    1 (bs5 hee h5f h3d hcb hff) (RS 81 D) R0 R0 (RS 82 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 hbe h5f
    h3d hcb hff) R0 (RS 26 C) R0 R0) (DPNode (MkDag 1 (bs5 h7f h3f h2f hcb hff) (RS 42 E) R0 R0 R0) (DPNode (MkDag
    1 (bs5 h7e h5f h2f hcb hff) R0 R0 R0 (RS 22 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 he7 hcf h3f hcb
    hff) R0 R0 R0 (RS 58 B)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 hfe h79 he5 hff hcf) R0 (RS 14 C) R0 R0)
    (DPNode (MkDag 0 (bs5 hfd hcb hef hcb he7) R0 (RS 22 C) (RS 72 E) (RS 22 C)) (DPNode (MkDag 2 (bs5 hfc hfb he5
    hff hcf) R0 R0 (RS 38 E) (RS 39 B)) (DPNode (MkDag 1 (bs5 h7e h7f h2f hcb hff) R0 R0 R0 (RS 11 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hff h9f h3d hcb hff) R0 R0 (RS 54 E) (RS 55 D)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs5 hbf h2f hff hcb he7) R0 (RS 30 C) R0 R0) (DPNode (MkDag 0 (bs5 h3d hfe h7f hcb he7) R0 R0
    R0 (RS 46 C)) (DPNode (MkDag 1 (bs5 hee h7f h3d hcb hff) R0 R0 R0 (RS 78 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs5 he7 hf7 h2f hcb hff) R0 R0 R0 (RS 62 B)) DPEmpty DPEmpty)))) (DPNode (MkDag 2 (bs5 hfe h7b he5
    hff hcf) R0 (RS 8 C) R0 R0) (DPNode (MkDag 1 (bs5 hfe h7f h2f hcb hff) R0 (RS 12 C) (RS 69 E) (RS 12 C))
    (DPNode (MkDag 0 (bs5 hfe h7e h7f hcb he7) R0 (RS 20 C) R0 R0) (DPNode (MkDag 1 (bs5 h5f hcf h3f hcb hff) (RS
    36 B) R0 R0 R0) (DPNode (MkDag 0 (bs5 h3e h5e h7f hcb he7) R0 R0 R0 (RS 0 A)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 2 (bs5 hff h9f he5 hff hcf) (RS 51 D) R0 (RS 52 E) (RS 53 C)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs5
    h9f h2f hfd hcb hcf) R0 (RS 28 C) R0 R0) (DPNode (MkDag 1 (bs5 he5 hf7 h3f hcb hff) R0 R0 R0 (RS 44 C)) (DPNode
    (MkDag 2 (bs5 hee h7f he5 hff hcf) R0 R0 R0 (RS 76 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3f hcf
    hef hcb he7) R0 R0 R0 (RS 60 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs5 hfe h7f h3d hcb hff) R0 (RS 16 C) R0
    (RS 16 C)) (DPNode (MkDag 0 (bs5 hbe h79 h7f hcb he7) R0 (RS 24 C) (RS 74 E) R0) (DPNode (MkDag 1 (bs5 h79 hf7
    h2f hcb hff) (RS 40 B) R0 R0 R0) (DPNode (MkDag 1 (bs5 h3e h7f h3f hcb hff) R0 R0 R0 (RS 79 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hcf hcf h3f hcb hff) R0 R0 R0 (RS 56 C)) DPEmpty DPEmpty)) (DPNode
    (MkDag 1 (bs5 h9f h3f h2f hcb hff) R0 R0 R0 (RS 32 A)) (DPNode (MkDag 0 (bs5 h2f hfe h7f hcb he7) R0 R0 R0 (RS
    48 C)) (DPNode (MkDag 0 (bs5 hee h7e h7f hcb he7) (RS 79 D) R0 R0 (RS 80 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 2 (bs5 hfd hf9 he5 hff hcf) R0 R0 R0 (RS 64 C)) DPEmpty DPEmpty)))))).

Definition dagTree_46 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 0 C) R0 R0) DPEmpty.

Definition dagTree_47 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 hcf hcf hff h3c) R0 R0 R0 (RS 50 A)) (DPNode (MkDag 0 (bs4 hcb hcf hff h3c) R0 R0 R0 (RS
    48 B)) (DPNode (MkDag 0 (bs4 hcf h3c hbf h3c) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 0 (bs4 hcf hfc hbf h3c) R0 R0
    R0 (RS 8 D)) (DPNode (MkDag 0 (bs4 hcf he5 hf7 h3c) R0 R0 R0 (RS 2 D)) (DPNode (MkDag 0 (bs4 h97 he7 hf7 h3c)
    R0 R0 R0 (RS 46 A)) (DPNode (MkDag 0 (bs4 he7 he5 hf7 h3c) R0 R0 R0 (RS 33 A)) DPEmpty DPEmpty) (DPNode (MkDag
    0 (bs4 h79 he7 h9f h3c) (RS 49 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 hf9 he7 hf7 h3c) (RS 24 D)
    (RS 14 A) R0 (RS 14 A)) (DPNode (MkDag 0 (bs4 h9f hcf hff h3c) R0 (RS 41 B) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs4 hcb he5 hf7 h3c) R0 R0 R0 (RS 5 D)) (DPNode (MkDag 0 (bs4 h3f hcf h3f h3c) R0 R0 R0 (RS
    21 A)) (DPNode (MkDag 0 (bs4 hbf hcf hff h3c) R0 R0 R0 (RS 37 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs4 hf3 hfc hbf h3c) (RS 28 D) (RS 29 C) R0 (RS 29 C)) (DPNode (MkDag 0 (bs4 h7f h3c hbf h3c) R0 R0 R0 (RS 43
    B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs4 hcf he7 h9f h3c) R0 R0 R0 (RS 10 D)) (DPNode (MkDag 0
    (bs4 hcf he7 hf7 h3c) R0 R0 R0 (RS 0 D)) (DPNode (MkDag 0 (bs4 hcb hfc hbf h3c) R0 R0 R0 (RS 12 D)) (DPNode
    (MkDag 0 (bs4 hfe he7 hf7 h3c) R0 (RS 36 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hb9 he7 h9f h3c) R0
    (RS 51 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h79 hfd hff h3c) R0 R0 R0 (RS 25 B)) (DPNode (MkDag 0
    (bs4 hbf h3c hbf h3c) R0 R0 R0 (RS 43 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 hb9 hfd hff h3c) R0
    (RS 25 C) R0 (RS 25 C)) (DPNode (MkDag 0 (bs4 hff h2f h3f h3c) (RS 22 D) R0 R0 (RS 23 A)) (DPNode (MkDag 0 (bs4
    h7f hcf hff h3c) R0 R0 R0 (RS 37 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hfe he5 hf7 h3c) R0 (RS 42
    A) R0 R0) (DPNode (MkDag 0 (bs4 h9f he7 hf7 h3c) R0 (RS 47 C) R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 0 (bs4 hcb he7 hf7 h3c) (RS 3 D) R0 R0 (RS 1 D)) (DPNode (MkDag 0 (bs4 hcf h2f hff h3c) R0 R0 R0 (RS 9
    D)) (DPNode (MkDag 0 (bs4 hcb he7 h9f h3c) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 0 (bs4 hf9 h7d hff h3c) R0 R0 (RS
    49 E) (RS 18 D)) (DPNode (MkDag 0 (bs4 h9f h3c hbf h3c) R0 (RS 15 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs4 h79 h7d hff h3c) (RS 11 D) R0 R0 (RS 17 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 hf9 hfd hff h3c) (RS
    25 D) R0 (RS 26 E) (RS 27 A)) (DPNode (MkDag 0 (bs4 h79 he7 hf7 h3c) R0 R0 R0 (RS 24 B)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs4 hbe he7 hf7 h3c) R0 (RS 34 C) (RS 35 E) R0) (DPNode (MkDag 0 (bs4 hbf h2f h3f
    h3c) R0 (RS 22 C) R0 R0) (DPNode (MkDag 0 (bs4 hff hcf hff h3c) R0 R0 (RS 38 E) (RS 23 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs4 hbe he5 hf7 h3c) R0 (RS 30 C) (RS 31 E) R0) (DPNode (MkDag 0 (bs4 h9e he7 hf7
    h3c) R0 (RS 16 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs4 hb9 h7d hff h3c) R0 R0 R0 (RS 17 C))
    (DPNode (MkDag 0 (bs4 hcf h7c hbf h3c) R0 R0 R0 (RS 4 D)) (DPNode (MkDag 0 (bs4 hbf hcf h3f h3c) R0 R0 (RS 20
    E) R0) (DPNode (MkDag 0 (bs4 h3e he7 hf7 h3c) R0 R0 R0 (RS 39 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hf9
    he7 h9f h3c) R0 (RS 7 A) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h9f h7c hbf h3c) R0 (RS 28 C) R0 R0)
    (DPNode (MkDag 0 (bs4 hff h3c hbf h3c) R0 R0 (RS 44 E) (RS 45 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs4 hf3 he7 h9f h3c) (RS 15 D) (RS 13 C) R0 (RS 13 C)) (DPNode (MkDag 0 (bs4 hb9 he7 hf7 h3c) R0 (RS 24 C) R0
    R0) (DPNode (MkDag 0 (bs4 he7 he7 hf7 h3c) R0 R0 R0 (RS 40 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4
    h3e he5 hf7 h3c) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 0 (bs4 hf3 hcf hff h3c) R0 (RS 3 D) R0 R0) DPEmpty DPEmpty)
    DPEmpty))))).

Definition dagTree_48 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 he7 he7 hf9 hfd) R0 (RS 1 A) R0 (RS 1 A)) (DPNode (MkDag 1 (bs4 h9e h5e h79 he7) R0 (RS
    2 A) R0 (RS 2 A)) (DPNode (MkDag 2 (bs4 h9e h79 he7 h97) R0 (RS 3 A) R0 (RS 3 A)) (DPNode (MkDag 0 (bs4 h9e h79
    he7 h97) R0 (RS 5 A) R0 (RS 5 A)) (DPNode (MkDag 1 (bs4 h9e h79 he7 h9f) R0 (RS 9 A) R0 (RS 9 A)) (DPNode
    (MkDag 14 (bs4 hcf h9e h7f h2f) R0 R0 R0 (RS 17 A)) (DPNode (MkDag 7 (bs4 h3f hf3 hcf hff) R0 R0 R0 (RS 33 C))
    DPEmpty DPEmpty) (DPNode (MkDag 6 (bs4 hff h3d hcf h2f) (RS 48 D) R0 R0 (RS 49 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 6 (bs4 hf9 he7 hcf h7f) R0 (RS 25 A) R0 R0) (DPNode (MkDag 0 (bs4 h2f h3c hff h2f) R0 R0 R0 (RS 41 C))
    DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 10 (bs4 h9e h79 he7 h97) R0 (RS 13 A) R0 (RS 13 A)) (DPNode (MkDag 16
    (bs4 hf3 hf3 hcf hef) (RS 20 D) R0 R0 (RS 21 B)) (DPNode (MkDag 9 (bs4 h3f h73 hf9 hfd) R0 R0 R0 (RS 37 C))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h3e he7 hf9 hfd) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty)) (DPNode (MkDag 12
    (bs4 h9f h7d hcf hff) R0 (RS 29 C) R0 R0) (DPNode (MkDag 17 (bs4 hff h3f hb9 he7) R0 (RS 45 A) R0 R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 5 (bs4 h9e h79 he7 h9f) R0 (RS 7 A) R0 (RS 7 A)) (DPNode (MkDag 8 (bs4 h9e
    h79 he7 h97) R0 (RS 11 A) R0 (RS 11 A)) (DPNode (MkDag 15 (bs4 hf9 hf3 hcf h3f) (RS 18 D) R0 R0 (RS 19 A))
    (DPNode (MkDag 9 (bs4 h2f h73 hf9 hfd) R0 R0 R0 (RS 35 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hf3 he7 hb9
    hfd) (RS 50 D) R0 R0 (RS 51 C)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 hf9 hfd hcf hff) R0 R0 (RS 27 E) (RS 28
    A)) (DPNode (MkDag 0 (bs4 h3f h3c hff h2f) R0 R0 R0 (RS 43 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 12
    (bs4 h9e h79 he7 h9f) R0 (RS 2 A) R0 (RS 2 A)) (DPNode (MkDag 3 (bs4 hcf hfe h7f h7f) R0 R0 R0 (RS 23 A))
    (DPNode (MkDag 3 (bs4 h3f hf3 hf3 hff) R0 R0 R0 (RS 39 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs4 hcf
    h2f h9f h2f) R0 R0 R0 (RS 31 C)) (DPNode (MkDag 3 (bs4 h9e h7f hf9 he7) R0 (RS 47 B) R0 R0) DPEmpty DPEmpty)
    DPEmpty)))) (DPNode (MkDag 3 (bs4 h9e h79 he7 h9f) R0 (RS 4 A) R0 (RS 4 A)) (DPNode (MkDag 4 (bs4 h9e h79 he7
    h97) R0 (RS 6 A) R0 (RS 6 A)) (DPNode (MkDag 7 (bs4 h9e h79 he7 h97) R0 (RS 10 A) R0 (RS 10 A)) (DPNode (MkDag
    15 (bs4 hb9 hf3 hcf h3f) R0 (RS 18 C) R0 R0) (DPNode (MkDag 9 (bs4 haf h73 hf9 hfd) R0 R0 (RS 34 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 6 (bs4 h9f h3f hcf h2f) R0 (RS 50 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 hb9
    hfd hcf hff) R0 R0 R0 (RS 26 C)) (DPNode (MkDag 0 (bs4 hbf h3c hff h2f) R0 R0 (RS 42 E) R0) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 11 (bs4 h9e h79 he7 h97) R0 (RS 14 A) R0 (RS 14 A)) (DPNode (MkDag 9 (bs4 h7f hee h79
    hfd) (RS 22 D) R0 R0 R0) (DPNode (MkDag 3 (bs4 hbf hf3 hf3 hff) R0 R0 (RS 38 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 12 (bs4 hf3 hfd hcf hff) (RS 29 D) R0 R0 (RS 30 D)) (DPNode (MkDag 18 (bs4 h9e h7f hf9 hfd) R0
    R0 R0 (RS 46 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 6 (bs4 h9e h79 he7 h97) R0 (RS 8 A) R0 (RS 8 A))
    (DPNode (MkDag 9 (bs4 h9e h79 he7 h9f) R0 (RS 12 A) R0 (RS 12 A)) (DPNode (MkDag 16 (bs4 h9f h73 hcf hef) R0
    (RS 20 C) R0 R0) (DPNode (MkDag 9 (bs4 hbf h73 hf9 hfd) R0 R0 (RS 36 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs4 hbe he7 hf9 hfd) R0 R0 (RS 52 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 h79 hfd hcf hff) R0 R0 R0 (RS
    26 B)) (DPNode (MkDag 17 (bs4 hbf h3f hb9 he7) R0 (RS 44 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 13
    (bs4 h7c hf2 hff hfc) (RS 16 D) R0 R0 R0) (DPNode (MkDag 6 (bs4 hb9 he7 hcf h7f) R0 (RS 24 C) R0 R0) (DPNode
    (MkDag 0 (bs4 haf h3c hff h2f) R0 R0 (RS 40 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs4 hbf hf3 hcf
    hff) R0 R0 (RS 32 E) R0) (DPNode (MkDag 6 (bs4 h7f h3d hcf h2f) R0 R0 R0 (RS 48 B)) DPEmpty DPEmpty)
    DPEmpty))))).

Definition dagTree_49 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 0 A) R0 (RS 0 A)) DPEmpty.

Definition dagTree_50 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 he5 hf7 h2f hbe h5f) (RS 0 D) R0 R0 (RS 5 C)) (DPNode (MkDag 0 (bs5 he7 hf7 h2f hbe h5f)
    (RS 1 D) R0 R0 (RS 13 B)) (DPNode (MkDag 0 (bs5 hcf hff h2f h72 hfb) R0 R0 R0 (RS 11 C)) (DPNode (MkDag 0 (bs5
    hfc hbf h3f h73 hfb) (RS 4 D) R0 (RS 15 E) (RS 0 B)) (DPNode (MkDag 0 (bs5 h2f hff h2f h72 hfb) R0 R0 R0 (RS 9
    C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h3c hbf h3f h73 hfb) R0 R0 R0 (RS 3 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 h3d hff h2f h72 hfb) R0 R0 R0 (RS 7 C)) (DPNode (MkDag 0 (bs5 h3f hff h2f h72 hfb) R0 R0 R0 (RS
    11 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hfd hff h2f h72 hfb) R0 R0 R0 (RS 4 C)) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs5 he7 h9f h3c hf3 hfb) (RS 3 D) R0 R0 (RS 1 B)) (DPNode (MkDag 0 (bs5 hbd hff h2f h72 hfb)
    R0 R0 (RS 6 E) R0) (DPNode (MkDag 0 (bs5 hbf hff h2f h72 hfb) R0 R0 (RS 10 E) R0) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs5 h7d hff h2f h72 hfb) (RS 2 D) R0 R0 (RS 14 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs5 haf hff
    h2f h72 hfb) R0 R0 (RS 8 E) R0) (DPNode (MkDag 0 (bs5 hbc hbf h3f h73 hfb) R0 R0 (RS 12 E) R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 h7c hbf h3f h73 hfb) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty)))).

Definition dagTree_51 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hef h9e h79 he5 he7) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 0 (bs5 hfc hfe h79 he5 he7) R0
    R0 R0 (RS 33 B)) (DPNode (MkDag 1 (bs5 hfc hfe h79 hef hf9) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 2 (bs5 hfc hfe
    h7f h2f hbf) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 0 (bs5 h3c hbe h79 he5 he7) R0 R0 R0 (RS 21 C)) (DPNode (MkDag
    1 (bs5 haf h3e h79 h7f hf9) R0 R0 (RS 17 E) R0) (DPNode (MkDag 0 (bs5 h7c hfe h79 he5 he7) R0 R0 R0 (RS 1 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 hbc hbe h79 he5 hf3) R0 R0 (RS 25 E) R0) (DPNode (MkDag 2 (bs5
    h3e h7e h5f h2f hbf) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 4 (bs5 hfc hfe h79 he5 hf3)
    R0 R0 R0 (RS 36 B)) (DPNode (MkDag 0 (bs5 hbc hbe h79 he5 he7) R0 R0 (RS 8 E) R0) (DPNode (MkDag 1 (bs5 h79 hfe
    h79 hff hf9) R0 R0 R0 (RS 5 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 he7 hee h5f h2f hbf) R0 R0 R0
    (RS 3 B)) (DPNode (MkDag 3 (bs5 h9f h97 hcf h3c hf3) R0 R0 R0 (RS 45 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 3 (bs5 hfc hf3 hcf h3c hf3) R0 R0 R0 (RS 31 B)) (DPNode (MkDag 2 (bs5 he7 h9e h5f h2f hbf) R0 R0 R0 (RS
    30 B)) (DPNode (MkDag 1 (bs5 hbf h3e h79 h7f hf9) R0 R0 (RS 19 E) R0) (DPNode (MkDag 2 (bs5 h7c hfe h7f h2f
    hbf) R0 R0 R0 (RS 4 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 he7 hbe h79 hff hf9) R0 R0 R0 (RS 27
    B)) (DPNode (MkDag 3 (bs5 hbb h97 hcf h3c hf3) R0 (RS 43 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 3
    (bs5 hbe h7e h5f h3c hf3) R0 R0 (RS 15 E) R0) (DPNode (MkDag 3 (bs5 h3c hbe h7f h3c hf3) R0 R0 R0 (RS 23 C))
    (DPNode (MkDag 2 (bs5 hf3 hee h5f h2f hbf) (RS 38 D) R0 R0 (RS 39 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    3 (bs5 h7c hf3 hcf h3c hf3) R0 R0 R0 (RS 6 B)) (DPNode (MkDag 1 (bs5 hbc hbe h79 hef hf9) R0 R0 (RS 47 E) R0)
    DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0 (bs5 he7 h9e h79 he5 he7) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 1
    (bs5 hf9 hfe h79 hff hf9) R0 R0 R0 (RS 37 A)) (DPNode (MkDag 2 (bs5 h3c hbe h7f h2f hbf) R0 R0 R0 (RS 24 C))
    (DPNode (MkDag 1 (bs5 h2f h3e h79 h7f hf9) R0 R0 R0 (RS 18 C)) (DPNode (MkDag 3 (bs5 h7c hfe h7f h3c hf3) R0 R0
    R0 (RS 11 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 h3c hbe h79 he5 hf3) R0 R0 R0 (RS 26 B)) (DPNode
    (MkDag 0 (bs5 h7f h9e h79 he5 he7) (RS 7 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs5 hcf h9e
    h5f h2f hbf) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 3 (bs5 hbc hbe h7f h3c hf3) R0 R0 (RS 22 E) R0) (DPNode (MkDag
    3 (bs5 h9f h3e h5f h3c hf3) R0 (RS 38 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 he7 h97 hcf h3c
    hf3) R0 R0 R0 (RS 10 B)) (DPNode (MkDag 1 (bs5 h7f h9e h79 hff hf9) (RS 13 D) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 2 (bs5 hcf h9e h7f h2f hbf) R0 R0 R0 (RS 42 A)) (DPNode (MkDag 3 (bs5 hfc hfe h7f h3c
    hf3) R0 R0 R0 (RS 34 B)) (DPNode (MkDag 1 (bs5 h3f h3e h79 h7f hf9) R0 R0 R0 (RS 20 C)) (DPNode (MkDag 4 (bs5
    h7c hfe h79 he5 hf3) R0 R0 R0 (RS 12 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 he7 hfe h79 hff hf9)
    R0 R0 R0 (RS 28 B)) (DPNode (MkDag 3 (bs5 hfb h97 hcf h3c hf3) R0 (RS 44 A) R0 R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 3 (bs5 h3e h7e h5f h3c hf3) R0 R0 R0 (RS 16 C)) (DPNode (MkDag 2 (bs5 hbc hbe h7f h2f hbf) R0 R0
    (RS 9 E) R0) (DPNode (MkDag 2 (bs5 hbe h7e h5f h2f hbf) R0 R0 (RS 40 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs5 h7c hfe h79 hef hf9) R0 R0 R0 (RS 2 B)) (DPNode (MkDag 1 (bs5 h3c hbe h79 hef hf9) R0 R0 R0 (RS
    20 C)) DPEmpty DPEmpty) DPEmpty))))).

Definition dagTree_52 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hfc hbe h5f h3e he5) (RS 0 D) R0 R0 (RS 98 B)) (DPNode (MkDag 1 (bs5 hf3 hee h7f h73
    hf9) (RS 1 D) R0 R0 (RS 102 C)) (DPNode (MkDag 2 (bs5 h5f hcb hdc hbf hf9) (RS 99 B) R0 R0 R0) (DPNode (MkDag 4
    (bs5 hfc hfc hfc hbc hf9) (RS 4 D) R0 R0 (RS 44 C)) (DPNode (MkDag 3 (bs5 hfc hf3 hff hf3 hf9) R0 (RS 94 B) R0
    R0) (DPNode (MkDag 9 (bs5 hcf h97 hcb he7 hf7) R0 R0 R0 (RS 17 A)) (DPNode (MkDag 5 (bs5 hfc hff hcb hf3 hf9)
    R0 (RS 33 B) R0 R0) (DPNode (MkDag 4 (bs5 hbc hf2 hfc hbc hf9) R0 (RS 65 C) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 11 (bs5 h9f h97 hdf hf3 hf9) R0 (RS 97 B) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 h7f hee h7f
    h3c hf9) R0 R0 R0 (RS 49 B)) (DPNode (MkDag 9 (bs5 hcf hf3 hcf hf2 hf7) R0 R0 R0 (RS 81 A)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 5 (bs5 h7f h9f hcb hef hf9) (RS 25 D) R0 R0 R0) (DPNode (MkDag 1 (bs5 hdc hfe h7f hcf
    hb9) R0 R0 R0 (RS 41 A)) (DPNode (MkDag 9 (bs5 h7c hfc hf9 hfc hf7) R0 R0 R0 (RS 73 B)) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 hef h9e h7f h3e he5) R0 R0 R0 (RS 89 B)) DPEmpty DPEmpty)) (DPNode (MkDag 11 (bs5 hf9 hee
    h7f h73 hf9) (RS 56 D) R0 R0 (RS 57 A)) (DPNode (MkDag 11 (bs5 h9f hfc hff hf3 hf9) R0 (RS 89 B) R0 R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 3 (bs5 hcf h72 hff hf3 hf9) R0 R0 R0 (RS 11 D)) (DPNode (MkDag 2 (bs5 h7f
    h9e h79 hff hf9) R0 R0 R0 (RS 21 B)) (DPNode (MkDag 3 (bs5 hdc hfe h5f h3f hf9) R0 R0 R0 (RS 37 A)) (DPNode
    (MkDag 12 (bs5 h7c hf3 hfb he5 hf9) (RS 69 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs5 hb9 hf3 hcb hf3
    hf9) R0 (RS 9 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs5 hb9 hfd hcb hef hf9) R0 (RS 5 C) R0 R0) (DPNode
    (MkDag 10 (bs5 hf3 hf3 hf3 hf3 hf9) R0 R0 (RS 85 E) (RS 86 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 4 (bs5
    he7 h97 hdf hf3 hf9) (RS 28 D) R0 R0 (RS 29 B)) (DPNode (MkDag 1 (bs5 hf2 hf7 hcf h3f hb9) R0 R0 (RS 45 E) (RS
    46 B)) (DPNode (MkDag 2 (bs5 h7f h3f h9e h7f hf9) (RS 77 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    3 (bs5 h7c hbe h7f h3d hf9) (RS 6 D) R0 R0 R0) (DPNode (MkDag 2 (bs5 h72 hf9 h7c hbf hf9) R0 R0 R0 (RS 91 B))
    DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 3 (bs5 hdc hbe h7f h3f hf9) R0 R0 R0 (RS 61 A)) (DPNode (MkDag 7
    (bs5 h7f he7 hcb hf2 hff) (RS 3 D) R0 R0 R0) (DPNode (MkDag 3 (bs5 hfb h97 hcb hcf hf9) (RS 18 D) R0 R0 (RS 19
    A)) (DPNode (MkDag 7 (bs5 hfc hfe h79 hfc hff) (RS 34 D) R0 R0 (RS 35 B)) (DPNode (MkDag 3 (bs5 h7c hf3 hfe h7f
    hf9) R0 R0 R0 (RS 67 B)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs5 h7c hbe h5e h7c hff) (RS 2 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 4 (bs5 h79 he7 hcf h3c hf9) R0 R0 R0 (RS 51 B)) (DPNode (MkDag 3 (bs5 hf9 hf3 hf9 hf3
    hf9) R0 (RS 83 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 10 (bs5 hbc hf2 hf9 hf3 hf9) R0 (RS 27 C) R0
    R0) (DPNode (MkDag 1 (bs5 hfc hfe h7f hcf hb9) R0 (RS 43 B) R0 R0) (DPNode (MkDag 6 (bs5 h7f h3c hff h3f hb9)
    (RS 75 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 11 (bs5 hf9 hfe h7f h73 hf9) R0 (RS 59 A) R0 R0)
    (DPNode (MkDag 0 (bs5 hff h9e h7f h3e he5) R0 R0 R0 (RS 91 C)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8
    (bs5 h5f h97 hcb he7 h9f) (RS 15 B) R0 R0 R0) (DPNode (MkDag 5 (bs5 h7b h9f hcb hef hf9) (RS 23 B) R0 R0 R0)
    (DPNode (MkDag 3 (bs5 hfc hfe h5f h3f hf9) (RS 38 D) R0 R0 (RS 39 B)) (DPNode (MkDag 13 (bs5 hbc hfe hf9 he7
    hff) R0 (RS 71 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 hbe h7e h7f h73 hf9) R0 R0 (RS 103 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 hf3 hf3 hf9 hf3 hf9) R0 (RS 55 B) R0 R0) (DPNode (MkDag 11 (bs5 h7b
    hfc hff hf3 hf9) R0 R0 R0 (RS 87 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs5 hdc hff hcb hf3 hf9) R0
    R0 R0 (RS 31 A)) (DPNode (MkDag 11 (bs5 h7f he7 hcf hef hf9) R0 R0 R0 (RS 47 B)) (DPNode (MkDag 12 (bs5 h7e h7e
    h5f h3f hb9) (RS 79 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 hfc hbe h7f h3f hf9) (RS 62 D)
    R0 R0 (RS 63 B)) (DPNode (MkDag 11 (bs5 h7b h97 hdf hf3 hf9) R0 R0 R0 (RS 95 B)) DPEmpty DPEmpty) DPEmpty)))))
    (DPNode (MkDag 3 (bs5 hdc hf3 hff hf3 hf9) R0 R0 R0 (RS 93 A)) (DPNode (MkDag 5 (bs5 hf9 hfd hcb hef hf9) (RS 5
    D) R0 R0 (RS 53 A)) (DPNode (MkDag 6 (bs5 hf9 hf3 hcb hf3 hf9) (RS 9 D) R0 R0 (RS 101 A)) (DPNode (MkDag 3 (bs5
    hbb h97 hcb hcf hf9) R0 (RS 18 C) R0 R0) (DPNode (MkDag 7 (bs5 h7c hfe h79 hfc hff) R0 R0 R0 (RS 34 B)) (DPNode
    (MkDag 4 (bs5 hfc hf2 hfc hbc hf9) R0 (RS 66 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h7c hbe h5f h3e
    he5) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 hff hee h7f h3c hf9) R0 R0 R0 (RS 50 B))
    (DPNode (MkDag 3 (bs5 hb9 hf3 hf9 hf3 hf9) R0 (RS 82 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 10
    (bs5 hdc hf2 hf9 hf3 hf9) R0 R0 R0 (RS 26 A)) (DPNode (MkDag 1 (bs5 hbc hfe h7f hcf hb9) R0 (RS 42 C) R0 R0)
    (DPNode (MkDag 9 (bs5 hfc hfc hf9 hfc hf7) (RS 73 D) R0 R0 (RS 74 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    11 (bs5 hb9 hfe h7f h73 hf9) R0 (RS 58 C) R0 R0) (DPNode (MkDag 0 (bs5 h7f h9e h7f h3e he5) (RS 10 B) R0 R0 (RS
    90 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 8 (bs5 h7b h97 hcb he7 h9f) (RS 14 B) R0 R0 R0) (DPNode
    (MkDag 2 (bs5 hff h9e h79 hff hf9) (RS 21 D) R0 R0 (RS 22 B)) (DPNode (MkDag 3 (bs5 hbc hfe h5f h3f hf9) R0 (RS
    38 C) R0 R0) (DPNode (MkDag 13 (bs5 hdc hfe hf9 he7 hff) R0 R0 R0 (RS 70 A)) DPEmpty DPEmpty) (DPNode (MkDag 2
    (bs5 h9f h3e h79 hf3 hf9) R0 (RS 1 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs5 h9f h73 hf9 hf3 hf9) R0
    (RS 54 C) R0 R0) (DPNode (MkDag 10 (bs5 h73 hf3 hf3 hf3 hf9) R0 R0 R0 (RS 84 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 5 (bs5 h7c hf7 hcb hf3 hf9) (RS 30 D) R0 R0 R0) (DPNode (MkDag 1 (bs5 h72 hf7 hcf h3f hb9) R0 R0
    R0 (RS 44 B)) (DPNode (MkDag 12 (bs5 h5e h7e h5f h3f hb9) (RS 78 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 3 (bs5 hbc hbe h7f h3f hf9) R0 (RS 62 C) R0 R0) (DPNode (MkDag 3 (bs5 hbc hf3 hff hf3 hf9) R0 (RS 8 C)
    R0 R0) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 4 (bs5 hdc hf2 hfc hbc hf9) R0 R0 R0 (RS 64 A)) (DPNode
    (MkDag 3 (bs5 hcf hf2 hff hf3 hf9) R0 R0 R0 (RS 100 A)) (DPNode (MkDag 3 (bs5 h9f h97 hcb hcf hf9) R0 (RS 20 B)
    R0 R0) (DPNode (MkDag 3 (bs5 h7c hfe h5f h3d hf9) (RS 36 D) R0 R0 R0) (DPNode (MkDag 3 (bs5 hfc hf3 hfe h7f
    hf9) (RS 67 D) R0 R0 (RS 68 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h7f hcb hdc hbf hf9) (RS 12 D) R0 R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs5 hf9 he7 hcf h3c hf9) R0 R0 R0 (RS 52 A)) (DPNode (MkDag 10 (bs5 h9f h73
    hf3 hf3 hf9) R0 R0 R0 (RS 84 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 10 (bs5 hfc hf2 hf9 hf3 hf9) (RS 27
    D) R0 R0 (RS 28 B)) (DPNode (MkDag 4 (bs5 h7c hfc hfc hbc hf9) R0 R0 R0 (RS 4 B)) (DPNode (MkDag 2 (bs5 h5f h3f
    h9e h7f hf9) (RS 76 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs5 h9f h3c hff hf3 hf9) R0 R0 R0
    (RS 60 B)) (DPNode (MkDag 2 (bs5 hf2 hf9 h7c hbf hf9) (RS 91 D) R0 (RS 92 E) (RS 10 B)) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 8 (bs5 h7f h97 hcb he7 h9f) (RS 16 D) R0 R0 R0) (DPNode (MkDag 5 (bs5 h5f h9f hcb hef
    hf9) (RS 24 B) R0 R0 R0) (DPNode (MkDag 6 (bs5 h7c hfe h5e he7 hf9) (RS 40 D) R0 R0 R0) (DPNode (MkDag 13 (bs5
    hfc hfe hf9 he7 hff) R0 (RS 72 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs5 h3e h7e h7f h73 hf9) R0 R0 R0
    (RS 104 B)) DPEmpty DPEmpty)) (DPNode (MkDag 11 (bs5 h79 hee h7f h73 hf9) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 11
    (bs5 hfb hfc hff hf3 hf9) R0 R0 R0 (RS 88 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 5 (bs5 hbc hff hcb hf3
    hf9) R0 (RS 32 C) R0 R0) (DPNode (MkDag 11 (bs5 hff he7 hcf hef hf9) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 9 (bs5
    hcf h73 hcf hf2 hf7) R0 R0 R0 (RS 80 D)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 6 (bs5 h7c hbe h7e he7 hf9)
    (RS 7 D) R0 R0 R0) (DPNode (MkDag 11 (bs5 hfb h97 hdf hf3 hf9) (RS 95 D) R0 R0 (RS 96 A)) DPEmpty DPEmpty)
    DPEmpty)))))).

Definition dagSub_53_128 : DagPTree :=
  DPNode (MkDag 3 (bs5 hf7 h2f hcf h3f he7) (RS 8 D) (RS 130 C) R0 (RS 130 C)) (DPNode (MkDag 6 (bs5 hbf h3f h9f
    he5 hf3) R0 (RS 17 C) R0 R0) (DPNode (MkDag 3 (bs5 hb9 hfc hfe h7f he7) R0 (RS 33 C) R0 R0) (DPNode (MkDag 0
    (bs5 h7c hf3 hf9 he7 h9e) (RS 65 D) R0 R0 R0) (DPNode (MkDag 11 (bs5 hfb he5 hff h3c hf3) (RS 128 D) R0 R0 (RS
    129 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5 hfb h9f hcf h3c hf3) (RS 96 D) R0 R0 (RS 97 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs5 hf7 h2f h9e hf9 h7c) R0 (RS 49 C) R0 R0) (DPNode (MkDag 0 (bs5 hb9 hff
    hf7 h2f hfe) R0 R0 R0 (RS 81 C)) (DPNode (MkDag 0 (bs5 haf h97 hcb hee h5e) R0 R0 (RS 0 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 12 (bs5 hcf h9f hcf h3c hf3) R0 R0 R0 (RS 113 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0
    (bs5 hbc hf7 h2f hff h97) R0 R0 (RS 25 E) R0) (DPNode (MkDag 10 (bs5 h9f h3d hff h3f hfe) R0 R0 R0 (RS 41 C))
    (DPNode (MkDag 2 (bs5 h9e h7e h7f he7 h9e) R0 (RS 73 B) R0 R0) (DPNode (MkDag 0 (bs5 haf h9e h7f h2f hfe) R0 R0
    (RS 137 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 hbe h7c hfb hfe h7e) R0 R0 (RS 105 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hb9 hfd hfe h7c hfe) R0 (RS 57 C) R0 R0) (DPNode (MkDag 2 (bs5 h97 hcf
    h9f hfe h7e) R0 (RS 89 A) R0 (RS 89 A)) (DPNode (MkDag 1 (bs5 hf2 hfc hbe he7 hf2) (RS 152 D) R0 R0 (RS 153 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 hbf h3d hcf h3f he7) R0 R0 (RS 121 E) R0) DPEmpty DPEmpty))).

Definition dagSub_53_129 : DagPTree :=
  DPNode (MkDag 6 (bs5 hf7 h3f h9e he5 hf3) R0 R0 (RS 13 E) (RS 14 C)) (DPNode (MkDag 0 (bs5 hfc hf2 hfb hfe h5e)
    (RS 20 D) R0 R0 (RS 21 B)) (DPNode (MkDag 8 (bs5 h79 hf3 hcf hfc hfc) R0 R0 R0 (RS 37 B)) (DPNode (MkDag 9 (bs5
    h9f hff he7 he7 hf2) R0 R0 R0 (RS 69 A)) (DPNode (MkDag 3 (bs5 h3f h2f hcf h3f he7) R0 R0 R0 (RS 133 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h9e h7c hbe he7 hf2) R0 (RS 101 B) R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs5 hf7 h2f h3f h2f h9e) R0 R0 (RS 53 E) (RS 54 C)) (DPNode (MkDag 3 (bs5 hf7 h3f hcf h3f
    he7) R0 (RS 85 C) R0 R0) (DPNode (MkDag 2 (bs5 h2f h9e h5f hfe h7e) R0 R0 R0 (RS 149 C)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs5 hbe h7c hbe he7 hf2) R0 R0 (RS 117 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 9
    (bs5 haf hb9 h7e h5f h72) R0 R0 (RS 29 E) R0) (DPNode (MkDag 10 (bs5 h3f h3f hff h3f hfe) R0 R0 R0 (RS 45 A))
    (DPNode (MkDag 2 (bs5 h79 h7e h7f hfe h7e) R0 R0 R0 (RS 4 B)) (DPNode (MkDag 12 (bs5 haf h97 hcf h3c hf3) R0 R0
    (RS 141 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hcf h9f h9f hcb hf3) R0 R0 R0 (RS 109 A))
    DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 hf3 hf9 h7c hfc hf2) R0 (RS 61 C) R0 R0) (DPNode (MkDag 1 (bs5 h7f h9e
    h7f he7 hf2) (RS 93 D) R0 R0 (RS 94 B)) (DPNode (MkDag 2 (bs5 h79 h7c hfb hfe h7e) R0 R0 R0 (RS 2 B)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5 h7f h9f hcf h3c hf3) (RS 125 D) R0 R0 R0) DPEmpty DPEmpty))).

Definition dagSub_53_130 : DagPTree :=
  DPNode (MkDag 4 (bs5 hf9 he5 hfe he5 hf7) R0 (RS 11 A) R0 R0) (DPNode (MkDag 7 (bs5 h9f h3f h3e he5 he7) R0 (RS
    19 B) R0 R0) (DPNode (MkDag 2 (bs5 h9f h73 hcf h2f h9e) R0 (RS 35 C) R0 R0) (DPNode (MkDag 2 (bs5 hbc hf2 hfb
    he7 h9e) R0 (RS 67 C) R0 R0) (DPNode (MkDag 3 (bs5 hbf h2f hcf h3f he7) R0 (RS 131 C) (RS 132 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h7f h9f hcb hee h5e) R0 R0 R0 (RS 99 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 8 (bs5 hff h2f h9e hf9 h7c) R0 (RS 51 A) R0 R0) (DPNode (MkDag 0 (bs5 h79 hff hf7 h2f hfe) R0 R0 R0 (RS
    81 B)) (DPNode (MkDag 0 (bs5 h3f h97 hcb hee h5e) R0 R0 R0 (RS 147 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    0 (bs5 hfb h9f hcb hee h5e) (RS 114 D) R0 R0 (RS 115 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs5 hbc hff h2f
    hff h97) R0 R0 (RS 27 E) R0) (DPNode (MkDag 10 (bs5 h77 h3f hff h3f hfe) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 0
    (bs5 hff h3e h5f h2f hfe) (RS 74 D) R0 R0 (RS 75 A)) (DPNode (MkDag 0 (bs5 hbf h9e h7f h2f hfe) R0 R0 (RS 139
    E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 he7 hcf h9f hfe h7e) R0 R0 R0 (RS 107 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs5 h9f h7f hfe h7b h9f) R0 (RS 59 C) R0 R0) (DPNode (MkDag 1 (bs5 h97 h9f h9f hcb
    hf3) R0 (RS 91 A) R0 (RS 91 A)) (DPNode (MkDag 11 (bs5 h97 he5 hff h3c hf3) R0 R0 R0 (RS 129 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5 h7b h9f hcf h3c hf3) (RS 123 B) R0 R0 R0) DPEmpty DPEmpty))).

Definition dagSub_53_131 : DagPTree :=
  DPNode (MkDag 6 (bs5 hbf h3f h9e he5 hf3) R0 R0 (RS 15 E) R0) (DPNode (MkDag 2 (bs5 h67 h9f hf9 h7c hfe) R0 R0 R0
    (RS 23 B)) (DPNode (MkDag 8 (bs5 hb9 hfb h97 hf9 h7c) R0 (RS 39 C) R0 R0) (DPNode (MkDag 2 (bs5 h7f h3e h7b he7
    h9e) R0 R0 R0 (RS 71 B)) (DPNode (MkDag 9 (bs5 hbf h9e h5e he7 hf2) R0 R0 (RS 135 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 3 (bs5 hff h3d hcf h3f he7) (RS 102 D) R0 R0 (RS 103 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs5 hbf h2f h3f h2f h9e) R0 R0 (RS 55 E) R0) (DPNode (MkDag 3 (bs5 hff h3f hcf h3f he7) (RS 86 D) (RS
    87 A) R0 (RS 87 A)) (DPNode (MkDag 2 (bs5 h3f h9e h5f hfe h7e) R0 R0 R0 (RS 151 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 3 (bs5 haf h3d hcf h3f he7) R0 R0 (RS 119 E) R0) DPEmpty DPEmpty))) (DPNode (MkDag 9 (bs5 hbf
    hb9 h7e h5f h72) R0 R0 (RS 31 E) R0) (DPNode (MkDag 9 (bs5 hff h3f h97 hdc hf3) (RS 46 D) R0 R0 (RS 47 A))
    (DPNode (MkDag 0 (bs5 hb9 hef hf7 h2f hfe) R0 (RS 79 C) R0 R0) (DPNode (MkDag 12 (bs5 hbf h97 hcf h3c hf3) R0
    R0 (RS 143 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hfb h9e h7f he7 hf2) R0 (RS 6 A) R0 R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 9 (bs5 h7c hf3 hcf he7 hf2) R0 R0 R0 (RS 63 B)) (DPNode (MkDag 1 (bs5 hff h9e
    h7f he7 hf2) (RS 94 D) R0 R0 (RS 122 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hcf hff he7 he7 h9e) R0 R0 R0
    (RS 127 A)) DPEmpty DPEmpty))).

Definition dagSub_53_132 : DagPTree :=
  DPNode (MkDag 4 (bs5 hb9 he5 hfe he5 hf7) R0 (RS 10 C) R0 R0) (DPNode (MkDag 6 (bs5 hff h3f h9f he5 hf3) (RS 17
    D) R0 R0 (RS 18 A)) (DPNode (MkDag 3 (bs5 hf9 hfc hfe h7f he7) (RS 33 D) R0 R0 (RS 34 A)) (DPNode (MkDag 2 (bs5
    hdc hf2 hfb he7 h9e) R0 R0 R0 (RS 66 A)) (DPNode (MkDag 11 (bs5 h9f he5 hff h3c hf3) R0 (RS 8 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 12 (bs5 h9f h9f hcf h3c hf3) R0 (RS 98 B) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 8 (bs5 hbf h2f h9e hf9 h7c) R0 (RS 50 C) R0 R0) (DPNode (MkDag 0 (bs5 hf9 hff hf7 h2f hfe) R0 R0 (RS 82
    E) (RS 83 A)) (DPNode (MkDag 0 (bs5 hbf h97 hcb hee h5e) R0 R0 (RS 146 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs5 hbb h9f hcb hee h5e) R0 (RS 114 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs5 h3c hf7 h2f
    hff h97) R0 R0 R0 (RS 26 C)) (DPNode (MkDag 10 (bs5 hf7 h3f hff h3f hfe) R0 R0 (RS 42 E) (RS 43 C)) (DPNode
    (MkDag 0 (bs5 h7f h3e h5f h2f hfe) R0 R0 R0 (RS 74 B)) (DPNode (MkDag 0 (bs5 h2f h9e h7f h2f hfe) R0 R0 R0 (RS
    138 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs5 h3e h7c hfb hfe h7e) R0 R0 R0 (RS 106 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 2 (bs5 hf9 hfd hfe h7c hfe) (RS 57 D) R0 R0 (RS 58 A)) (DPNode (MkDag 2 (bs5 h9f hcf
    h9f hfe h7e) R0 (RS 90 A) R0 (RS 90 A)) (DPNode (MkDag 11 (bs5 h9e he5 hff h3c hf3) R0 (RS 154 A) R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h3f h3d hcf h3f he7) R0 R0 R0 (RS 85 A)) DPEmpty DPEmpty))).

Definition dagSub_53_133 : DagPTree :=
  DPNode (MkDag 6 (bs5 h77 h3f h9e he5 hf3) R0 R0 R0 (RS 12 B)) (DPNode (MkDag 8 (bs5 h7c hf3 hff h3f hfc) (RS 22
    E) R0 R0 R0) (DPNode (MkDag 8 (bs5 hf9 hf3 hcf hfc hfc) (RS 37 D) R0 R0 (RS 38 A)) (DPNode (MkDag 3 (bs5 h9e
    h7e h5f h3f he7) R0 (RS 70 B) R0 R0) (DPNode (MkDag 1 (bs5 hb9 h7b h9f hcb hf3) R0 (RS 1 C) R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h7f h3d hcf h3f he7) R0 R0 R0 (RS 102 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs5 h77 h2f h3f h2f h9e) R0 R0 R0 (RS 52 B)) (DPNode (MkDag 3 (bs5 hbf h3f hcf h3f he7) R0 (RS 86 C)
    R0 R0) (DPNode (MkDag 2 (bs5 hbf h9e h5f hfe h7e) R0 R0 (RS 150 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    1 (bs5 h3e h7c hbe he7 hf2) R0 R0 R0 (RS 118 C)) DPEmpty DPEmpty))) (DPNode (MkDag 9 (bs5 h2f hb9 h7e h5f h72)
    R0 R0 R0 (RS 30 C)) (DPNode (MkDag 9 (bs5 hbf h3f h97 hdc hf3) R0 (RS 46 C) R0 R0) (DPNode (MkDag 12 (bs5 hcf
    h2f hf3 he7 hf3) R0 R0 R0 (RS 78 A)) (DPNode (MkDag 12 (bs5 h2f h97 hcf h3c hf3) R0 R0 R0 (RS 142 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hbb h9e h7f he7 hf2) R0 (RS 110 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hf3 hf9 h7b hff h97) R0 (RS 3 C) R0 R0) (DPNode (MkDag 11 (bs5 hcf h9e h7f h3c hf3) R0 R0 R0 (RS
    95 A)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 hcf h9f hcb hee h5e) R0 R0 R0 (RS 126 D)) DPEmpty DPEmpty))).

Definition dagSub_53_134 : DagPTree :=
  DPNode (MkDag 5 (bs5 h9f h3c hff h3c hbf) R0 R0 R0 (RS 12 C)) (DPNode (MkDag 0 (bs5 h7c hf2 hfb hfe h5e) R0 R0 R0
    (RS 20 B)) (DPNode (MkDag 2 (bs5 hf3 hf3 hcf h2f h9e) R0 (RS 36 B) R0 R0) (DPNode (MkDag 2 (bs5 hfc hf2 hfb he7
    h9e) R0 (RS 68 A) R0 R0) (DPNode (MkDag 3 (bs5 hff h2f hcf h3f he7) R0 (RS 155 A) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs5 hff h9f hcb hee h5e) (RS 99 D) R0 R0 (RS 100 A)) DPEmpty DPEmpty)) (DPNode
    (MkDag 8 (bs5 h9f h2f h9f hf9 h7c) R0 R0 R0 (RS 52 C)) (DPNode (MkDag 3 (bs5 h9f h3d hcf h3f he7) R0 (RS 84 C)
    R0 R0) (DPNode (MkDag 2 (bs5 haf h9e h5f hfe h7e) R0 R0 (RS 148 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    0 (bs5 h9f h9f hcb hee h5e) R0 (RS 7 C) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs5 h3c hff h2f hff h97) R0
    R0 R0 (RS 28 C)) (DPNode (MkDag 10 (bs5 hbf h3f hff h3f hfe) R0 R0 (RS 44 E) R0) (DPNode (MkDag 11 (bs5 h9e h7e
    h5f h3c hf3) R0 (RS 76 B) R0 R0) (DPNode (MkDag 0 (bs5 h3f h9e h7f h2f hfe) R0 R0 R0 (RS 140 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h7c hfb h9f hcb hf3) (RS 108 D) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs5 hf3 hff hfe h7b h9f) R0 (RS 60 C) R0 R0) (DPNode (MkDag 1 (bs5 h9f h9f h9f hcb hf3) R0 (RS 92 B)
    R0 (RS 92 B)) (DPNode (MkDag 2 (bs5 hb9 h7c hfb hfe h7e) R0 R0 R0 (RS 2 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 12 (bs5 h5f h9f hcf h3c hf3) (RS 124 B) R0 R0 R0) DPEmpty DPEmpty))).

Definition dagSub_53_135 : DagPTree :=
  DPNode (MkDag 6 (bs5 h3f h3f h9e he5 hf3) R0 R0 R0 (RS 16 A)) (DPNode (MkDag 2 (bs5 he7 h9f hf9 h7c hfe) R0 R0 R0
    (RS 24 C)) (DPNode (MkDag 8 (bs5 hf9 hfb h97 hf9 h7c) R0 (RS 40 A) R0 R0) (DPNode (MkDag 2 (bs5 hff h3e h7b he7
    h9e) (RS 71 D) R0 R0 (RS 72 A)) (DPNode (MkDag 9 (bs5 h3f h9e h5e he7 hf2) R0 R0 R0 (RS 136 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 3 (bs5 h9f h3f hcf h3f he7) R0 (RS 5 C) R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 2 (bs5 h3f h2f h3f h2f h9e) R0 R0 R0 (RS 56 A)) (DPNode (MkDag 2 (bs5 h9e h7c hfb hfe h7e) R0 (RS 88 A)
    R0 (RS 88 A)) (DPNode (MkDag 1 (bs5 hb2 hfc hbe he7 hf2) R0 (RS 152 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 3 (bs5 h2f h3d hcf h3f he7) R0 R0 R0 (RS 120 C)) DPEmpty DPEmpty))) (DPNode (MkDag 9 (bs5 h3f hb9 h7e
    h5f h72) R0 R0 R0 (RS 32 A)) (DPNode (MkDag 0 (bs5 h9f h3c hbe h5f h9f) R0 (RS 48 C) R0 R0) (DPNode (MkDag 0
    (bs5 hf9 hef hf7 h2f hfe) R0 (RS 80 A) R0 R0) (DPNode (MkDag 12 (bs5 h3f h97 hcf h3c hf3) R0 R0 R0 (RS 144 C))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 11 (bs5 h7f h9e h7f h3c hf3) (RS 112 D) R0 R0 R0) DPEmpty DPEmpty))
    (DPNode (MkDag 9 (bs5 hfc hf3 hcf he7 hf2) (RS 63 D) R0 R0 (RS 64 B)) (DPNode (MkDag 12 (bs5 hbb h9f hcf h3c
    hf3) R0 (RS 96 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs5 hbb he5 hff h3c hf3) R0 (RS 128 C) R0 R0)
    DPEmpty DPEmpty))).

Definition dagTree_53 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 h2f h97 hcb hee h5e) R0 R0 R0 (RS 145 C)) (DPNode (MkDag 1 (bs5 hf9 h7b h9f hcb hf3) (RS
    1 D) R0 R0 (RS 134 C)) (DPNode (MkDag 2 (bs5 hf9 h7c hfb hfe h7e) R0 R0 (RS 156 E) (RS 133 A)) (DPNode (MkDag 2
    (bs5 hf9 h7e h7f hfe h7e) (RS 4 D) R0 R0 (RS 77 D)) dagSub_53_128 dagSub_53_129) (DPNode (MkDag 1 (bs5 h9f h9e
    h7f he7 hf2) R0 R0 R0 (RS 111 B)) dagSub_53_130 dagSub_53_131)) (DPNode (MkDag 1 (bs5 hff hf3 hcb hdc hf3) R0
    (RS 62 B) R0 R0) (DPNode (MkDag 0 (bs5 hf3 he7 hcf hee h5e) (RS 5 D) R0 R0 (RS 104 C)) dagSub_53_132
    dagSub_53_133) (DPNode (MkDag 2 (bs5 hf3 hff he7 he7 h9e) (RS 7 D) R0 R0 (RS 116 C)) dagSub_53_134
    dagSub_53_135))).

Definition dagTree_54 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf2 hf9 hf9 hee h7f) R0 (RS 4 A) (RS 18 E) (RS 4 A)) (DPNode (MkDag 1 (bs5 hf2 hf9 hfe
    h5e h7f) R0 (RS 0 C) (RS 17 E) (RS 0 C)) (DPNode (MkDag 2 (bs5 h97 he7 h97 hb9 h79) R0 (RS 3 A) R0 (RS 3 A))
    (DPNode (MkDag 2 (bs5 h9e he7 h97 hb9 h79) R0 (RS 2 A) R0 (RS 2 A)) (DPNode (MkDag 5 (bs5 hf3 hcf h9e h7c hf3)
    R0 (RS 9 C) R0 R0) (DPNode (MkDag 0 (bs5 h7c hf2 hf9 h7e h7f) R0 R0 R0 (RS 15 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 8 (bs5 hbf hff h97 hdc hf3) R0 R0 R0 (RS 13 C)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs5 h97 hff
    h3f h97 hcb) R0 R0 R0 (RS 7 A)) (DPNode (MkDag 7 (bs5 hbe hff h3f hcb hf2) R0 (RS 11 C) R0 R0) (DPNode (MkDag 0
    (bs5 h72 hf9 hf9 hee h7f) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 8 (bs5 h7f hff h97 hdc
    hf3) R0 R0 R0 (RS 13 B)) DPEmpty DPEmpty))) (DPNode (MkDag 2 (bs5 h9f he7 h97 hb9 h79) R0 (RS 1 C) R0 (RS 1 C))
    (DPNode (MkDag 3 (bs5 h9f h2f h3c hf7 h3c) R0 (RS 6 A) R0 R0) (DPNode (MkDag 6 (bs5 hf3 hfb h9f hdf hff) R0 (RS
    10 C) R0 R0) (DPNode (MkDag 1 (bs5 h72 hf9 hfe h5e h7f) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 8 (bs5 hff hff h97 hdc hf3) R0 R0 (RS 14 E) (RS 15 C)) DPEmpty DPEmpty)) (DPNode (MkDag 4 (bs5 h9f hff
    h3f h97 hcb) R0 (RS 8 C) R0 R0) (DPNode (MkDag 7 (bs5 hfe hff h3f hcb hf2) R0 (RS 12 A) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 0 (bs5 hfc hf2 hf9 h7e h7f) (RS 15 D) R0 (RS 16 E) (RS 1 C)) DPEmpty DPEmpty)))).

Definition dagTree_55 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf9 hf9 h7e h5e he7) (RS 0 D) (RS 1 A) (RS 14 E) (RS 1 A)) (DPNode (MkDag 0 (bs5 hb9 hf9
    h7e h5e he7) R0 (RS 0 C) R0 (RS 0 C)) (DPNode (MkDag 1 (bs5 hfc hf3 hf9 hf9 he5) R0 R0 (RS 3 E) (RS 4 C))
    (DPNode (MkDag 1 (bs5 hf2 hf9 hff hcb he5) (RS 4 D) R0 (RS 5 E) (RS 6 C)) (DPNode (MkDag 3 (bs5 hf3 hfe h7e h5f
    he7) (RS 8 D) R0 (RS 9 E) (RS 10 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 hff hcb hff h9e he7) R0 R0 (RS 13
    E) (RS 1 A)) DPEmpty DPEmpty)) (DPNode (MkDag 2 (bs5 hf2 hf7 h3f hcb he7) R0 R0 (RS 7 E) (RS 8 C)) (DPNode
    (MkDag 4 (bs5 h7f hff hcf he5 he7) (RS 11 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs5 h79 hf9 h7e h5e
    he7) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs5 h7c hf3 hf9 hf9 he5) R0 R0 R0 (RS 2 B))
    (DPNode (MkDag 1 (bs5 h72 hf9 hff hcb he5) R0 R0 R0 (RS 4 B)) (DPNode (MkDag 3 (bs5 h73 hfe h7e h5f he7) R0 R0
    R0 (RS 8 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs5 h7f hcb hff h9e he7) R0 R0 R0 (RS 12 B)) DPEmpty DPEmpty))
    (DPNode (MkDag 2 (bs5 h72 hf7 h3f hcb he7) R0 R0 R0 (RS 6 B)) (DPNode (MkDag 0 (bs5 hcb hf9 h7e h5e he7) R0 R0
    R0 (RS 12 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_56 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 hf3 hcf h3e h5e h7f) (RS 0 D) R0 R0 (RS 1 D)) (DPNode (MkDag 0 (bs5 hcf h3c hbe h79 he5)
    R0 R0 R0 (RS 2 D)) (DPNode (MkDag 0 (bs5 hcf h3c hbd hcb hef) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 1 (bs5 hcf h3c
    hbe h7f h2f) R0 R0 R0 (RS 5 D)) (DPNode (MkDag 1 (bs5 hcf h3c hbe h7f h3f) R0 R0 R0 (RS 9 D)) (DPNode (MkDag 1
    (bs5 h9f hff h2f hcf h3f) R0 (RS 17 A) R0 R0) (DPNode (MkDag 0 (bs5 haf hf3 hf3 hcb hef) R0 R0 (RS 33 E) R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h2f hcb hff h9f he5) R0 R0 R0 (RS 25 C)) (DPNode (MkDag 0 (bs5
    hbd hcf hee h7e h7f) R0 R0 (RS 41 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs5 hcf h3c hfe h5f h2f)
    R0 R0 R0 (RS 13 D)) (DPNode (MkDag 0 (bs5 hff h3f h97 h9f h3c) (RS 20 D) R0 R0 (RS 21 C)) (DPNode (MkDag 1 (bs5
    hee h5f hfe h7f h2f) (RS 36 D) R0 R0 (RS 37 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 h7e h79 he7 hf7
    h2f) R0 R0 R0 (RS 29 B)) (DPNode (MkDag 0 (bs5 hbf hcf hee h7e h7f) R0 R0 (RS 45 E) R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 0 (bs5 hcf h3c hfe h5f h3c) R0 R0 R0 (RS 7 D)) (DPNode (MkDag 0 (bs5 hcf h3c hbe h7b
    he5) R0 R0 R0 (RS 11 D)) (DPNode (MkDag 1 (bs5 h9f hb9 h79 hf7 h2f) R0 (RS 19 B) R0 R0) (DPNode (MkDag 0 (bs5
    hbf hf3 hf3 hcb hef) R0 R0 (RS 35 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 h3f hcb hff h9f he5)
    R0 R0 R0 (RS 27 B)) (DPNode (MkDag 0 (bs5 haf hcf hee h7e h7f) R0 R0 (RS 43 E) R0) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs5 h9f h2f he5 hf9 hff) R0 (RS 15 A) R0 R0) (DPNode (MkDag 0 (bs5 h3d hcb hff h9f he5) R0 R0
    R0 (RS 23 C)) (DPNode (MkDag 0 (bs5 hfe h79 h7e h7f h3c) R0 R0 (RS 39 E) (RS 40 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 1 (bs5 hbe h5f h7c hbf h3f) R0 R0 (RS 31 E) R0) (DPNode (MkDag 0 (bs5 he7 h9f hfd hcb hef) R0 R0
    R0 (RS 47 A)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 1 (bs5 hcf h3c hfe h5f h3f) R0 R0 R0 (RS 4 D))
    (DPNode (MkDag 0 (bs5 hcf h3c hbe h7e h7f) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 0 (bs5 hcf h3c hfe h79 h7f) R0 R0
    R0 (RS 10 D)) (DPNode (MkDag 1 (bs5 h97 hb9 h79 hf7 h2f) R0 R0 R0 (RS 18 A)) (DPNode (MkDag 0 (bs5 h2f hf3 hf3
    hcb hef) R0 R0 R0 (RS 34 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs5 hbf hcb hff h9f he5) R0 R0 (RS 26
    E) R0) (DPNode (MkDag 0 (bs5 h3d hcf hee h7e h7f) R0 R0 R0 (RS 42 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    0 (bs5 hcf h3c hfe h5e h7f) R0 R0 R0 (RS 1 D)) (DPNode (MkDag 0 (bs5 hbd hcb hff h9f he5) R0 R0 (RS 22 E) R0)
    (DPNode (MkDag 1 (bs5 h7e h5f hfe h7f h2f) (RS 38 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5
    hfe h79 he7 hf7 h2f) R0 R0 R0 (RS 30 C)) (DPNode (MkDag 0 (bs5 h3f hcf hee h7e h7f) R0 R0 R0 (RS 46 B)) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs5 hcf h3c hbe h7f he5) R0 R0 R0 (RS 8 D)) (DPNode (MkDag 0 (bs5 hcf h3c
    hbe h7f h3c) R0 R0 R0 (RS 12 D)) (DPNode (MkDag 0 (bs5 h7f h3f h97 h9f h3c) R0 R0 R0 (RS 20 B)) (DPNode (MkDag
    0 (bs5 h3f hf3 hf3 hcb hef) R0 R0 R0 (RS 36 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs5 hee h79 he7 hf7
    h2f) R0 R0 R0 (RS 28 B)) (DPNode (MkDag 0 (bs5 h2f hcf hee h7e h7f) R0 R0 R0 (RS 44 C)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 1 (bs5 h97 hff h2f hcf h3f) R0 R0 R0 (RS 16 A)) (DPNode (MkDag 0 (bs5 haf hcb hff h9f
    he5) R0 R0 (RS 24 E) R0) (DPNode (MkDag 0 (bs5 h7e h79 h7e h7f h3c) R0 R0 R0 (RS 38 B)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs5 h3e h5f h7c hbf h3f) R0 R0 R0 (RS 32 C)) (DPNode (MkDag 0 (bs5 h9e h5e h7e h5f
    h3c) R0 (RS 0 C) R0 R0) DPEmpty DPEmpty) DPEmpty))))).

Definition dagTree_57 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 R0 R0 (RS 0 D)) DPEmpty.

Definition dagTree_58 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 h65 hf3 hdf h2f) R0 R0 R0 (RS 1 B)) (DPNode (MkDag 0 (bs4 he5 hf3 hdf h2f) R0 R0 R0 (RS
    2 B)) (DPNode (MkDag 0 (bs4 he5 hf3 hff h2f) R0 R0 R0 (RS 3 B)) (DPNode (MkDag 0 (bs4 he5 hf3 hcf h2f) R0 R0 R0
    (RS 5 B)) (DPNode (MkDag 0 (bs4 he5 hee h5f h7f) R0 R0 R0 (RS 9 B)) (DPNode (MkDag 0 (bs4 h9f h2f hfe h7d) R0
    R0 R0 (RS 17 A)) (DPNode (MkDag 0 (bs4 hf3 hf3 hcf h2f) (RS 32 D) R0 R0 (RS 33 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs4 hbf hf2 hf9 he7) R0 (RS 21 C) R0 R0) (DPNode (MkDag 0 (bs4 h9f h72 hf9 he7) R0 (RS 41 C)
    R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 he7 hf2 hf9 hfd) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 0
    (bs4 hdf hf2 hf9 he7) R0 R0 R0 (RS 24 A)) (DPNode (MkDag 0 (bs4 hdf hee h5f h7f) R0 R0 R0 (RS 42 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hcf hf3 hff h2f) R0 R0 R0 (RS 29 A)) DPEmpty DPEmpty))) (DPNode (MkDag
    0 (bs4 he5 hf3 hf9 hfd) R0 R0 R0 (RS 7 B)) (DPNode (MkDag 0 (bs4 he7 hf3 hcb hff) R0 R0 R0 (RS 11 B)) (DPNode
    (MkDag 0 (bs4 h9f hf2 hff hcf) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 0 (bs4 h5f h73 hf3 hff) (RS 35 B) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 h7f h9e h5f h7f) (RS 27 D) R0 R0 R0) (DPNode (MkDag 0 (bs4 hbf
    hee h5f h7f) R0 (RS 37 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 hbc hff hcf hfd) R0 (RS 15 C)
    R0 R0) (DPNode (MkDag 0 (bs4 hcb hf2 hf3 hff) (RS 22 D) R0 R0 (RS 23 B)) (DPNode (MkDag 0 (bs4 h79 hf3 hcb hff)
    R0 R0 R0 (RS 39 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hf9 hf3 hf9 h7d) (RS 30 D) R0 R0 (RS 31 A))
    DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs4 he5 hf3 hf9 h7d) R0 R0 R0 (RS 4 B)) (DPNode (MkDag 0 (bs4 he5 hf3 hf9
    he7) R0 R0 R0 (RS 6 B)) (DPNode (MkDag 0 (bs4 he7 hf2 hf9 h7d) R0 R0 R0 (RS 10 B)) (DPNode (MkDag 0 (bs4 h97
    hf2 hff hcf) R0 (RS 18 A) R0 R0) (DPNode (MkDag 0 (bs4 h79 hf3 hf9 hfd) (RS 34 B) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs4 h5f h9e h5f h7f) (RS 26 B) R0 R0 R0) (DPNode (MkDag 0 (bs4 hf3 hf2 hf9 he7) (RS
    41 D) R0 R0 (RS 43 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 he7 hf2 hf3 hff) R0 R0 R0 (RS 1 B))
    (DPNode (MkDag 0 (bs4 hff hf2 hf9 he7) R0 (RS 22 D) R0 R0) (DPNode (MkDag 0 (bs4 hff hee h5f h7f) R0 (RS 38 B)
    R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hb9 hf3 hf9 h7d) R0 (RS 30 C) R0 R0) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs4 he5 hf3 hf3 hff) R0 R0 R0 (RS 8 B)) (DPNode (MkDag 0 (bs4 he7 hf2 hf9 he7) R0 R0 R0 (RS
    12 B)) (DPNode (MkDag 0 (bs4 h7f h73 hcb hff) (RS 20 D) R0 R0 R0) (DPNode (MkDag 0 (bs4 h7f h73 hf3 hff) (RS 36
    D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 hcf h73 hff h2f) R0 R0 R0 (RS 28 D)) (DPNode
    (MkDag 0 (bs4 h79 hf2 hf3 hff) (RS 0 E) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 hfc hff hcf
    hfd) R0 (RS 16 A) R0 R0) (DPNode (MkDag 0 (bs4 h7b h9e h5f h7f) (RS 25 B) R0 R0 R0) (DPNode (MkDag 0 (bs4 hf9
    hf3 hcb hff) (RS 39 D) R0 R0 (RS 40 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs4 h9f h73 hcf h2f) R0 (RS
    32 C) R0 R0) DPEmpty DPEmpty))))).

Definition dagTree_59 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 R0 R0 (RS 0 B)) DPEmpty.

Definition dagTree_60 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hcf h3c hfe h5f h2f hb9) R0 R0 R0 (RS 10 D)) (DPNode (MkDag 0 (bs6 hcf h3c hfe h5f h3f
    hb9) R0 R0 R0 (RS 11 D)) (DPNode (MkDag 0 (bs6 hcf h3c hbe h7f he5 hf9) R0 R0 R0 (RS 12 D)) (DPNode (MkDag 0
    (bs6 hcf h3c hbd hcb hef hf9) R0 R0 R0 (RS 1 D)) (DPNode (MkDag 0 (bs6 hcf h3c hbe h7e h7f hf9) R0 R0 R0 (RS 5
    D)) (DPNode (MkDag 0 (bs6 hbd hcb he7 hcf h3c hf9) R0 R0 (RS 17 E) R0) (DPNode (MkDag 0 (bs6 h9f hf3 hee h79
    he5 hf9) R0 R0 R0 (RS 33 C)) (DPNode (MkDag 0 (bs6 h9f hcf h3e h7f h3f hb9) R0 R0 R0 (RS 65 A)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h73 hfb hfe h7f h3c hf9) R0 R0 R0 (RS 47 B)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs6 h9e h7f h3e h5f h3c hf9) R0 R0 R0 (RS 25 A)) (DPNode (MkDag 0 (bs6 hbe h7f h3e h5f h3f hb9) R0 R0
    (RS 41 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 he7 h9f hfe h5f h2f hb9) R0 R0 R0 (RS 57 A)) DPEmpty
    DPEmpty))) (DPNode (MkDag 0 (bs6 hcf h3c hbe h7f h3f hb9) R0 R0 R0 (RS 9 D)) (DPNode (MkDag 0 (bs6 hbf hcb he7
    hcf h3c hf9) R0 R0 (RS 21 E) R0) (DPNode (MkDag 0 (bs6 h3f h2f h3e h7f h3f hb9) R0 R0 R0 (RS 37 B)) (DPNode
    (MkDag 0 (bs6 h9f h9f hfd hcb hef hf9) R0 R0 R0 (RS 69 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7d
    hcf h3f hcb hef hf9) (RS 53 D) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h97 hcf hf3 hcb hef hf9) R0 R0
    R0 (RS 29 A)) (DPNode (MkDag 0 (bs6 hfe h7e h7e h5e h7f hf9) R0 R0 R0 (RS 45 C)) DPEmpty DPEmpty) (DPNode
    (MkDag 0 (bs6 h97 h9f hee h7f he5 hf9) R0 R0 R0 (RS 61 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs6 hcf h3c
    hbe h7b he5 hf9) R0 R0 R0 (RS 3 D)) (DPNode (MkDag 0 (bs6 hcf h3c hfe h5e h7f hf9) R0 R0 R0 (RS 7 D)) (DPNode
    (MkDag 0 (bs6 haf hcb he7 hcf h3c hf9) R0 R0 (RS 19 E) R0) (DPNode (MkDag 0 (bs6 h77 h2f h3e h7f h3f hb9) R0 R0
    R0 (RS 33 B)) (DPNode (MkDag 0 (bs6 h9f hcf hee h7e h7f hf9) R0 R0 R0 (RS 67 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h3e hf9 h7e h7e h7f hf9) R0 R0 R0 (RS 51 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h97
    hcf h73 hcb hef hf9) R0 R0 R0 (RS 27 A)) (DPNode (MkDag 0 (bs6 hee h7e h7e h5e h7f hf9) R0 R0 R0 (RS 43 B))
    DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h97 hcf hee h5e h7f hf9) R0 R0 R0 (RS 59 A)) DPEmpty DPEmpty))) (DPNode
    (MkDag 0 (bs6 h65 hf9 h7e h7f h3f hb9) R0 R0 R0 (RS 15 B)) (DPNode (MkDag 0 (bs6 he7 hcb hcf hcb hef hf9) R0 R0
    R0 (RS 23 A)) (DPNode (MkDag 0 (bs6 h7d hcb hfe h5f h2f hb9) (RS 39 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 hf3 hcf
    h3e h5e h7f hf9) R0 (RS 7 D) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbf hcf hee h5f he5 hf9) R0
    R0 (RS 55 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h97 hb9 hfe h7f he5 hf9) R0 R0 R0 (RS 31 A)) (DPNode
    (MkDag 0 (bs6 h73 hcf hee h79 he5 hf9) R0 R0 R0 (RS 45 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9e h79 h7e
    h7f h3c hf9) R0 R0 R0 (RS 63 A)) DPEmpty DPEmpty))))) (DPNode (MkDag 0 (bs6 hcf h3c hbe h7f h3c hf9) R0 R0 R0
    (RS 0 D)) (DPNode (MkDag 0 (bs6 hcf h3c hfe h5f h3c hf9) R0 R0 R0 (RS 2 D)) (DPNode (MkDag 0 (bs6 hcf h3c hfe
    h79 h7f hf9) R0 R0 R0 (RS 6 D)) (DPNode (MkDag 0 (bs6 h3d hcb he7 hcf h3c hf9) R0 R0 R0 (RS 18 C)) (DPNode
    (MkDag 0 (bs6 hf7 h2f h3e h7f h3f hb9) R0 R0 (RS 34 E) (RS 35 C)) (DPNode (MkDag 0 (bs6 h97 hcf hee h7e h7f
    hf9) R0 (RS 66 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbe hf9 h7e h7e h7f hf9) R0 R0 (RS 50
    E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h9e h7e h7e h5f h3f hb9) R0 (RS 26 A) R0 R0) (DPNode (MkDag 0
    (bs6 h3e h7f h3e h5f h3f hb9) R0 R0 R0 (RS 42 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f hcf h3e h5f h3f
    hb9) R0 (RS 58 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 h7c hbf hfe h79 he5 hf9) (RS 14 E) R0 R0 R0)
    (DPNode (MkDag 0 (bs6 h3f hcb he7 hcf h3c hf9) R0 R0 R0 (RS 22 B)) (DPNode (MkDag 0 (bs6 he7 hfe h7e h7e h7f
    hf9) R0 R0 R0 (RS 38 B)) (DPNode (MkDag 0 (bs6 h9e h5e h7e h5f h3c hf9) R0 (RS 70 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs6 hcf hcf h3f hcb hef hf9) R0 R0 R0 (RS 54 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0
    (bs6 h9f hcf hf3 hcb hef hf9) R0 (RS 30 A) R0 R0) (DPNode (MkDag 0 (bs6 hf3 hcf hee h79 he5 hf9) (RS 45 D) R0
    (RS 46 E) (RS 47 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f h9f hee h7f he5 hf9) R0 (RS 62 A) R0 R0)
    DPEmpty DPEmpty)))) (DPNode (MkDag 0 (bs6 hcf h3c hbe h79 he5 hf9) (RS 7 D) R0 R0 (RS 4 D)) (DPNode (MkDag 0
    (bs6 hcf h3c hbe h7f h2f hb9) R0 R0 R0 (RS 8 D)) (DPNode (MkDag 0 (bs6 h2f hcb he7 hcf h3c hf9) R0 R0 R0 (RS 20
    C)) (DPNode (MkDag 0 (bs6 hbf h2f h3e h7f h3f hb9) R0 R0 (RS 36 E) R0) (DPNode (MkDag 0 (bs6 h97 h9f hfd hcb
    hef hf9) R0 (RS 68 A) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 he7 hf9 h7e h7e h7f hf9) (RS 51 D)
    R0 R0 (RS 52 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h9f hcf h73 hcb hef hf9) R0 (RS 28 A) R0 R0) (DPNode
    (MkDag 0 (bs6 h7e h7e h7e h5e h7f hf9) R0 R0 R0 (RS 44 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h9f hcf hee
    h5e h7f hf9) R0 (RS 60 A) R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf9 h7e h7f h3f hb9) R0 R0 R0 (RS
    16 C)) (DPNode (MkDag 0 (bs6 h9e h79 hfe h79 h7f hf9) R0 (RS 24 A) R0 R0) (DPNode (MkDag 0 (bs6 hcf hcb hfe h5f
    h2f hb9) R0 R0 R0 (RS 40 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h3f hcf hee h5f he5 hf9) R0 R0 R0 (RS 56
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs6 h9f hb9 hfe h7f he5 hf9) R0 (RS 32 A) R0 R0) (DPNode (MkDag 0 (bs6
    hf3 hfb hfe h7f h3c hf9) R0 R0 (RS 48 E) (RS 49 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h97 hcf h3e h7f h3f
    hb9) R0 (RS 64 A) R0 R0) DPEmpty DPEmpty)))))).

Definition dagTree_61 : DagNTree :=
  MkDagNTree (MkDag 0 (bs5 he5 hf3 hf9 he5 hf3) (RS 0 D) R0 R0 (RS 1 B)) (DPNode (MkDag 1 (bs5 he5 hf3 hf9 he5 hf3)
    (RS 1 D) R0 R0 (RS 2 B)) (DPNode (MkDag 2 (bs5 he5 hf3 hf9 he5 hf3) (RS 2 D) R0 R0 (RS 3 B)) (DPNode (MkDag 4
    (bs5 he5 hf3 hf9 he5 hf3) (RS 4 D) R0 R0 (RS 5 B)) (DPNode (MkDag 8 (bs5 he5 hf3 hf9 he5 hf3) (RS 8 D) R0 R0
    (RS 9 B)) DPEmpty DPEmpty) (DPNode (MkDag 12 (bs5 he5 hf3 hf9 he5 hf3) (RS 12 D) R0 R0 (RS 0 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 6 (bs5 he5 hf3 hf9 he5 hf3) (RS 6 D) R0 R0 (RS 7 B)) (DPNode (MkDag 10 (bs5 he5 hf3
    hf9 he5 hf3) (RS 10 D) R0 R0 (RS 11 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 3 (bs5 he5 hf3 hf9 he5 hf3)
    (RS 3 D) R0 R0 (RS 4 B)) (DPNode (MkDag 5 (bs5 he5 hf3 hf9 he5 hf3) (RS 5 D) R0 R0 (RS 6 B)) (DPNode (MkDag 9
    (bs5 he5 hf3 hf9 he5 hf3) (RS 9 D) R0 R0 (RS 10 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 7 (bs5 he5 hf3 hf9
    he5 hf3) (RS 7 D) R0 R0 (RS 8 B)) (DPNode (MkDag 11 (bs5 he5 hf3 hf9 he5 hf3) (RS 11 D) R0 R0 (RS 12 B))
    DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_62 : DagNTree :=
  MkDagNTree (MkDag 0 nil (RS 0 D) R0 R0 (RS 0 B)) DPEmpty.

Definition dagTree_63 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 hb2 hf9 hef h97) R0 (RS 1 C) R0 R0) (DPNode (MkDag 0 (bs4 hf2 hf9 hef h97) R0 (RS 2 C)
    R0 R0) (DPNode (MkDag 0 (bs4 hf2 hf9 hff h97) R0 (RS 3 C) R0 R0) (DPNode (MkDag 0 (bs4 hf2 hf9 he7 h97) R0 (RS
    5 C) R0 R0) (DPNode (MkDag 0 (bs4 hf2 hf7 h2f hbf) R0 (RS 9 C) R0 R0) (DPNode (MkDag 0 (bs4 h3c hf9 h7c hfe) R0
    R0 R0 (RS 17 C)) (DPNode (MkDag 0 (bs4 he7 hb9 hfc hf3) (RS 32 D) R0 R0 (RS 33 B)) (DPNode (MkDag 0 (bs4 hef
    hf9 h79 hff) R0 R0 R0 (RS 65 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 haf hb9 he7 h97) R0 R0 (RS 97 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h9f hb9 hfc hf3) R0 (RS 49 A) R0 R0) (DPNode (MkDag 0 (bs4 h79 hf9 h7c
    hf3) R0 R0 R0 (RS 81 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h3f hb9 h7f h97) R0 R0 R0 (RS 114 B)) DPEmpty
    DPEmpty))) (DPNode (MkDag 0 (bs4 hbf hf9 hfc hbe) R0 R0 (RS 25 E) R0) (DPNode (MkDag 0 (bs4 hff hb9 h7c hf3) R0
    (RS 41 C) R0 R0) (DPNode (MkDag 0 (bs4 h2f hb9 hf9 hff) R0 R0 R0 (RS 73 C)) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs4 h7f hf9 hfc hf3) (RS 105 E) R0 R0 (RS 100 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h3c hf9 h7c hf3) R0
    R0 R0 (RS 57 C)) (DPNode (MkDag 0 (bs4 hef hf9 h7c hfe) (RS 88 D) R0 R0 (RS 89 B)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 0 (bs4 hf3 hf9 h7c hfe) R0 (RS 13 C) R0 R0) (DPNode (MkDag 0 (bs4 h3f hb9 h79 hff) R0 R0 R0 (RS
    30 B)) (DPNode (MkDag 0 (bs4 hb9 hf9 hf9 hff) R0 (RS 37 C) R0 R0) (DPNode (MkDag 0 (bs4 hef hf9 hfc hbe) (RS 68
    D) R0 R0 (RS 27 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hff hf9 hfc hf3) R0 R0 R0 (RS 101 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs4 h7f h3f h2f hbf) (RS 53 E) R0 R0 R0) (DPNode (MkDag 0 (bs4 haf hb9 h7c hf3) R0
    R0 (RS 85 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h65 hf9 h7c hf3) R0 R0 R0 (RS 14 B)) DPEmpty DPEmpty)))
    (DPNode (MkDag 0 (bs4 he5 hf9 hfc hf3) (RS 28 D) R0 R0 (RS 29 C)) (DPNode (MkDag 0 (bs4 h97 hb9 hff h97) R0 (RS
    45 A) R0 R0) (DPNode (MkDag 0 (bs4 hbc hf9 he5 hff) R0 R0 (RS 77 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4
    h3c hff h2f hbf) R0 R0 R0 (RS 109 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h3f hb9 h7c hfe) R0 R0 R0 (RS 64
    B)) (DPNode (MkDag 0 (bs4 h65 hf9 hff h97) R0 R0 R0 (RS 93 B)) DPEmpty DPEmpty) DPEmpty)))) (DPNode (MkDag 0
    (bs4 hf2 hf9 hfc hfe) R0 (RS 7 C) R0 R0) (DPNode (MkDag 0 (bs4 hf3 hf9 he5 hff) R0 (RS 11 C) R0 R0) (DPNode
    (MkDag 0 (bs4 h2f hb9 h79 hff) R0 R0 R0 (RS 19 C)) (DPNode (MkDag 0 (bs4 h7c hf9 hfc hfe) (RS 35 D) R0 R0 R0)
    (DPNode (MkDag 0 (bs4 haf hb9 hff h97) R0 R0 (RS 67 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hbf hb9 he7
    h97) R0 R0 (RS 99 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h97 h9f h3c hf3) R0 (RS 51 A) R0 R0) (DPNode
    (MkDag 0 (bs4 hef hf7 h2f hbf) (RS 82 D) R0 R0 (RS 83 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hef hf9 h7c
    hbe) (RS 114 D) R0 R0 (RS 115 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs4 hff hf9 hfc hbe) R0 R0 (RS 27 E) (RS
    28 B)) (DPNode (MkDag 0 (bs4 hff hf9 h7c hfe) R0 (RS 43 A) R0 R0) (DPNode (MkDag 0 (bs4 h3f hb9 hf9 hff) R0 R0
    R0 (RS 82 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h3c hf7 h2f hbf) R0 R0 R0 (RS 107 C)) DPEmpty DPEmpty))
    (DPNode (MkDag 0 (bs4 h2f hb9 h7c hfe) R0 R0 R0 (RS 59 C)) (DPNode (MkDag 0 (bs4 h5f hcf h2f hbf) (RS 91 B) R0
    R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs4 he5 hf9 h7c hf3) (RS 14 D) R0 R0 (RS 15 C)) (DPNode
    (MkDag 0 (bs4 h3f hb9 hff h97) R0 R0 R0 (RS 68 B)) (DPNode (MkDag 0 (bs4 hbd hf9 h7c hbe) R0 (RS 39 C) R0 R0)
    (DPNode (MkDag 0 (bs4 h3c hf9 hfc hfe) R0 R0 R0 (RS 71 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hbc hf7 h2f
    hbf) R0 R0 (RS 106 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 he5 hf9 he5 hff) R0 R0 R0 (RS 55 C)) (DPNode
    (MkDag 0 (bs4 hbf hb9 h7c hf3) R0 R0 (RS 87 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h3c hf9 h79 hff) R0
    R0 R0 (RS 0 A)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs4 hef hb9 hff h97) (RS 30 D) R0 R0 (RS 31 B)) (DPNode
    (MkDag 0 (bs4 h9f hf9 hfc hbe) R0 (RS 47 A) R0 R0) (DPNode (MkDag 0 (bs4 hfc hf9 he5 hff) R0 R0 (RS 79 E) (RS
    80 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h2f hb9 h7f h97) R0 R0 R0 (RS 111 C)) DPEmpty DPEmpty)) (DPNode
    (MkDag 0 (bs4 hbc hf9 hef h97) R0 R0 (RS 63 E) R0) (DPNode (MkDag 0 (bs4 hbc hf9 hfc hbe) R0 R0 (RS 95 E) R0)
    DPEmpty DPEmpty) DPEmpty))))) (DPNode (MkDag 0 (bs4 hf2 hf9 hfc hbe) R0 (RS 4 C) R0 R0) (DPNode (MkDag 0 (bs4
    hf2 hf9 hfc hf3) R0 (RS 6 C) R0 R0) (DPNode (MkDag 0 (bs4 hf3 hf9 h7c hbe) R0 (RS 10 C) R0 R0) (DPNode (MkDag 0
    (bs4 haf hb9 h79 hff) R0 R0 (RS 18 E) R0) (DPNode (MkDag 0 (bs4 he7 hf9 hfc hf3) (RS 33 D) R0 R0 (RS 34 B))
    (DPNode (MkDag 0 (bs4 h7f hf9 h79 hff) R0 R0 R0 (RS 61 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h2f hb9 he7
    h97) R0 R0 R0 (RS 98 C)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h9f hf9 hfc hfe) R0 R0 R0 (RS 50 A)) (DPNode
    (MkDag 0 (bs4 hf9 hf9 h7c hf3) R0 R0 R0 (RS 117 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hff hf9 h7c hbe) R0
    R0 R0 (RS 14 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs4 h3f hf9 hfc hbe) R0 R0 R0 (RS 32 B)) (DPNode (MkDag 0
    (bs4 hbf hf9 h7c hfe) R0 (RS 42 C) R0 R0) (DPNode (MkDag 0 (bs4 hbf hb9 hf9 hff) R0 R0 (RS 74 E) R0) DPEmpty
    DPEmpty) (DPNode (MkDag 0 (bs4 h65 hf9 hf9 hff) R0 R0 R0 (RS 101 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4
    haf hb9 h7c hfe) R0 R0 (RS 58 E) R0) (DPNode (MkDag 0 (bs4 h7f hf9 h7c hfe) (RS 90 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs4 hf3 hf9 h79 hff) R0 (RS 1 C) R0 R0) (DPNode (MkDag 0 (bs4 hbf hb9 hff
    h97) R0 R0 (RS 22 E) R0) (DPNode (MkDag 0 (bs4 hf9 hf9 hf9 hff) R0 (RS 38 C) R0 R0) (DPNode (MkDag 0 (bs4 h65
    hf9 hfc hf3) R0 R0 R0 (RS 28 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 he5 hf9 hf9 hff) R0 R0 R0 (RS 102 C))
    DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h65 hf9 he5 hff) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 0 (bs4 h2f hb9 h7c
    hf3) R0 R0 R0 (RS 86 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hbc hf9 h79 hff) R0 R0 (RS 118 E) R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 0 (bs4 hbc hf9 hfc hfe) R0 R0 (RS 70 E) R0) (DPNode (MkDag 0 (bs4 h9f hb9 hff h97) R0
    R0 R0 (RS 46 A)) (DPNode (MkDag 0 (bs4 h3c hf9 he5 hff) R0 R0 R0 (RS 84 C)) DPEmpty DPEmpty) (DPNode (MkDag 0
    (bs4 haf hb9 h7f h97) R0 R0 (RS 110 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 hff hf9 h79 hff) R0 R0 R0
    (RS 62 C)) (DPNode (MkDag 0 (bs4 he5 hf9 hff h97) R0 R0 R0 (RS 94 C)) DPEmpty DPEmpty) DPEmpty)))) (DPNode
    (MkDag 0 (bs4 hf2 hf9 hf9 hff) R0 (RS 8 C) R0 R0) (DPNode (MkDag 0 (bs4 hf3 hf9 h7c hf3) R0 (RS 12 C) R0 R0)
    (DPNode (MkDag 0 (bs4 hbf hb9 h79 hff) R0 R0 (RS 20 E) R0) (DPNode (MkDag 0 (bs4 hcf hb9 hf9 hff) R0 R0 R0 (RS
    36 A)) (DPNode (MkDag 0 (bs4 h2f hb9 hff h97) R0 R0 R0 (RS 21 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h3f
    hb9 he7 h97) R0 R0 R0 (RS 103 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h9f h9f h3c hf3) R0 R0 R0 (RS 52 B))
    (DPNode (MkDag 0 (bs4 h7f hf7 h2f hbf) (RS 78 C) R0 R0 (RS 75 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 h7f
    hf9 h7c hbe) (RS 116 E) R0 R0 (RS 113 B)) DPEmpty DPEmpty))) (DPNode (MkDag 0 (bs4 h7f hf9 hfc hbe) (RS 69 E)
    R0 R0 (RS 26 B)) (DPNode (MkDag 0 (bs4 h9f hcf h2f hbf) R0 R0 R0 (RS 44 A)) (DPNode (MkDag 0 (bs4 hff hf7 h2f
    hbf) R0 R0 R0 (RS 76 C)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hbc hff h2f hbf) R0 R0 (RS 108 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 0 (bs4 hbf hb9 h7c hfe) R0 R0 (RS 60 E) R0) (DPNode (MkDag 0 (bs4 h7f hcf h2f hbf) (RS
    92 E) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs4 hbc hf9 h7c hfe) R0 R0 (RS 16 E) R0) (DPNode
    (MkDag 0 (bs4 hff hb9 hff h97) R0 R0 R0 (RS 24 C)) (DPNode (MkDag 0 (bs4 hfd hf9 h7c hbe) R0 (RS 40 C) R0 R0)
    (DPNode (MkDag 0 (bs4 haf hb9 hf9 hff) R0 R0 (RS 72 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hef hf9 hfc
    hf3) (RS 103 D) R0 R0 (RS 104 B)) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 hbc hf9 h7c hf3) R0 R0 (RS 56 E) R0)
    (DPNode (MkDag 0 (bs4 h3f hb9 h7c hf3) R0 R0 R0 (RS 88 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs4 h7f
    hb9 hff h97) (RS 26 C) R0 R0 (RS 23 B)) (DPNode (MkDag 0 (bs4 h97 hb9 hfc hf3) R0 R0 R0 (RS 48 A)) (DPNode
    (MkDag 0 (bs4 h7c hf9 he5 hff) R0 R0 R0 (RS 78 B)) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs4 hbf hb9 h7f h97) R0
    R0 (RS 112 E) R0) DPEmpty DPEmpty)) (DPNode (MkDag 0 (bs4 h3c hf9 hef h97) R0 R0 R0 (RS 66 C)) (DPNode (MkDag 0
    (bs4 h3c hf9 hfc hbe) R0 R0 R0 (RS 96 C)) DPEmpty DPEmpty) DPEmpty)))))).

Definition dagTree_64 : DagNTree :=
  MkDagNTree (MkDag 0 nil R0 (RS 0 C) R0 R0) DPEmpty.

Definition dagSub_65_136 : DagPTree :=
  DPNode (MkDag 0 (bs6 h7c hf3 hcf h2f hff h3c) (RS 129 E) R0 R0 (RS 108 B)) (DPNode (MkDag 0 (bs6 hcb hf3 hcb he7
    hf7 h3c) (RS 16 D) R0 R0 (RS 91 C)) (DPNode (MkDag 0 (bs6 h3c hf3 hcf he7 h9f h3c) R0 R0 R0 (RS 142 C)) (DPNode
    (MkDag 0 (bs6 haf h73 hcf he7 hf7 h3c) R0 R0 (RS 3 E) R0) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 h7d hff h3c) R0 (RS
    106 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hf9 h7d hff h3c) (RS 96 D) (RS 97 B) R0
    (RS 97 B)) (DPNode (MkDag 0 (bs6 h3f h73 hcf he5 hf7 h3c) R0 R0 R0 (RS 161 C)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs6 h79 hf3 hcf he7 hf7 h3c) (RS 49 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h73 hf3 hf9 he7 h9f
    h3c) R0 R0 R0 (RS 78 B)) (DPNode (MkDag 0 (bs6 hbc hf3 hcb he5 hf7 h3c) R0 R0 (RS 145 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs6 hdf hf3 hf9 h7d hff h3c) R0 R0 R0 (RS 113 A)) (DPNode (MkDag 0 (bs6 he7 hf3 hcb
    he7 hf7 h3c) R0 R0 R0 (RS 177 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf3 hcf h3c hbf h3c)
    (RS 24 D) R0 R0 (RS 135 B)) (DPNode (MkDag 0 (bs6 hfc hf2 hf9 he7 h9f h3c) (RS 40 D) R0 R0 (RS 34 B)) (DPNode
    (MkDag 0 (bs6 hbf hf3 hcf h2f hff h3c) R0 R0 (RS 73 E) R0) (DPNode (MkDag 0 (bs6 he5 hf2 hf9 he7 h9f h3c) (RS
    136 D) R0 R0 (RS 31 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hcf he7 hf7 h3c) (RS 104 D) R0
    R0 (RS 4 B)) (DPNode (MkDag 0 (bs6 h2f h73 hcb he7 h9f h3c) R0 R0 R0 (RS 169 C)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs6 h65 hf3 hcf he5 hf7 h3c) R0 R0 R0 (RS 38 B)) (DPNode (MkDag 0 (bs6 h5f h72 hf9 h7d hff
    h3c) (RS 89 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hbc hf3 hcb hfc hbf h3c) R0 R0 (RS 153 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs6 hbc hf3 hcb he7 hf7 h3c) R0 (RS 121 C) (RS 122 E) R0) (DPNode (MkDag 0 (bs6 h7c
    hf3 hcb hcf hff h3c) R0 R0 R0 (RS 185 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_65_137 : DagPTree :=
  DPNode (MkDag 0 (bs6 h3f h73 hcb hfc hbf h3c) R0 R0 R0 (RS 72 C)) (DPNode (MkDag 0 (bs6 hff hf3 hcf h7c hbf h3c)
    R0 R0 R0 (RS 109 D)) (DPNode (MkDag 0 (bs6 hcf hf3 hcf he7 h9f h3c) R0 R0 R0 (RS 76 A)) (DPNode (MkDag 0 (bs6
    h3f hf2 hf9 he7 h9f h3c) R0 R0 R0 (RS 69 C)) (DPNode (MkDag 0 (bs6 hbf hf3 hcb hcf hff h3c) R0 (RS 133 C) (RS
    134 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hbe h79 he7 h9f h3c) R0 (RS 127 B) R0 (RS 127
    B)) (DPNode (MkDag 0 (bs6 h2f h73 hf9 he7 h9f h3c) R0 R0 R0 (RS 165 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 hbf hf2 hf9 h7d hff h3c) R0 (RS 53 C) R0 R0) (DPNode (MkDag 0 (bs6 hff hf3 hcf hfc hbf h3c) R0
    (RS 85 D) (RS 86 E) (RS 85 D)) (DPNode (MkDag 0 (bs6 hbc hfe h79 he7 h9f h3c) R0 R0 (RS 149 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hdc hf3 hcf h3c hbf h3c) R0 R0 R0 (RS 117 A)) (DPNode (MkDag 0 (bs6 hfc
    hf3 hcf he7 h9f h3c) R0 R0 R0 (RS 181 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h79 hf3 hcb hcf hff
    h3c) (RS 115 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 he5 hf3 hcb he7 hf7 h3c) (RS 44 D) R0 R0 (RS 139 C)) (DPNode
    (MkDag 0 (bs6 hb9 hf3 hcf hcf hff h3c) R0 (RS 77 C) R0 R0) (DPNode (MkDag 0 (bs6 h3c hf3 hcf h7c hbf h3c) R0 R0
    R0 (RS 141 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hcf h2f hff h3c) R0 (RS 7 B) R0 (RS 7
    B)) (DPNode (MkDag 0 (bs6 he7 hf3 hcf he7 hf7 h3c) R0 R0 R0 (RS 173 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 h3d hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 61 C)) (DPNode (MkDag 0 (bs6 h7c hf3 hcf he5 hf7 h3c) R0 R0
    R0 (RS 91 B)) (DPNode (MkDag 0 (bs6 hbf h9e h79 he7 h9f h3c) R0 R0 (RS 25 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h9f h73 hcf he5 hf7 h3c) R0 (RS 125 C) R0 R0) (DPNode (MkDag 0 (bs6 h7c hf3 hcb he7 hf7
    h3c) R0 R0 R0 (RS 121 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_65_138 : DagPTree :=
  DPNode (MkDag 0 (bs6 h7c hbe h79 he7 h9f h3c) (RS 37 D) R0 R0 (RS 100 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hcf hcf
    hff h3c) (RS 18 D) R0 R0 (RS 58 B)) (DPNode (MkDag 0 (bs6 h7c hf3 hcb hfc hbf h3c) (RS 35 D) R0 R0 (RS 33 B))
    (DPNode (MkDag 0 (bs6 h3f h73 hcf he7 hf7 h3c) R0 R0 R0 (RS 67 C)) (DPNode (MkDag 0 (bs6 h7f h73 hcb he7 h9f
    h3c) (RS 131 D) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hdc hbe h79 he7 h9f h3c) R0 R0 R0 (RS
    126 A)) (DPNode (MkDag 0 (bs6 h3f hf3 hcf he7 h9f h3c) R0 R0 R0 (RS 163 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 h7f h72 hf9 he7 h9f h3c) (RS 51 D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h9f h73 hcb he7 h9f h3c) R0
    (RS 83 C) R0 R0) (DPNode (MkDag 0 (bs6 hbc hf3 hcb hcf hff h3c) R0 R0 (RS 147 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hff hf3 hf9 h7d hff h3c) (RS 114 D) R0 R0 (RS 21 D)) (DPNode (MkDag 0 (bs6 hfc hf3 hcf
    h7c hbf h3c) R0 R0 R0 (RS 179 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hfc hfe h79 he7 h9f h3c) R0
    R0 R0 (RS 187 B)) (DPNode (MkDag 0 (bs6 h7c hf3 hf9 h7d hff h3c) R0 R0 R0 (RS 96 B)) (DPNode (MkDag 0 (bs6 hef
    hf3 hcf h7c hbf h3c) (RS 74 D) R0 R0 (RS 75 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hcf h2f hff h3c) (RS 138 D) R0 R0
    (RS 44 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf2 hf9 h7d hff h3c) (RS 106 D) R0 R0 (RS 8 B))
    (DPNode (MkDag 0 (bs6 he7 hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 171 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs6 he5 hf3 hf9 he7 h9f h3c) (RS 58 D) R0 R0 (RS 39 B)) (DPNode (MkDag 0 (bs6 hbf hf3 hcb hfc hbf h3c) R0 (RS
    6 C) R0 R0) (DPNode (MkDag 0 (bs6 haf h9e h79 he7 h9f h3c) R0 R0 (RS 155 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h3c hf3 hcb he7 hf7 h3c) R0 R0 R0 (RS 154 C)) (DPNode (MkDag 0 (bs6 h7c hfe h79 he7 h9f
    h3c) R0 R0 R0 (RS 26 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_65_139 : DagPTree :=
  DPNode (MkDag 0 (bs6 h3f hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 64 C)) (DPNode (MkDag 0 (bs6 hf9 hf3 hcb he5 hf7 h3c)
    (RS 22 D) R0 R0 (RS 82 A)) (DPNode (MkDag 0 (bs6 he5 hf3 hcf he5 hf7 h3c) (RS 38 D) R0 R0 (RS 57 B)) (DPNode
    (MkDag 0 (bs6 h2f h73 hcb hfc hbf h3c) R0 R0 R0 (RS 71 C)) (DPNode (MkDag 0 (bs6 h3f hf3 hcb hcf hff h3c) R0 R0
    R0 (RS 170 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf3 hcf he7 hf7 h3c) (RS 103 D) R0 R0 (RS
    104 B)) (DPNode (MkDag 0 (bs6 h3f h73 hf9 he7 h9f h3c) R0 R0 R0 (RS 113 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 hcb hf3 hcf h2f hff h3c) R0 R0 R0 (RS 55 B)) (DPNode (MkDag 0 (bs6 h7f hf3 hcf hfc hbf h3c) R0 R0
    R0 (RS 84 B)) (DPNode (MkDag 0 (bs6 hbc hf2 hf9 he7 h9f h3c) R0 R0 (RS 151 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h3c hf3 hcf h3c hbf h3c) R0 R0 R0 (RS 150 C)) (DPNode (MkDag 0 (bs6 h7c hf3 hcb he5 hf7
    h3c) R0 R0 R0 (RS 183 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf3 hcb he5 hf7 h3c) (RS 30 D)
    R0 R0 (RS 19 B)) (DPNode (MkDag 0 (bs6 h7f hfe h79 he7 h9f h3c) R0 R0 R0 (RS 45 B)) (DPNode (MkDag 0 (bs6 hf3
    hf3 hf9 he7 h9f h3c) R0 (RS 79 B) (RS 80 E) (RS 79 B)) (DPNode (MkDag 0 (bs6 hbc hf3 hf9 he7 h9f h3c) R0 R0 (RS
    143 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h79 hf3 hcf hcf hff h3c) (RS 27 B) R0 R0 (RS 77 B))
    (DPNode (MkDag 0 (bs6 he7 hf2 hf9 h7d hff h3c) R0 R0 R0 (RS 13 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs6 h2f hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 63 C)) (DPNode (MkDag 0 (bs6 hfc hf3 hcf hcf hff h3c) R0 R0 R0 (RS
    42 B)) (DPNode (MkDag 0 (bs6 h2f h73 hcf he5 hf7 h3c) R0 R0 R0 (RS 159 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs6 hbc hbe h79 he7 h9f h3c) R0 (RS 100 C) R0 R0) DPEmpty DPEmpty))).

Definition dagSub_65_140 : DagPTree :=
  DPNode (MkDag 0 (bs6 h3f h73 hcb he7 h9f h3c) R0 R0 R0 (RS 132 C)) (DPNode (MkDag 0 (bs6 hdc hf3 hf9 h7d hff h3c)
    R0 R0 R0 (RS 95 A)) (DPNode (MkDag 0 (bs6 hfc hf3 hcb hfc hbf h3c) R0 R0 R0 (RS 188 B)) (DPNode (MkDag 0 (bs6
    hbf h73 hcf he7 hf7 h3c) R0 R0 (RS 66 E) R0) (DPNode (MkDag 0 (bs6 h65 hf3 hcf h7c hbf h3c) R0 R0 R0 (RS 7 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf3 hcb he7 h9f h3c) (RS 98 D) R0 R0 (RS 99 B)) (DPNode
    (MkDag 0 (bs6 hbf hf3 hcf he7 h9f h3c) R0 R0 (RS 162 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6
    h5f h72 hf9 he7 h9f h3c) (RS 50 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h5f h73 hcb he7 h9f h3c) (RS 130 B) R0 R0
    R0) (DPNode (MkDag 0 (bs6 h3c hf3 hcb he5 hf7 h3c) R0 R0 R0 (RS 146 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 0 (bs6 hbf hf3 hf9 h7d hff h3c) R0 (RS 114 C) (RS 0 E) R0) (DPNode (MkDag 0 (bs6 h7c hf3 hcf h7c hbf
    h3c) R0 R0 R0 (RS 178 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h3f h9e h79 he7 h9f h3c) R0 R0 R0
    (RS 157 C)) (DPNode (MkDag 0 (bs6 hf9 hf3 hcf h7c hbf h3c) (RS 41 D) R0 R0 (RS 124 A)) (DPNode (MkDag 0 (bs6
    h3f hf3 hcf h2f hff h3c) R0 R0 R0 (RS 74 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hcb hfc hbf h3c) (RS 137 D) R0 R0
    (RS 138 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hdc hf3 hcf h2f hff h3c) R0 R0 R0 (RS 107 A))
    (DPNode (MkDag 0 (bs6 hbf h73 hcb he7 h9f h3c) R0 R0 (RS 9 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs6 he5 hf3 hcf he7 h9f h3c) (RS 57 D) R0 R0 (RS 18 B)) (DPNode (MkDag 0 (bs6 h7f h72 hf9 h7d hff h3c) (RS 1
    D) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3c hf3 hcb hfc hbf h3c) R0 R0 R0 (RS 120 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hfc hf3 hcb he7 hf7 h3c) R0 (RS 123 B) R0 (RS 123 B)) (DPNode (MkDag 0 (bs6 hfc hf3 hcb
    hcf hff h3c) R0 R0 R0 (RS 186 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_65_141 : DagPTree :=
  DPNode (MkDag 0 (bs6 he7 hf3 hcb hfc hbf h3c) R0 R0 R0 (RS 175 B)) (DPNode (MkDag 0 (bs6 hcb hf3 hcb he7 h9f h3c)
    R0 R0 R0 (RS 28 B)) (DPNode (MkDag 0 (bs6 hdc hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 101 A)) (DPNode (MkDag 0 (bs6
    haf h73 hcb hfc hbf h3c) R0 R0 (RS 70 E) R0) (DPNode (MkDag 0 (bs6 hff hf3 hcb hcf hff h3c) (RS 133 D) R0 R0
    (RS 24 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbc hf3 hcf hfc hbf h3c) R0 (RS 23 C) R0 R0) (DPNode
    (MkDag 0 (bs6 hbf h73 hf9 he7 h9f h3c) R0 R0 (RS 166 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0 (bs6
    hff hf2 hf9 h7d hff h3c) (RS 53 D) R0 R0 (RS 54 D)) (DPNode (MkDag 0 (bs6 hcb hf3 hcf he7 hf7 h3c) (RS 85 D) R0
    R0 (RS 87 B)) (DPNode (MkDag 0 (bs6 h3c hfe h79 he7 h9f h3c) R0 R0 R0 (RS 117 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 hbc hf3 hcf h3c hbf h3c) R0 (RS 29 C) (RS 118 E) R0) (DPNode (MkDag 0 (bs6 h7c hf3 hf9
    he7 h9f h3c) R0 R0 R0 (RS 15 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 hfc hf3 hcf h3c hbf h3c) R0
    (RS 119 B) R0 (RS 119 B)) (DPNode (MkDag 0 (bs6 hff hfe h79 he7 h9f h3c) R0 R0 (RS 46 E) (RS 47 D)) (DPNode
    (MkDag 0 (bs6 hf9 hf3 hcf hcf hff h3c) (RS 77 D) (RS 11 A) R0 (RS 11 A)) (DPNode (MkDag 0 (bs6 hbc hf3 hcf he7
    h9f h3c) R0 R0 (RS 32 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hcb hf3 hcf he7 h9f h3c) R0 R0 R0
    (RS 110 B)) (DPNode (MkDag 0 (bs6 he7 hf2 hf9 he7 h9f h3c) R0 R0 R0 (RS 174 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs6 haf hf3 hcf hfc hbf h3c) R0 R0 (RS 62 E) R0) (DPNode (MkDag 0 (bs6 h7c hf3 hcf hcf hff
    h3c) (RS 17 D) R0 R0 (RS 94 B)) (DPNode (MkDag 0 (bs6 haf h73 hcf he5 hf7 h3c) R0 R0 (RS 158 E) R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hf3 hf3 hcf he5 hf7 h3c) (RS 125 D) (RS 110 B) R0 (RS 110 B)) DPEmpty
    DPEmpty))).

Definition dagSub_65_142 : DagPTree :=
  DPNode (MkDag 0 (bs6 h9f h73 hf9 he7 h9f h3c) R0 (RS 78 C) R0 (RS 78 C)) (DPNode (MkDag 0 (bs6 he5 hf3 hcb he7
    h9f h3c) (RS 19 D) R0 R0 (RS 2 B)) (DPNode (MkDag 0 (bs6 hdc hf3 hcb he7 hf7 h3c) R0 R0 R0 (RS 120 A)) (DPNode
    (MkDag 0 (bs6 hbf hf2 hf9 he7 h9f h3c) R0 R0 (RS 68 E) R0) (DPNode (MkDag 0 (bs6 hdf hf3 hcb hcf hff h3c) R0 R0
    R0 (RS 132 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hfc hf3 hcb he7 h9f h3c) (RS 99 D) R0 R0 (RS 10
    B)) (DPNode (MkDag 0 (bs6 haf h73 hf9 he7 h9f h3c) R0 R0 (RS 164 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 hdf hf2 hf9 h7d hff h3c) R0 R0 R0 (RS 52 A)) (DPNode (MkDag 0 (bs6 hf3 hf3 hcb he7 h9f h3c) (RS
    83 D) (RS 84 C) R0 (RS 84 C)) (DPNode (MkDag 0 (bs6 h3c hf3 hcb hcf hff h3c) R0 R0 R0 (RS 148 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h5f h3e h79 he7 h9f h3c) (RS 5 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h7c
    hf3 hcf he7 h9f h3c) R0 R0 R0 (RS 180 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 h5f h73 hf9 he7 h9f
    h3c) (RS 111 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 hcf h73 hcf he7 h9f h3c) R0 R0 R0 (RS 36 D)) (DPNode (MkDag 0
    (bs6 h7f hf3 hcf h7c hbf h3c) (RS 43 D) R0 R0 (RS 20 B)) (DPNode (MkDag 0 (bs6 hbc hf3 hcf h7c hbf h3c) R0 R0
    (RS 140 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hbc hf3 hcf h2f hff h3c) R0 (RS 108 C) R0 R0)
    (DPNode (MkDag 0 (bs6 he7 hf3 hcf h3c hbf h3c) R0 R0 R0 (RS 172 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 0
    (bs6 hbd hf3 hcf hfc hbf h3c) R0 R0 (RS 60 E) R0) (DPNode (MkDag 0 (bs6 hfc hf3 hcf he5 hf7 h3c) R0 R0 (RS 92
    E) (RS 93 B)) (DPNode (MkDag 0 (bs6 h2f h9e h79 he7 h9f h3c) R0 R0 R0 (RS 156 C)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 0 (bs6 h79 hf3 hcf h7c hbf h3c) R0 R0 R0 (RS 41 B)) (DPNode (MkDag 0 (bs6 h7c hf3 hcf h3c hbf
    h3c) R0 R0 R0 (RS 29 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_65_143 : DagPTree :=
  DPNode (MkDag 0 (bs6 hfc hf3 hf9 he7 h9f h3c) R0 R0 R0 (RS 182 B)) (DPNode (MkDag 0 (bs6 hfc hf3 hcf hfc hbf h3c)
    (RS 23 D) (RS 102 B) R0 (RS 102 B)) (DPNode (MkDag 0 (bs6 he5 hf3 hf9 h7d hff h3c) (RS 39 D) R0 R0 (RS 30 B))
    (DPNode (MkDag 0 (bs6 hbf h73 hcb hfc hbf h3c) R0 R0 (RS 12 E) R0) (DPNode (MkDag 0 (bs6 he5 hf3 hcf he7 hf7
    h3c) (RS 135 D) R0 R0 (RS 136 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 hdc hf2 hf9 h7d hff h3c) R0
    R0 R0 (RS 128 A)) (DPNode (MkDag 0 (bs6 haf h73 hcb he7 h9f h3c) R0 R0 (RS 168 E) R0) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 0 (bs6 h79 hf3 hcb he7 hf7 h3c) (RS 56 E) R0 R0 R0) (DPNode (MkDag 0 (bs6 h79 hf2 hf9
    he7 h9f h3c) (RS 88 B) R0 R0 R0) (DPNode (MkDag 0 (bs6 h3c hf2 hf9 he7 h9f h3c) R0 R0 R0 (RS 152 C)) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf2 hf9 he7 h9f h3c) R0 R0 R0 (RS 40 B)) (DPNode (MkDag 0 (bs6 hfc
    hf3 hcb he5 hf7 h3c) R0 R0 R0 (RS 184 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 0 (bs6 he5 hf2 hf9 h7d hff
    h3c) (RS 31 D) R0 R0 (RS 137 B)) (DPNode (MkDag 0 (bs6 hcb hf3 hcf h3c hbf h3c) R0 R0 R0 (RS 48 B)) (DPNode
    (MkDag 0 (bs6 h79 hf3 hcb he5 hf7 h3c) (RS 81 B) R0 R0 (RS 22 B)) (DPNode (MkDag 0 (bs6 h3c hf3 hf9 he7 h9f
    h3c) R0 R0 R0 (RS 144 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0 (bs6 h7f h73 hf9 he7 h9f h3c) (RS 112 D)
    R0 R0 R0) (DPNode (MkDag 0 (bs6 he7 hf3 hcf h2f hff h3c) R0 R0 R0 (RS 176 B)) DPEmpty DPEmpty) DPEmpty))
    (DPNode (MkDag 0 (bs6 hbf hf3 hcf hfc hbf h3c) R0 R0 (RS 14 E) R0) (DPNode (MkDag 0 (bs6 hbc hf3 hf9 h7d hff
    h3c) R0 (RS 96 C) R0 R0) (DPNode (MkDag 0 (bs6 hbf h73 hcf he5 hf7 h3c) R0 R0 (RS 160 E) R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 0 (bs6 h7c hf3 hcf hfc hbf h3c) R0 R0 R0 (RS 23 B)) DPEmpty DPEmpty))).

Definition dagTree_65 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h3f hf3 hf9 h7d hff h3c) R0 R0 R0 (RS 167 C)) (DPNode (MkDag 0 (bs6 hdf hf3 hcb hfc hbf
    h3c) R0 R0 R0 (RS 90 A)) (DPNode (MkDag 0 (bs6 he5 hf3 hcb hcf hff h3c) (RS 2 D) R0 R0 (RS 59 C)) (DPNode
    (MkDag 0 (bs6 h7c hf2 hf9 h7d hff h3c) (RS 105 D) R0 R0 (RS 106 B)) dagSub_65_136 dagSub_65_137) (DPNode (MkDag
    0 (bs6 hff hf3 hcb hfc hbf h3c) (RS 6 D) (RS 16 D) R0 (RS 16 D)) dagSub_65_138 dagSub_65_139)) (DPNode (MkDag 0
    (bs6 h2f h73 hcf he7 hf7 h3c) R0 R0 R0 (RS 65 C)) (DPNode (MkDag 0 (bs6 h7f h3e h79 he7 h9f h3c) (RS 116 D) R0
    R0 R0) dagSub_65_140 dagSub_65_141) (DPNode (MkDag 0 (bs6 he5 hf3 hcf h7c hbf h3c) R0 R0 R0 (RS 38 B))
    dagSub_65_142 dagSub_65_143))).

Definition dagSub_66_144 : DagPTree :=
  DPNode (MkDag 8 (bs6 hf2 hf3 hf3 hf9 h7c hf9) R0 R0 (RS 74 E) (RS 75 A)) (DPNode (MkDag 5 (bs6 h7f h3f hf3 hff
    h3c hfe) (RS 1 B) R0 R0 R0) (DPNode (MkDag 20 (bs6 hfd hcf hf2 hf9 he7 hb9) R0 (RS 33 C) R0 R0) (DPNode (MkDag
    5 (bs6 h97 hcf h3e h5f h3c hfe) R0 (RS 65 A) R0 R0) (DPNode (MkDag 5 (bs6 h7c hfc hf3 hff h3c hfe) (RS 13 B) R0
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 hf7 hfc hbd hcf h2f h97) R0 R0 (RS 193 E) (RS 194 C)) DPEmpty
    DPEmpty)) (DPNode (MkDag 25 (bs6 hff hcb hf2 hf7 h3f h3f) R0 (RS 9 C) R0 R0) (DPNode (MkDag 1 (bs6 hf7 h3f h72
    hf9 he7 h9f) R0 R0 (RS 161 E) (RS 162 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 27 (bs6 h9f hcb he7 h9f h3c
    hfe) R0 R0 R0 (RS 49 A)) (DPNode (MkDag 38 (bs6 h9f h9f h2f hcf hcf hcf) R0 R0 R0 (RS 81 A)) (DPNode (MkDag 12
    (bs6 hfe he7 hf2 hf3 hff hcf) R0 (RS 145 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h5f h2f h3e h79 he7
    hb9) (RS 209 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 43 (bs6 h97 hcf hcf hcf h2f h97) R0 (RS 113 A) R0
    R0) (DPNode (MkDag 44 (bs6 hbc hbc hf2 hff hdc hbe) R0 R0 (RS 177 E) R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 16 (bs6 hfe h5f h73 hf9 he7 hf3) R0 (RS 25 C) R0 R0) (DPNode (MkDag 24 (bs6 he7 hf9 hf9 hf7 h3f h3e) (RS
    40 D) R0 R0 (RS 41 A)) (DPNode (MkDag 4 (bs6 hf2 hf9 hf3 hf9 he7 hb9) R0 R0 (RS 73 E) (RS 8 C)) (DPNode (MkDag
    37 (bs6 h9f h9f hcf h2f h3d hcf) R0 (RS 137 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 25 (bs6 h7f h2f hf2 hf7
    h3f h3f) (RS 201 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 21 (bs6 hbc hff hf2 hf7 h3c hf3) R0 (RS 105 C)
    R0 R0) (DPNode (MkDag 14 (bs6 h2f hcb hff hcb hdc hbf) R0 R0 R0 (RS 169 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 30 (bs6 hf3 hff hf3 hf9 he5 hf9) R0 R0 (RS 57 E) (RS 58 C)) (DPNode (MkDag 22 (bs6 h3f hff he7 h9e he7
    hf7) R0 R0 R0 (RS 89 C)) (DPNode (MkDag 13 (bs6 h9f h3f hf3 hf9 h7f hf9) R0 R0 R0 (RS 153 C)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 3 (bs6 h3f h3f h97 hb9 hfd hcf) R0 R0 R0 (RS 174 A)) (DPNode (MkDag 1 (bs6 hf7 hfc hf2
    hf9 he7 h9f) R0 (RS 185 C) (RS 186 E) (RS 185 C)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_145 : DagPTree :=
  DPNode (MkDag 5 (bs6 he7 hdc hf3 hff h3c hfe) R0 R0 R0 (RS 128 B)) (DPNode (MkDag 13 (bs6 h7f h3f hf3 hf9 h7f
    hf9) (RS 204 B) R0 R0 R0) (DPNode (MkDag 22 (bs6 h79 h79 hf3 hf9 he5 hf7) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 35
    (bs6 h97 h9f hfe h5f h2f h9f) R0 (RS 69 A) R0 R0) (DPNode (MkDag 2 (bs6 h9e h7c hfd hcb hef hf9) R0 (RS 133 A)
    R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs6 h3c hbf h2f h97 hcf hcf) R0 R0 R0 (RS 197 A)) DPEmpty DPEmpty))
    (DPNode (MkDag 40 (bs6 hbe h79 hf3 hcf h3f hb9) R0 (RS 101 C) R0 R0) (DPNode (MkDag 4 (bs6 hbf h2f h3e h79 he7
    hb9) R0 (RS 14 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 29 (bs6 h9f hcb hcf hff h3c hfc) R0 R0 R0
    (RS 53 A)) (DPNode (MkDag 12 (bs6 h9f hdf hf2 hf3 hff hcf) R0 R0 R0 (RS 85 C)) (DPNode (MkDag 25 (bs6 h9f h2f
    hf2 hf7 h3f h3f) R0 (RS 149 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 h7f hcf h2f hcf h2f h97) R0 R0 R0
    (RS 211 B)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs6 hbf h3f h97 hcf h2f hcf) R0 R0 (RS 117 E) R0) (DPNode
    (MkDag 15 (bs6 hf2 hfc hf3 hf7 h3f hb9) R0 (RS 181 A) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 19 (bs6
    hfe h7b hf2 hf9 h7d hcf) R0 (RS 29 C) R0 R0) (DPNode (MkDag 13 (bs6 h9f hf9 h79 hf9 hff hf9) R0 R0 R0 (RS 45
    A)) (DPNode (MkDag 36 (bs6 h9e h7f h73 hcf h2f h97) R0 R0 R0 (RS 77 A)) (DPNode (MkDag 2 (bs6 h97 he7 hf2 hf9
    he7 hcf) R0 R0 R0 (RS 141 A)) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs6 h5f h3f h73 hf7 h3f hb9) (RS 22 B) R0 R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 10 (bs6 h9f hdf hf3 hcb hff hb9) R0 (RS 109 A) R0 R0) (DPNode (MkDag 3
    (bs6 h9f h3f h97 hb9 hfd hcf) R0 (RS 173 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 32 (bs6 hf3 hf7
    h3f hb9 hfc hf7) R0 R0 (RS 61 E) (RS 62 A)) (DPNode (MkDag 6 (bs6 h3f h97 he5 hf3 hfc hbc) R0 R0 R0 (RS 93 C))
    (DPNode (MkDag 15 (bs6 h3f h3f h73 hf7 h3f hb9) R0 R0 R0 (RS 157 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    15 (bs6 hf3 hfc hf3 hf7 h3f hb9) (RS 124 D) R0 (RS 125 E) (RS 126 C)) (DPNode (MkDag 1 (bs6 h3f hfc hf2 hf9 he7
    h9f) R0 R0 R0 (RS 189 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_146 : DagPTree :=
  DPNode (MkDag 10 (bs6 h97 hdf hf3 hcb hff hb9) R0 R0 R0 (RS 108 A)) (DPNode (MkDag 1 (bs6 h7f h3f h72 hf9 he7
    h9f) (RS 208 B) R0 R0 R0) (DPNode (MkDag 22 (bs6 hb9 h79 hf3 hf9 he5 hf7) R0 R0 R0 (RS 35 C)) (DPNode (MkDag 34
    (bs6 h97 hcf hee h5f h2f h9e) R0 (RS 67 A) R0 R0) (DPNode (MkDag 4 (bs6 hfc hfc hfe h79 he7 hb9) R0 R0 (RS 131
    E) (RS 132 A)) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 hbf hfc hbd hcf h2f h97) R0 R0 (RS 15 E) R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 13 (bs6 hf2 hff hf3 hf9 h7f hf9) R0 (RS 99 C) R0 R0) (DPNode (MkDag 1 (bs6 hbf h3f h72
    hf9 he7 h9f) R0 R0 (RS 163 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs6 h9f hcb he7 hf7 h3c hfe) R0
    R0 R0 (RS 51 A)) (DPNode (MkDag 3 (bs6 h9e h7f h72 hf9 hfd hcf) R0 R0 R0 (RS 83 A)) (DPNode (MkDag 6 (bs6 hff
    hf9 he5 hf3 hdc hbc) R0 R0 (RS 147 E) (RS 148 A)) DPEmpty DPEmpty) (DPNode (MkDag 14 (bs6 h7d hcb hff hcb hdc
    hbf) R0 R0 R0 (RS 21 B)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs6 hf7 h3f h97 hcf h2f hcf) R0 R0 (RS 115 E) (RS
    116 C)) (DPNode (MkDag 0 (bs6 hbf hfc hf3 hfe he7 hf7) R0 (RS 179 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode
    (MkDag 18 (bs6 hf3 hcb hee h5f h7f hcf) R0 (RS 27 C) R0 R0) (DPNode (MkDag 13 (bs6 h97 hb9 h7c hf9 hef hf9) R0
    R0 R0 (RS 43 A)) (DPNode (MkDag 8 (bs6 h72 hf3 hf3 hf9 h7c hf9) R0 R0 R0 (RS 8 B)) (DPNode (MkDag 38 (bs6 hff
    h3f h2f h97 hcf hcf) (RS 138 D) R0 R0 (RS 139 A)) DPEmpty DPEmpty) (DPNode (MkDag 9 (bs6 h7f h2f h73 hff hcf
    hff) (RS 203 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 h9e h79 hf2 hf9 he7 h9f) R0 R0 R0 (RS 107 A))
    (DPNode (MkDag 14 (bs6 h3f hcb hff hcb hdc hbf) R0 R0 R0 (RS 171 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    31 (bs6 hf3 hf9 he5 hf9 hfc hbe) R0 R0 (RS 59 E) (RS 60 C)) (DPNode (MkDag 6 (bs6 h2f h97 he5 hf3 hfc hbc) R0
    R0 R0 (RS 91 C)) (DPNode (MkDag 15 (bs6 h77 h3f h73 hf7 h3f hb9) R0 R0 R0 (RS 153 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 15 (bs6 hf3 hdc hf3 hf7 h3f hb9) R0 R0 (RS 123 E) (RS 124 C)) (DPNode (MkDag 1 (bs6 h77 hfc hf2
    hf9 he7 h9f) R0 R0 R0 (RS 184 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_147 : DagPTree :=
  DPNode (MkDag 4 (bs6 hff h2f h3e h79 he7 hb9) (RS 14 D) R0 R0 (RS 165 C)) (DPNode (MkDag 15 (bs6 h7f h3f h73 hf7
    h3f hb9) (RS 205 B) R0 R0 R0) (DPNode (MkDag 23 (bs6 h3f hf9 hfc hbf h3c hbf) R0 R0 R0 (RS 39 B)) (DPNode
    (MkDag 10 (bs6 hf3 hcf h73 hcf hff hb9) R0 R0 (RS 71 E) (RS 72 C)) (DPNode (MkDag 11 (bs6 h9f hdc hbd hcf h2f
    h97) R0 (RS 135 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hff he5 hf2 hf9 hfd hcf) (RS 198 D) R0 R0 (RS
    5 C)) DPEmpty DPEmpty)) (DPNode (MkDag 41 (bs6 hbe h7f h72 hfb he5 hf9) R0 (RS 103 C) R0 R0) (DPNode (MkDag 14
    (bs6 h3d hcb hff hcb hdc hbf) R0 R0 R0 (RS 167 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 30 (bs6 hf3 hdf
    hf3 hf9 he5 hf9) R0 R0 (RS 55 E) (RS 56 C)) (DPNode (MkDag 22 (bs6 h77 hff he7 h9e he7 hf7) R0 R0 R0 (RS 85 B))
    (DPNode (MkDag 9 (bs6 hbf h2f h73 hff hcf hff) R0 (RS 151 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 44 (bs6 h7c
    hbc hf2 hff hdc hbe) (RS 215 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hbf h3f h97 hb9 hfd hcf) R0
    (RS 119 C) (RS 120 E) R0) (DPNode (MkDag 5 (bs6 h97 hdc hf3 hff h3c hfe) R0 (RS 183 A) R0 (RS 183 A)) DPEmpty
    DPEmpty) DPEmpty))) (DPNode (MkDag 19 (bs6 hfe h7f hf2 hf9 h7d hcf) R0 (RS 31 C) R0 R0) (DPNode (MkDag 26 (bs6
    h9f hcf h3f h9f he5 hf9) R0 R0 R0 (RS 47 A)) (DPNode (MkDag 37 (bs6 h9f hdf hff hcf h3f hcf) R0 R0 R0 (RS 79
    A)) (DPNode (MkDag 3 (bs6 hf3 he7 hf2 hf9 hfd hcf) R0 (RS 143 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 21 (bs6
    h7f h2f h72 hf7 h3c hf3) (RS 207 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 h9f hb9 h7e h79 h79 hf9)
    R0 (RS 111 A) R0 R0) (DPNode (MkDag 12 (bs6 hbf h3f h9f hf3 hff hcf) R0 (RS 17 C) (RS 175 E) R0) DPEmpty
    DPEmpty) DPEmpty)) (DPNode (MkDag 33 (bs6 h9e h7b hfd hcb hef hf9) R0 (RS 63 A) R0 R0) (DPNode (MkDag 11 (bs6
    h3c hbf hfc hf2 hf9 he7) R0 R0 R0 (RS 95 A)) (DPNode (MkDag 21 (bs6 hff h2f h72 hf7 h3c hf3) R0 (RS 159 A) R0
    R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 41 (bs6 hbe h7c hf2 hfb he5 hf9) R0 R0 (RS 127 E) R0) (DPNode
    (MkDag 7 (bs6 h9e h7c hfe h79 h79 hf9) R0 R0 R0 (RS 191 A)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_148 : DagPTree :=
  DPNode (MkDag 9 (bs6 hbe h5f h73 hff hcf hff) R0 (RS 97 C) R0 R0) (DPNode (MkDag 12 (bs6 hff h3f h9f hf3 hff hcf)
    (RS 17 D) R0 R0 (RS 214 B)) (DPNode (MkDag 21 (bs6 hff h9f h72 hf9 h79 hf3) R0 (RS 34 A) R0 R0) (DPNode (MkDag
    5 (bs6 h9f hcf h3e h5f h3c hfe) R0 R0 R0 (RS 66 A)) (DPNode (MkDag 10 (bs6 h7e h7c hf3 hcb hff hb9) (RS 130 C)
    R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 h77 hfc hbd hcf h2f h97) R0 R0 R0 (RS 192 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 9 (bs6 hfe h5f h73 hff hcf hff) R0 (RS 98 C) R0 R0) (DPNode (MkDag 1 (bs6 h77 h3f h72
    hf9 he7 h9f) R0 R0 R0 (RS 160 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 28 (bs6 h97 hcb he7 hf7 h3c hfe) R0
    (RS 50 A) R0 R0) (DPNode (MkDag 39 (bs6 h9e h79 hfc hf3 hff hcf) R0 (RS 82 A) R0 R0) (DPNode (MkDag 6 (bs6 hbf
    hf9 he5 hf3 hdc hbc) R0 R0 R0 (RS 146 C)) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h7f h2f h3e h79 he7 hb9) (RS
    21 C) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 43 (bs6 h9f hcf hcf hcf h2f h97) R0 R0 R0 (RS 114 C)) (DPNode
    (MkDag 44 (bs6 h3c hbc hf2 hff hdc hbe) R0 R0 R0 (RS 178 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 17 (bs6
    hf2 hff hf3 hf9 hfd hcb) R0 (RS 26 C) R0 R0) (DPNode (MkDag 25 (bs6 h9f he5 he7 hcf h3f h3f) R0 (RS 42 A) R0
    R0) (DPNode (MkDag 4 (bs6 h72 hf9 hf3 hf9 he7 hb9) R0 R0 R0 (RS 72 B)) (DPNode (MkDag 38 (bs6 h7f h3f h2f h97
    hcf hcf) R0 R0 R0 (RS 138 B)) DPEmpty DPEmpty) (DPNode (MkDag 9 (bs6 h5f h2f h73 hff hcf hff) (RS 202 B) R0 R0
    R0) DPEmpty DPEmpty)) (DPNode (MkDag 21 (bs6 hfc hff hf2 hf7 h3c hf3) R0 (RS 106 A) R0 R0) (DPNode (MkDag 14
    (bs6 hbf hcb hff hcb hdc hbf) R0 R0 (RS 170 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 30 (bs6 h73 hff
    hf3 hf9 he5 hf9) R0 R0 R0 (RS 56 B)) (DPNode (MkDag 6 (bs6 haf h97 he5 hf3 hfc hbc) R0 R0 (RS 90 E) R0) (DPNode
    (MkDag 15 (bs6 hf7 h3f h73 hf7 h3f hb9) R0 R0 (RS 154 E) (RS 155 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag
    12 (bs6 h9f h3f h9f hf3 hff hcf) R0 (RS 11 A) R0 R0) (DPNode (MkDag 1 (bs6 hbf hfc hf2 hf9 he7 h9f) R0 (RS 187
    C) (RS 188 E) R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_149 : DagPTree :=
  DPNode (MkDag 10 (bs6 h5e h7c hf3 hcb hff hb9) (RS 129 B) R0 R0 R0) (DPNode (MkDag 14 (bs6 hfd hcb hff hcb hdc
    hbf) R0 R0 (RS 210 E) (RS 211 C)) (DPNode (MkDag 23 (bs6 hbf hf9 hfc hbf h3c hbf) R0 R0 (RS 38 E) R0) (DPNode
    (MkDag 35 (bs6 h9f h9f hfe h5f h2f h9f) R0 R0 R0 (RS 70 C)) (DPNode (MkDag 11 (bs6 h97 hdc hbd hcf h2f h97) R0
    R0 R0 (RS 134 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hbf he5 hf2 hf9 hfd hcf) R0 (RS 198 C) R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 40 (bs6 hfe h79 hf3 hcf h3f hb9) R0 (RS 102 C) R0 R0) (DPNode (MkDag 14 (bs6 hbd hcb
    hff hcb hdc hbf) R0 R0 (RS 166 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 1 (bs6 h9e h79 he7 he7 he7 h9f)
    R0 (RS 7 A) R0 R0) (DPNode (MkDag 22 (bs6 hf7 hff he7 h9e he7 hf7) R0 R0 (RS 86 E) (RS 87 C)) (DPNode (MkDag 9
    (bs6 hf7 h2f h73 hff hcf hff) R0 (RS 150 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 19 (bs6 h9f h3f h97 hcf h2f
    hcf) R0 (RS 3 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs6 h3f h3f h97 hcf h2f hcf) R0 R0 R0 (RS 118 A))
    (DPNode (MkDag 41 (bs6 h9e h7c hf2 hfb he5 hf9) R0 (RS 182 A) R0 (RS 182 A)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 19 (bs6 hbe h7f hf2 hf9 h7d hcf) R0 (RS 30 C) R0 R0) (DPNode (MkDag 26 (bs6 h97 hcf h3f h9f he5
    hf9) R0 (RS 46 A) R0 R0) (DPNode (MkDag 37 (bs6 h97 hdf hff hcf h3f hcf) R0 (RS 78 A) R0 R0) (DPNode (MkDag 2
    (bs6 h9f he7 hf2 hf9 he7 hcf) R0 (RS 142 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 21 (bs6 h5f h2f h72 hf7 h3c
    hf3) (RS 206 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs6 h97 hb9 h7e h79 h79 hf9) R0 R0 R0 (RS 110 A))
    (DPNode (MkDag 12 (bs6 hf7 h3f h9f hf3 hff hcf) (RS 173 D) R0 R0 (RS 174 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 32 (bs6 h73 hf7 h3f hb9 hfc hf7) R0 R0 R0 (RS 60 B)) (DPNode (MkDag 11 (bs6 hbc hbf hfc hf2 hf9 he7) R0
    R0 (RS 94 E) R0) (DPNode (MkDag 21 (bs6 hbf h2f h72 hf7 h3c hf3) R0 (RS 158 C) R0 R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 15 (bs6 h73 hfc hf3 hf7 h3f hb9) R0 R0 R0 (RS 124 B)) (DPNode (MkDag 4 (bs6 hb2 hfc hfe h79 he7
    hb9) R0 (RS 4 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_150 : DagPTree :=
  DPNode (MkDag 0 (bs6 h9f hfc hf3 hfe he7 hf7) R0 R0 R0 (RS 122 C)) (DPNode (MkDag 6 (bs6 hf2 hf9 he5 hf3 hdc hbc)
    (RS 19 D) R0 (RS 6 E) (RS 200 B)) (DPNode (MkDag 22 (bs6 hf9 h79 hf3 hf9 he5 hf7) R0 R0 (RS 36 E) (RS 37 C))
    (DPNode (MkDag 34 (bs6 h9f hcf hee h5f h2f h9e) R0 R0 R0 (RS 68 A)) (DPNode (MkDag 4 (bs6 h7c hfc hfe h79 he7
    hb9) R0 R0 R0 (RS 130 B)) DPEmpty DPEmpty) (DPNode (MkDag 38 (bs6 hbc hbf h2f h97 hcf hcf) R0 R0 (RS 196 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 15 (bs6 hf3 hcb hf3 hf7 h3f hb9) R0 (RS 100 C) R0 R0) (DPNode (MkDag 1 (bs6
    h3f h3f h72 hf9 he7 h9f) R0 R0 R0 (RS 164 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 29 (bs6 h97 hcb hcf hff
    h3c hfc) R0 (RS 52 A) R0 R0) (DPNode (MkDag 12 (bs6 h97 hdf hf2 hf3 hff hcf) R0 (RS 84 A) R0 R0) (DPNode (MkDag
    6 (bs6 h7f hf9 he5 hf3 hdc hbc) R0 R0 R0 (RS 146 B)) DPEmpty DPEmpty) (DPNode (MkDag 11 (bs6 hff hcf h2f hcf
    h2f h97) (RS 211 D) R0 (RS 212 E) (RS 213 A)) DPEmpty DPEmpty)) (DPNode (MkDag 19 (bs6 h77 h3f h97 hcf h2f hcf)
    R0 R0 R0 (RS 114 B)) (DPNode (MkDag 0 (bs6 hff hfc hf3 hfe he7 hf7) R0 (RS 180 C) R0 R0) DPEmpty DPEmpty)
    DPEmpty))) (DPNode (MkDag 19 (bs6 hbe h7b hf2 hf9 h7d hcf) R0 (RS 28 C) R0 R0) (DPNode (MkDag 13 (bs6 h9f hb9
    h7c hf9 hef hf9) R0 (RS 44 A) R0 R0) (DPNode (MkDag 2 (bs6 h9e h79 hf3 hcf hef hf9) R0 (RS 76 A) R0 R0) (DPNode
    (MkDag 2 (bs6 h9e he7 hf2 hf9 he7 hcf) R0 (RS 140 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 13 (bs6 h5f h3f hf3
    hf9 h7f hf9) (RS 20 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 42 (bs6 h9e h7f h72 hf9 h7d hf9) R0 (RS 10 A)
    R0 R0) (DPNode (MkDag 11 (bs6 he7 hcf h2f hcf h2f h97) R0 R0 R0 (RS 172 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 31 (bs6 h73 hf9 he5 hf9 hfc hbe) R0 R0 R0 (RS 58 B)) (DPNode (MkDag 6 (bs6 hbf h97 he5 hf3 hfc hbc) R0
    R0 (RS 92 E) R0) (DPNode (MkDag 15 (bs6 hbf h3f h73 hf7 h3f hb9) R0 R0 (RS 156 E) R0) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 15 (bs6 h73 hdc hf3 hf7 h3f hb9) R0 R0 R0 (RS 122 B)) (DPNode (MkDag 1 (bs6 hff hfc hf2 hf9 he7
    h9f) R0 (RS 4 C) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_66_151 : DagPTree :=
  DPNode (MkDag 11 (bs6 h3f hfc hbd hcf h2f h97) R0 R0 R0 (RS 195 C)) (DPNode (MkDag 16 (bs6 hbe h5f h73 hf9 he7
    hf3) R0 (RS 24 C) R0 R0) (DPNode (MkDag 24 (bs6 he7 hb9 hf9 hf7 h3f h3e) (RS 39 D) R0 R0 (RS 40 B)) (DPNode
    (MkDag 10 (bs6 h73 hcf h73 hcf hff hb9) R0 R0 R0 (RS 70 B)) (DPNode (MkDag 37 (bs6 h97 h9f hcf h2f h3d hcf) R0
    R0 R0 (RS 136 A)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h72 hff hcf h97 hfe h7e) R0 R0 R0 (RS 5 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 41 (bs6 hfe h7f h72 hfb he5 hf9) R0 (RS 104 C) R0 R0) (DPNode (MkDag 14 (bs6 haf hcb
    hff hcb hdc hbf) R0 R0 (RS 168 E) R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 30 (bs6 h73 hdf hf3 hf9 he5
    hf9) R0 R0 R0 (RS 54 B)) (DPNode (MkDag 22 (bs6 hbf hff he7 h9e he7 hf7) R0 R0 (RS 88 E) R0) (DPNode (MkDag 9
    (bs6 hff h2f h73 hff hcf hff) R0 (RS 152 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 0 (bs6 h5f hfc hf3 hfe he7
    hf7) (RS 0 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hff h3f h97 hb9 hfd hcf) (RS 119 D) R0 R0 (RS
    121 A)) (DPNode (MkDag 5 (bs6 h9f hdc hf3 hff h3c hfe) R0 (RS 184 C) R0 (RS 184 C)) DPEmpty DPEmpty) DPEmpty)))
    (DPNode (MkDag 20 (bs6 hbd hcf hf2 hf9 he7 hb9) R0 (RS 32 C) R0 R0) (DPNode (MkDag 27 (bs6 h97 hcb he7 h9f h3c
    hfe) R0 (RS 48 A) R0 R0) (DPNode (MkDag 38 (bs6 h97 h9f h2f hcf hcf hcf) R0 (RS 80 A) R0 R0) (DPNode (MkDag 12
    (bs6 hbe he7 hf2 hf3 hff hcf) R0 (RS 144 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h5f h3f hf3 hff h3c
    hfe) (RS 16 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 14 (bs6 h9f hcf he7 hcb hdc hbf) R0 R0 R0 (RS 112 A))
    (DPNode (MkDag 12 (bs6 h3f h3f h9f hf3 hff hcf) R0 R0 R0 (RS 176 C)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    33 (bs6 h9e h7f hfd hcb hef hf9) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 25 (bs6 hbf hcb hf2 hf7 h3f h3f) R0 (RS 96
    C) R0 R0) (DPNode (MkDag 5 (bs6 h9f h3f hf3 hff h3c hfe) R0 R0 R0 (RS 160 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 41 (bs6 h3e h7c hf2 hfb he5 hf9) R0 R0 R0 (RS 12 B)) (DPNode (MkDag 2 (bs6 h97 hdc hfd hcb hef hf9) R0
    (RS 2 A) R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagTree_66 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 h7f hfc hf3 hfe he7 hf7) (RS 181 A) R0 R0 R0) (DPNode (MkDag 1 (bs6 h5f h3f h72 hf9 he7
    h9f) (RS 18 B) R0 R0 R0) (DPNode (MkDag 2 (bs6 h9f hdc hfd hcb hef hf9) R0 R0 R0 (RS 192 C)) (DPNode (MkDag 4
    (bs6 hf2 hfc hfe h79 he7 hb9) R0 (RS 190 A) R0 R0) dagSub_66_144 dagSub_66_145) (DPNode (MkDag 6 (bs6 h72 hf9
    he5 hf3 hdc hbc) R0 R0 R0 (RS 19 B)) dagSub_66_146 dagSub_66_147)) (DPNode (MkDag 3 (bs6 hf7 h3f h97 hb9 hfd
    hcf) (RS 3 D) R0 R0 (RS 118 C)) (DPNode (MkDag 5 (bs6 hf2 hff hcf h97 hfe h7e) R0 R0 (RS 199 E) (RS 19 C))
    dagSub_66_148 dagSub_66_149) (DPNode (MkDag 7 (bs6 h9e h5f h72 hf7 h2f hb9) R0 R0 R0 (RS 54 C)) dagSub_66_150
    dagSub_66_151))).

Definition dagSub_67_152 : DagPTree :=
  DPNode (MkDag 1 (bs6 h9e h5f hff hf3 hcf h9e) R0 R0 R0 (RS 60 A)) (DPNode (MkDag 7 (bs6 hbe h5f hfc hbd hcb he7)
    R0 R0 (RS 17 E) R0) (DPNode (MkDag 12 (bs6 hbf h9f hcf h3e h7f h3f) R0 R0 (RS 33 E) R0) (DPNode (MkDag 6 (bs6
    h9f hcf he5 hf3 hdf h2f) R0 (RS 65 A) R0 R0) (DPNode (MkDag 2 (bs6 h9f hff hff he7 hf7 h3f) R0 (RS 129 A) R0
    (RS 129 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 4 (bs6 h3f hb9 h7f hfc hbf h3c) R0 R0 R0 (RS 97 B))
    (DPNode (MkDag 22 (bs6 h7f hf2 hfc hff he7 hfe) (RS 161 D) R0 R0 (RS 162 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 17 (bs6 he7 hb9 h7d hcb he5 hf3) (RS 48 D) R0 R0 (RS 49 B)) (DPNode (MkDag 3 (bs6 h7c hbf hfb h9f he7
    hf2) R0 R0 R0 (RS 79 B)) (DPNode (MkDag 0 (bs6 h9f h9f hcf he7 he7 hee) R0 (RS 4 B) R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 6 (bs6 haf hf3 hff h97 hdf h2f) R0 R0 (RS 113 E) R0) (DPNode (MkDag 1 (bs6 h73 hff h9f
    hff hfb h9e) R0 R0 R0 (RS 175 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 10 (bs6 hbf h9e h79 hfe h5f he7)
    R0 R0 (RS 25 E) R0) (DPNode (MkDag 14 (bs6 hbf h9f hcf h2f hbf hcf) R0 R0 (RS 41 E) R0) (DPNode (MkDag 19 (bs6
    h9f hcf h2f h72 hff he7) R0 (RS 73 A) R0 R0) (DPNode (MkDag 3 (bs6 h7b h9e h7f h9f he7 hf2) (RS 138 B) R0 R0
    (RS 139 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 haf h9f h2f h97 h9e he7) R0 R0 (RS 105 E) R0)
    (DPNode (MkDag 4 (bs6 h5f h9e h7f he7 hcb hfc) (RS 169 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    18 (bs6 h9f hb9 h7d hcf he7 hfe) R0 R0 R0 (RS 57 A)) (DPNode (MkDag 6 (bs6 hff hff h2f h97 hdf h2f) (RS 88 D)
    R0 R0 (RS 89 B)) (DPNode (MkDag 22 (bs6 h7f hfe h5f hcf he7 hfe) R0 R0 R0 (RS 153 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 3 (bs6 hff h97 he7 h9f he7 hf2) R0 (RS 121 B) (RS 122 E) (RS 121 B)) (DPNode (MkDag 4 (bs6 h5f
    h9f hcf hdc hff h3c) (RS 4 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_67_153 : DagPTree :=
  DPNode (MkDag 6 (bs6 hf2 hff he7 h97 hdf h2f) R0 R0 (RS 159 E) (RS 160 B)) (DPNode (MkDag 9 (bs6 hbc hf2 hfc hff
    hcf hfc) R0 R0 (RS 21 E) R0) (DPNode (MkDag 13 (bs6 hbf h9f hcf hee h7e h7e) R0 R0 (RS 37 E) R0) (DPNode (MkDag
    20 (bs6 h9f hcf he5 he7 he5 hee) R0 (RS 69 A) R0 R0) (DPNode (MkDag 15 (bs6 hf3 hff hf7 h2f hff h3f) (RS 132 D)
    (RS 134 C) (RS 135 E) (RS 134 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 17 (bs6 hbc hf9 he7 hf3 he7 hf3) R0
    R0 (RS 101 E) R0) (DPNode (MkDag 0 (bs6 hfb h9f hcf h3e he7 hee) (RS 164 D) R0 R0 (RS 165 A)) DPEmpty DPEmpty)
    DPEmpty)) (DPNode (MkDag 15 (bs6 hb9 hff hcb hff h9f h3f) R0 (RS 53 C) R0 R0) (DPNode (MkDag 4 (bs6 h7f h2f h3d
    hff hcb hfc) (RS 85 E) R0 R0 R0) (DPNode (MkDag 2 (bs6 h7f h3f hf7 hf9 hf7 h3f) (RS 149 B) R0 R0 R0) DPEmpty
    DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hbf h3f hf7 hf9 hf7 h3f) R0 (RS 117 C) R0 R0) (DPNode (MkDag 3 (bs6 h9f
    h9e h7f h9f he7 hf2) R0 (RS 181 B) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 11 (bs6 hbf h9e h7e h7e
    h7f h2f) R0 R0 (RS 29 E) R0) (DPNode (MkDag 15 (bs6 hbf h9f hb9 hff h9f h2f) R0 R0 (RS 45 E) R0) (DPNode (MkDag
    16 (bs6 h9e h79 h7c hfe he7 hee) R0 (RS 77 B) R0 R0) (DPNode (MkDag 3 (bs6 h7f h9e h7f h9f he7 hf2) (RS 141 D)
    R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 haf h9f hf2 hf9 h7b h9e) R0 R0 (RS 109 E) R0) (DPNode
    (MkDag 17 (bs6 hb9 hf9 he7 hf3 he7 hf3) R0 (RS 173 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 19 (bs6
    h9e h7e h5f h72 hf9 he5) R0 (RS 61 A) R0 R0) (DPNode (MkDag 4 (bs6 hbc hfe h7f he7 hcb hfc) R0 R0 (RS 93 E) R0)
    (DPNode (MkDag 3 (bs6 h3e h5f h72 hff he7 hf2) R0 R0 R0 (RS 157 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2
    (bs6 hfc hbc hf7 hf9 hf7 h3f) R0 R0 R0 (RS 151 A)) (DPNode (MkDag 15 (bs6 h9e h79 h7f h2f hff h3f) R0 R0 R0 (RS
    147 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_67_154 : DagPTree :=
  DPNode (MkDag 3 (bs6 hbf h97 he7 h9f he7 hf2) R0 (RS 120 C) R0 R0) (DPNode (MkDag 8 (bs6 hbc hbf hfc hfd hcb he7)
    R0 R0 (RS 19 E) R0) (DPNode (MkDag 13 (bs6 haf h9f hcf hee h7e h7e) R0 R0 (RS 35 E) R0) (DPNode (MkDag 6 (bs6
    h9f hcf he5 hf3 hff h2f) R0 (RS 67 A) R0 R0) (DPNode (MkDag 3 (bs6 h9e h5f h72 hff he7 hf2) R0 (RS 131 C) R0
    (RS 131 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 15 (bs6 h7f hf9 h7f h2f hff h3f) R0 R0 R0 (RS 99 B))
    (DPNode (MkDag 22 (bs6 hff hf2 hfc hff he7 hfe) R0 R0 R0 (RS 186 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag
    0 (bs6 h7d hcb hff hcb he5 hee) (RS 51 D) R0 R0 R0) (DPNode (MkDag 17 (bs6 h9e h5f h97 hcf he7 hf3) R0 (RS 83
    C) R0 R0) (DPNode (MkDag 4 (bs6 hff h9f hcf hdc hff h3c) (RS 146 D) R0 R0 (RS 147 B)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 6 (bs6 hbf hf3 hff h97 hdf h2f) R0 R0 (RS 115 E) R0) (DPNode (MkDag 3 (bs6 hfb h97 he7 h9f he7
    hf2) R0 R0 R0 (RS 185 A)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 11 (bs6 haf h9e h7e h7e h7f h2f) R0 R0 (RS
    27 E) R0) (DPNode (MkDag 15 (bs6 haf h9f hb9 hff h9f h2f) R0 R0 (RS 43 E) R0) (DPNode (MkDag 21 (bs6 h9f hcf
    h3f h9f hcf hff) R0 (RS 75 A) R0 R0) (DPNode (MkDag 3 (bs6 h5f h9e h7f h9f he7 hf2) (RS 140 B) R0 R0 R0)
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 hbf h9f h2f h97 h9e he7) R0 R0 (RS 107 E) R0) (DPNode (MkDag 15
    (bs6 hfe h79 h7f h2f hff h3f) R0 R0 (RS 171 E) (RS 172 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs6 h97
    hcb hcf h3d hff h3f) R0 R0 R0 (RS 59 A)) (DPNode (MkDag 0 (bs6 h65 hff he5 he7 he7 hee) R0 R0 R0 (RS 91 B))
    (DPNode (MkDag 1 (bs6 h7f hcb hf2 hf7 hfb h9e) R0 R0 R0 (RS 1 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 3
    (bs6 h7f h97 he7 h9f he7 hf2) (RS 150 D) R0 R0 (RS 120 B)) (DPNode (MkDag 0 (bs6 h7b h9f hcf h3e he7 hee) R0 R0
    R0 (RS 164 B)) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_67_155 : DagPTree :=
  DPNode (MkDag 1 (bs6 h9f hcb hf2 hf7 hfb h9e) R0 (RS 130 A) R0 (RS 130 A)) (DPNode (MkDag 10 (bs6 haf h9e h79 hfe
    h5f he7) R0 R0 (RS 23 E) R0) (DPNode (MkDag 14 (bs6 haf h9f hcf h2f hbf hcf) R0 R0 (RS 39 E) R0) (DPNode (MkDag
    17 (bs6 h9f hcf h3f hbf he7 hf3) R0 (RS 71 A) R0 R0) (DPNode (MkDag 6 (bs6 hf3 hff he7 h97 hdf h2f) R0 (RS 136
    B) (RS 137 E) (RS 136 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 hbc hff hf7 hf9 hf7 h3f) R0 R0 (RS
    103 E) R0) (DPNode (MkDag 0 (bs6 h7f h9f hcf he7 he7 hee) R0 R0 R0 (RS 0 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 6 (bs6 h9f h3f hff hcf h3f h2f) R0 R0 R0 (RS 55 A)) (DPNode (MkDag 0 (bs6 he7 h97 hcf h9e he7 hee) R0 R0
    R0 (RS 87 A)) (DPNode (MkDag 0 (bs6 hdc hbe he7 he7 he7 hee) R0 R0 R0 (RS 179 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 1 (bs6 hbf hff h9f hff hfb h9e) R0 (RS 119 C) R0 R0) (DPNode (MkDag 0 (bs6 hff h9f hcf h3e he7
    hee) (RS 182 D) R0 R0 (RS 183 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 12 (bs6 haf h9f hcf h3e h7f h3f)
    R0 R0 (RS 31 E) R0) (DPNode (MkDag 16 (bs6 hbc hbf h2f hcb he5 hee) R0 R0 (RS 47 E) R0) (DPNode (MkDag 5 (bs6
    hff hff hff h2f h97 he7) (RS 78 D) R0 R0 (RS 79 C)) (DPNode (MkDag 0 (bs6 hbb h9f hcf he7 he7 hee) R0 (RS 143
    C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 hbf h9f hf2 hf9 h7b h9e) R0 R0 (RS 111 E) R0) (DPNode
    (MkDag 5 (bs6 h97 h97 h9f h2f h97 he7) R0 (RS 6 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs6 h9f
    hcf he5 hff he7 hfd) R0 (RS 63 A) R0 R0) (DPNode (MkDag 4 (bs6 haf hb9 h7f hfc hbf h3c) R0 R0 (RS 9 E) R0)
    (DPNode (MkDag 15 (bs6 hf2 hff hf7 h2f hff h3f) (RS 158 D) R0 R0 (RS 12 C)) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 2 (bs6 hbb hff hff he7 hf7 h3f) R0 (RS 127 C) R0 R0) DPEmpty DPEmpty))).

Definition dagSub_67_156 : DagPTree :=
  DPNode (MkDag 4 (bs6 h2f hb9 h7f hfc hbf h3c) R0 R0 R0 (RS 95 C)) (DPNode (MkDag 7 (bs6 h3e h5f hfc hbd hcb he7)
    R0 R0 R0 (RS 18 C)) (DPNode (MkDag 12 (bs6 h3f h9f hcf h3e h7f h3f) R0 R0 R0 (RS 34 C)) (DPNode (MkDag 6 (bs6
    h97 hcf he5 hf3 hff h2f) R0 R0 R0 (RS 66 A)) (DPNode (MkDag 1 (bs6 h97 hcb hf2 hf7 hfb h9e) R0 (RS 14 A) R0 (RS
    14 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 15 (bs6 hef hf9 h7f h2f hff h3f) R0 R0 R0 (RS 98 B)) (DPNode
    (MkDag 3 (bs6 hcf h9e h7f h9f he7 hf2) R0 R0 R0 (RS 163 A)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs6
    he7 hf9 h7d hcb he5 hf3) (RS 49 D) R0 R0 (RS 50 B)) (DPNode (MkDag 16 (bs6 he7 hff h97 hcf he7 hee) (RS 81 D)
    R0 R0 (RS 82 A)) (DPNode (MkDag 4 (bs6 hcf h9e h7f he7 hcb hfc) R0 R0 R0 (RS 172 A)) DPEmpty DPEmpty) DPEmpty)
    (DPNode (MkDag 6 (bs6 h2f hf3 hff h97 hdf h2f) R0 R0 R0 (RS 114 C)) (DPNode (MkDag 3 (bs6 h5f h97 he7 h9f he7
    hf2) (RS 122 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 10 (bs6 h3f h9e h79 hfe h5f he7) R0 R0 R0
    (RS 26 C)) (DPNode (MkDag 14 (bs6 h3f h9f hcf h2f hbf hcf) R0 R0 R0 (RS 42 C)) (DPNode (MkDag 21 (bs6 h97 hcf
    h3f h9f hcf hff) R0 R0 R0 (RS 74 A)) (DPNode (MkDag 6 (bs6 h73 hff he7 h97 hdf h2f) R0 R0 R0 (RS 134 B))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 h2f h9f h2f h97 h9e he7) R0 R0 R0 (RS 106 C)) (DPNode (MkDag 4
    (bs6 h7f h9e h7f he7 hcb hfc) (RS 170 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs6 h9f hcf
    h2f h73 hff he7) R0 (RS 58 A) R0 R0) (DPNode (MkDag 17 (bs6 h7c hbe he5 hf3 he7 hf3) (RS 90 E) R0 R0 R0)
    (DPNode (MkDag 22 (bs6 hff hfe h5f hcf he7 hfe) R0 R0 R0 (RS 1 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 0
    (bs6 h7c hbe he7 he7 he7 hee) R0 R0 R0 (RS 11 B)) (DPNode (MkDag 3 (bs6 h9f h97 he7 h9f he7 hf2) R0 (RS 7 B) R0
    R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_67_157 : DagPTree :=
  DPNode (MkDag 4 (bs6 hfb h9e h7f he7 hcb hfc) R0 R0 R0 (RS 187 A)) (DPNode (MkDag 9 (bs6 h3c hf2 hfc hff hcf hfc)
    R0 R0 R0 (RS 22 C)) (DPNode (MkDag 13 (bs6 h3f h9f hcf hee h7e h7e) R0 R0 R0 (RS 38 C)) (DPNode (MkDag 17 (bs6
    h97 hcf h3f hbf he7 hf3) R0 R0 R0 (RS 70 A)) (DPNode (MkDag 15 (bs6 h73 hdf hf7 h2f hff h3f) R0 R0 R0 (RS 131
    B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 17 (bs6 h3c hf9 he7 hf3 he7 hf3) R0 R0 R0 (RS 102 C)) (DPNode
    (MkDag 0 (bs6 h9f h9f hcf h3e he7 hee) R0 (RS 166 B) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 15 (bs6
    hf9 hff hcb hff h9f h3f) R0 (RS 54 A) R0 R0) (DPNode (MkDag 0 (bs6 h67 h97 hcf h9e he7 hee) R0 R0 R0 (RS 86 B))
    (DPNode (MkDag 1 (bs6 h7f hff h9f hff hfb h9e) (RS 120 C) R0 R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2
    (bs6 hff h3f hf7 hf9 hf7 h3f) (RS 117 D) R0 R0 (RS 118 A)) (DPNode (MkDag 0 (bs6 h7f h9f hcf h3e he7 hee) R0 R0
    R0 (RS 182 B)) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 11 (bs6 h3f h9e h7e h7e h7f h2f) R0 R0 R0 (RS 30 C))
    (DPNode (MkDag 15 (bs6 h3f h9f hb9 hff h9f h2f) R0 R0 R0 (RS 46 C)) (DPNode (MkDag 5 (bs6 h7f hff hff h2f h97
    he7) R0 R0 R0 (RS 78 B)) (DPNode (MkDag 0 (bs6 hcf h9f hcf h3e he7 hee) R0 R0 R0 (RS 142 A)) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 1 (bs6 h2f h9f hf2 hf9 h7b h9e) R0 R0 R0 (RS 110 C)) (DPNode (MkDag 17 (bs6 hf9 hf9 he7
    hf3 he7 hf3) R0 (RS 2 A) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 17 (bs6 h97 hcf he5 hff he7 hfd) R0
    R0 R0 (RS 62 A)) (DPNode (MkDag 4 (bs6 h3c hfe h7f he7 hcb hfc) R0 R0 R0 (RS 94 C)) (DPNode (MkDag 15 (bs6 hb2
    hff hf7 h2f hff h3f) R0 (RS 158 C) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 22 (bs6 hcf hfe h5f hcf he7
    hfe) R0 R0 R0 (RS 126 A)) DPEmpty DPEmpty))).

Definition dagSub_67_158 : DagPTree :=
  DPNode (MkDag 0 (bs6 hfc hbe he7 he7 he7 hee) (RS 11 D) R0 R0 (RS 7 B)) (DPNode (MkDag 8 (bs6 h3c hbf hfc hfd hcb
    he7) R0 R0 R0 (RS 20 C)) (DPNode (MkDag 13 (bs6 h2f h9f hcf hee h7e h7e) R0 R0 R0 (RS 36 C)) (DPNode (MkDag 20
    (bs6 h97 hcf he5 he7 he5 hee) R0 R0 R0 (RS 68 A)) (DPNode (MkDag 15 (bs6 hf3 hdf hf7 h2f hff h3f) R0 (RS 132 C)
    (RS 133 E) (RS 132 C)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 15 (bs6 hff hf9 h7f h2f hff h3f) R0 R0 R0 (RS
    100 C)) (DPNode (MkDag 0 (bs6 hbb h9f hcf h3e he7 hee) R0 (RS 164 C) R0 R0) DPEmpty DPEmpty) DPEmpty)) (DPNode
    (MkDag 0 (bs6 hcf hcb hff hcb he5 hee) R0 R0 R0 (RS 52 A)) (DPNode (MkDag 0 (bs6 hf3 hcf h97 hcf he7 hee) (RS
    83 D) R0 R0 (RS 84 B)) (DPNode (MkDag 17 (bs6 h79 hf9 he7 hf3 he7 hf3) (RS 5 B) R0 R0 R0) DPEmpty DPEmpty)
    DPEmpty) (DPNode (MkDag 6 (bs6 h3f hf3 hff h97 hdf h2f) R0 R0 R0 (RS 116 A)) (DPNode (MkDag 0 (bs6 hbc hbe he7
    he7 he7 hee) R0 (RS 11 C) R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 11 (bs6 h2f h9e h7e h7e h7f h2f) R0
    R0 R0 (RS 28 C)) (DPNode (MkDag 15 (bs6 h2f h9f hb9 hff h9f h2f) R0 R0 R0 (RS 44 C)) (DPNode (MkDag 6 (bs6 h9e
    h79 he5 hf2 hff h2f) R0 R0 R0 (RS 76 A)) (DPNode (MkDag 3 (bs6 hfb h9e h7f h9f he7 hf2) (RS 139 D) R0 R0 (RS
    180 A)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 5 (bs6 h3f h9f h2f h97 h9e he7) R0 R0 R0 (RS 108 C)) (DPNode
    (MkDag 15 (bs6 h7e h79 h7f h2f hff h3f) R0 R0 R0 (RS 170 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 2 (bs6
    h9f hcb hcf h3d hff h3f) R0 (RS 8 A) R0 R0) (DPNode (MkDag 0 (bs6 he5 hff he5 he7 he7 hee) R0 R0 R0 (RS 92 C))
    (DPNode (MkDag 3 (bs6 hbe h5f h72 hff he7 hf2) R0 R0 (RS 156 E) R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2
    (bs6 h5f hfc hff hf9 hf7 h3f) (RS 15 B) R0 R0 R0) (DPNode (MkDag 4 (bs6 h9f h9e h7f he7 hcb hfc) R0 (RS 188 A)
    R0 R0) DPEmpty DPEmpty) DPEmpty))).

Definition dagSub_67_159 : DagPTree :=
  DPNode (MkDag 2 (bs6 h7f hfc hff hf9 hf7 h3f) (RS 125 D) R0 R0 R0) (DPNode (MkDag 10 (bs6 h2f h9e h79 hfe h5f
    he7) R0 R0 R0 (RS 24 C)) (DPNode (MkDag 14 (bs6 h2f h9f hcf h2f hbf hcf) R0 R0 R0 (RS 40 C)) (DPNode (MkDag 19
    (bs6 h97 hcf h2f h72 hff he7) R0 R0 R0 (RS 72 A)) (DPNode (MkDag 15 (bs6 h73 hff hf7 h2f hff h3f) R0 R0 R0 (RS
    132 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h3c hff hf7 hf9 hf7 h3f) R0 R0 R0 (RS 104 C)) (DPNode
    (MkDag 4 (bs6 h7b h9e h7f he7 hcb hfc) (RS 168 B) R0 R0 (RS 13 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 18
    (bs6 h97 hb9 h7d hcf he7 hfe) R0 (RS 56 A) R0 R0) (DPNode (MkDag 6 (bs6 hbf hff h2f h97 hdf h2f) R0 (RS 88 C)
    R0 R0) (DPNode (MkDag 2 (bs6 h9f hfc hff hf9 hf7 h3f) R0 (RS 152 B) R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode
    (MkDag 1 (bs6 hff hff h9f hff hfb h9e) R0 (RS 10 C) R0 R0) (DPNode (MkDag 4 (bs6 h7b h9f hcf hdc hff h3c) (RS
    184 B) R0 R0 R0) DPEmpty DPEmpty) DPEmpty))) (DPNode (MkDag 12 (bs6 h2f h9f hcf h3e h7f h3f) R0 R0 R0 (RS 32
    C)) (DPNode (MkDag 16 (bs6 h3c hbf h2f hcb he5 hee) R0 R0 R0 (RS 48 B)) (DPNode (MkDag 3 (bs6 hfc hbf hfb h9f
    he7 hf2) R0 R0 (RS 80 E) (RS 81 B)) (DPNode (MkDag 0 (bs6 hfb h9f hcf he7 he7 hee) (RS 143 D) R0 R0 (RS 144 A))
    DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 1 (bs6 h3f h9f hf2 hf9 h7b h9e) R0 R0 R0 (RS 112 C)) (DPNode (MkDag 1
    (bs6 hf3 hff h9f hff hfb h9e) R0 R0 (RS 176 E) (RS 3 B)) DPEmpty DPEmpty) DPEmpty)) (DPNode (MkDag 6 (bs6 h97
    hcf he5 hf3 hdf h2f) R0 R0 R0 (RS 64 A)) (DPNode (MkDag 4 (bs6 hbf hb9 h7f hfc hbf h3c) R0 R0 (RS 96 E) R0)
    (DPNode (MkDag 6 (bs6 h72 hff he7 h97 hdf h2f) R0 R0 R0 (RS 12 B)) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2
    (bs6 hfb hff hff he7 hf7 h3f) (RS 127 D) (RS 128 A) R0 (RS 128 A)) DPEmpty DPEmpty))).

Definition dagTree_67 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hff h9f hcf he7 he7 hee) (RS 0 D) R0 R0 (RS 167 B)) (DPNode (MkDag 1 (bs6 hff hcb hf2
    hf7 hfb h9e) (RS 1 D) R0 (RS 154 E) (RS 155 C)) (DPNode (MkDag 2 (bs6 h9f h3f hf7 hf9 hf7 h3f) R0 R0 R0 (RS 174
    A)) (DPNode (MkDag 4 (bs6 h7f h9f hcf hdc hff h3c) (RS 145 D) R0 R0 (RS 146 B)) dagSub_67_152 dagSub_67_153)
    (DPNode (MkDag 5 (bs6 h9f h97 h9f h2f h97 he7) R0 R0 R0 (RS 175 C)) dagSub_67_154 dagSub_67_155)) (DPNode
    (MkDag 3 (bs6 h7b h97 he7 h9f he7 hf2) (RS 177 B) R0 R0 (RS 178 B)) (DPNode (MkDag 2 (bs6 h5f h3f hf7 hf9 hf7
    h3f) (RS 148 B) R0 R0 R0) dagSub_67_156 dagSub_67_157) (DPNode (MkDag 2 (bs6 h7c hbc hf7 hf9 hf7 h3f) (RS 123
    B) R0 R0 (RS 124 B)) dagSub_67_158 dagSub_67_159))).

Definition dagSub_68_160 : DagPTree :=
  DPNode (MkDag 1 (bs6 hcf h2f h3f hf3 hf3 hcf) R0 R0 R0 (RS 94 C)) (DPNode (MkDag 8 (bs6 hf2 hf9 h79 hfc hbe h5f)
    R0 R0 (RS 17 E) (RS 18 B)) (DPNode (MkDag 3 (bs6 h79 h7b h97 hb9 hfe h79) (RS 33 B) R0 R0 R0) (DPNode (MkDag 6
    (bs6 h5f h3f h73 hcf h2f he7) (RS 66 B) R0 R0 R0) (DPNode (MkDag 6 (bs6 h9f h3f h73 hcf h2f he7) R0 (RS 71 A)
    R0 R0) DPEmpty DPEmpty) DPEmpty) (DPNode (MkDag 2 (bs6 h7d hcf hfd hcf h2f h9f) R0 R0 R0 (RS 97 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 3 (bs6 h3f hcf h3f hb9 hfe h79) R0 R0 R0 (RS 49 B)) (DPNode (MkDag 3 (bs6 hf7 h3f h97
    hb9 hfe h79) R0 (RS 81 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h7f h3f h97 hb9 hfe h79) (RS 13 B) R0
    R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 11 (bs6 hbf h3c hbc hf7 hff hf3) R0 (RS 25 C) R0 R0) (DPNode (MkDag 2
    (bs6 hbf h2f h97 hcf h2f h9f) R0 (RS 2 C) R0 R0) (DPNode (MkDag 5 (bs6 h9e h79 hfe h5f h72 hfe) R0 (RS 15 A) R0
    (RS 15 A)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 h3e h79 hfe h5f h72 hfe) R0 R0 R0 (RS 105 B)) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 h7c hbe h7e h5f h72 hfe) (RS 57 B) R0 R0 R0) (DPNode (MkDag 1 (bs6 h97 hcf hef
    hf3 hf3 hcf) R0 (RS 89 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h7f hf9 hff hb9 hfe h79) (RS 121 D) R0
    R0 R0) DPEmpty DPEmpty))).

Definition dagTree_68 : DagNTree :=
  MkDagNTree (MkDag 0 (bs6 hcf hdc hf3 hcf h2f h97) R0 R0 R0 (RS 30 D)) (DPNode (MkDag 1 (bs6 hf7 h3f hf3 hcb hf3
    hf3) (RS 1 D) R0 R0 (RS 38 C)) (DPNode (MkDag 2 (bs6 hff h2f h97 hcf h2f h9f) (RS 2 D) R0 R0 (RS 41 A)) (DPNode
    (MkDag 3 (bs6 hff hf9 hff hb9 hfe h79) (RS 4 D) R0 R0 (RS 56 B)) dagSub_68_160 (DPNode (MkDag 5 (bs6 hfc hbe
    h7e h5f h72 hfe) (RS 12 D) R0 R0 (RS 123 A)) (DPNode (MkDag 10 (bs6 h9e h7d hf9 h79 hf9 hfc) R0 (RS 21 A) R0
    R0) (DPNode (MkDag 1 (bs6 h7f hf3 hef hf3 hf3 hcf) R0 R0 R0 (RS 35 B)) (DPNode (MkDag 14 (bs6 hbc hbe h7f hfd
    hcf h3f) R0 (RS 69 C) (RS 70 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hcf h3f h73 hcf h2f he7) R0 R0 R0
    (RS 68 C)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 hcf hdf hf3 hcf h2f he7) R0 R0 R0 (RS 53 C)) (DPNode (MkDag
    15 (bs6 h97 hff hff hee h79 h7e) R0 (RS 85 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f hcf hef hf3 hf3
    hcf) R0 R0 R0 (RS 14 B)) DPEmpty DPEmpty))) (DPNode (MkDag 13 (bs6 hcb hdc hbe h79 hf2 hf9) R0 R0 R0 (RS 29 D))
    (DPNode (MkDag 1 (bs6 hff h2f h9f hf3 hf3 hcf) R0 (RS 45 A) R0 R0) (DPNode (MkDag 14 (bs6 h9f hb9 h7b hfd hcf
    h3f) R0 (RS 77 B) R0 (RS 77 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7c hff hf3 hcb hf3 hf3) R0 R0 R0 (RS
    107 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 h7c hf9 hff hb9 hfe h79) R0 R0 R0 (RS 59 B)) (DPNode (MkDag 6
    (bs6 h73 hdf hf3 hcf h2f he7) R0 R0 R0 (RS 91 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h97 hcf hfd hcf h2f
    h9f) R0 R0 R0 (RS 125 A)) DPEmpty DPEmpty))))) (DPNode (MkDag 5 (bs6 h9f h9f hfe h5f h72 hfe) R0 R0 R0 (RS 91
    C)) (DPNode (MkDag 3 (bs6 h5f h3f h97 hb9 hfe h79) (RS 112 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 h7f he7 hb9 h79
    hfe h5f) R0 R0 R0 (RS 19 B)) (DPNode (MkDag 7 (bs6 h79 hfc hf3 hff hf3 hf9) (RS 35 C) R0 R0 R0) (DPNode (MkDag
    6 (bs6 h7f h3f h73 hcf h2f he7) (RS 67 D) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hff h9f h3f hf3 hf3
    hcf) (RS 98 D) R0 (RS 99 E) (RS 100 D)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h7c hfb hfe h5f h72 hfe) (RS 51
    D) R0 R0 R0) (DPNode (MkDag 3 (bs6 hff h3f h97 hb9 hfe h79) R0 (RS 83 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag
    3 (bs6 hfd hcf h3f hb9 hfe h79) R0 R0 (RS 115 E) (RS 14 C)) DPEmpty DPEmpty))) (DPNode (MkDag 12 (bs6 h7c hfc
    hbc hfc hbe h7f) R0 R0 R0 (RS 27 B)) (DPNode (MkDag 1 (bs6 hf7 h2f h9f hf3 hf3 hcf) R0 (RS 43 C) R0 R0) (DPNode
    (MkDag 1 (bs6 h9f hdf hf3 hcb hf3 hf3) R0 (RS 75 A) R0 (RS 75 A)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 h7e
    h7f h72 hff hf3 hf9) (RS 107 C) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 h7f hcb hf3 hcf h2f he7) (RS
    59 C) R0 R0 R0) (DPNode (MkDag 5 (bs6 h97 h9f hfe h5f h72 hfe) R0 (RS 6 A) R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 5 (bs6 hbc hbe h7e h5f h72 hfe) R0 (RS 12 C) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 1 (bs6 hff hcf
    hef hf3 hf3 hcf) R0 R0 (RS 116 E) (RS 117 A)) (DPNode (MkDag 10 (bs6 h9f hcf hf9 h79 hf9 hfc) R0 (RS 23 C) R0
    R0) (DPNode (MkDag 1 (bs6 hbf h3f hf3 hcb hf3 hf3) R0 R0 (RS 39 E) R0) (DPNode (MkDag 14 (bs6 h3c hbe h7f hfd
    hcf h3f) R0 R0 R0 (RS 101 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 hff hcb hff hb9 hfe h79) (RS 102 D) R0 R0
    (RS 103 C)) DPEmpty DPEmpty)) (DPNode (MkDag 14 (bs6 h3c hbe h5f hfd hcf h3f) R0 R0 R0 (RS 55 A)) (DPNode
    (MkDag 3 (bs6 h97 hcf h3f hb9 hfe h79) R0 (RS 87 A) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hff hdf hf3
    hcf h2f he7) (RS 118 D) R0 R0 (RS 119 B)) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 hcb hf9 h7f hf3 hf3 hcf) R0
    R0 R0 (RS 31 B)) (DPNode (MkDag 3 (bs6 h77 hcf h3f hb9 hfe h79) R0 R0 R0 (RS 3 B)) (DPNode (MkDag 2 (bs6 h5f
    h3f h97 hcf h2f h9f) (RS 111 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 4 (bs6 h5f h3f h97 hcf h2f h9e) (RS
    77 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 h5f h3e h7e h5f h72 hfe) (RS 63 B) R0 R0 R0) (DPNode
    (MkDag 5 (bs6 hbf hfe h7e h5f h72 hfe) R0 R0 (RS 95 E) R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h97 h9f h3f
    hf3 hf3 hcf) R0 R0 R0 (RS 127 A)) DPEmpty DPEmpty)))))) (DPNode (MkDag 3 (bs6 hf7 hcf h3f hb9 hfe h79) R0 R0
    (RS 46 E) (RS 47 C)) (DPNode (MkDag 4 (bs6 hff h3f h97 hcf h2f h9e) (RS 5 D) R0 R0 (RS 79 A)) (DPNode (MkDag 6
    (bs6 he7 hcb hf3 hcf h2f he7) R0 R0 R0 (RS 96 B)) (DPNode (MkDag 8 (bs6 h72 hf9 h79 hfc hbe h5f) R0 R0 R0 (RS
    16 B)) (DPNode (MkDag 1 (bs6 h79 hff h9f hf3 hf3 hcf) (RS 34 B) R0 R0 R0) (DPNode (MkDag 5 (bs6 hff h3e h7e h5f
    h72 hfe) (RS 65 D) R0 R0 (RS 128 A)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 hfd hcf hfd hcf h2f h9f) R0 R0 R0
    (RS 98 C)) DPEmpty DPEmpty)) (DPNode (MkDag 1 (bs6 he7 hcf hef hf3 hf3 hcf) R0 R0 R0 (RS 50 B)) (DPNode (MkDag
    3 (bs6 hbf h3f h97 hb9 hfe h79) R0 (RS 82 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f h3f h9f hf3 hf3
    hcf) (RS 114 C) R0 R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 11 (bs6 hff h3c hbc hf7 hff hf3) R0 (RS 26 B) R0
    R0) (DPNode (MkDag 3 (bs6 h9f h2f h97 hb9 hfe h79) R0 (RS 42 C) R0 R0) (DPNode (MkDag 1 (bs6 h97 hdf hf3 hcb
    hf3 hf3) R0 (RS 74 A) R0 (RS 74 A)) DPEmpty DPEmpty) (DPNode (MkDag 7 (bs6 hee h7f h72 hff hf3 hf9) R0 R0 R0
    (RS 106 B)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs6 h5f hcb hf3 hcf h2f he7) (RS 58 B) R0 R0 R0) (DPNode (MkDag
    1 (bs6 h9f hcf hef hf3 hf3 hcf) R0 R0 R0 (RS 90 A)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hdc hbe h7e h5f h72
    hfe) R0 R0 R0 (RS 122 A)) DPEmpty DPEmpty)))) (DPNode (MkDag 1 (bs6 h5f h3f h9f hf3 hf3 hcf) (RS 113 B) R0 R0
    R0) (DPNode (MkDag 10 (bs6 h97 hcf hf9 h79 hf9 hfc) R0 R0 R0 (RS 22 A)) (DPNode (MkDag 7 (bs6 h9f h2f h72 hff
    hf3 hf9) R0 (RS 1 C) R0 R0) (DPNode (MkDag 14 (bs6 hfc hbe h7f hfd hcf h3f) (RS 69 D) R0 R0 (RS 71 A)) DPEmpty
    DPEmpty) (DPNode (MkDag 3 (bs6 hbf hcb hff hb9 hfe h79) R0 (RS 102 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag
    14 (bs6 hbc hbe h5f hfd hcf h3f) R0 R0 (RS 54 E) R0) (DPNode (MkDag 15 (bs6 h9f hff hff hee h79 h7e) R0 R0 R0
    (RS 86 A)) DPEmpty DPEmpty) (DPNode (MkDag 6 (bs6 hbf hdf hf3 hcf h2f he7) R0 (RS 118 C) R0 R0) DPEmpty
    DPEmpty))) (DPNode (MkDag 5 (bs6 hcf hfc hbe h7f h72 hfe) R0 R0 R0 (RS 0 D)) (DPNode (MkDag 7 (bs6 h9f h3c hf3
    hff hf3 hf9) R0 R0 R0 (RS 3 C)) (DPNode (MkDag 4 (bs6 h7f h3f h97 hcf h2f h9e) (RS 78 B) R0 R0 (RS 5 B))
    DPEmpty DPEmpty) (DPNode (MkDag 14 (bs6 h79 hf9 h7b hfd hcf h3f) (RS 110 B) R0 R0 R0) DPEmpty DPEmpty)) (DPNode
    (MkDag 5 (bs6 h79 hf3 hee h5f h72 hfe) (RS 62 B) R0 R0 R0) (DPNode (MkDag 6 (bs6 h73 hff hf3 hcf h2f he7) R0 R0
    R0 (RS 7 B)) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h9f hcf hfd hcf h2f h9f) R0 (RS 126 A) R0 R0) DPEmpty
    DPEmpty))))) (DPNode (MkDag 6 (bs6 hf3 hff hf3 hcf h2f he7) R0 R0 (RS 93 E) (RS 8 D)) (DPNode (MkDag 3 (bs6 h5f
    hf9 hff hb9 hfe h79) (RS 120 B) R0 R0 R0) (DPNode (MkDag 9 (bs6 hff he7 hb9 h79 hfe h5f) R0 R0 R0 (RS 20 A))
    (DPNode (MkDag 1 (bs6 hff hf3 hef hf3 hf3 hcf) R0 R0 (RS 36 E) (RS 37 A)) (DPNode (MkDag 14 (bs6 hdc hbe h7f
    hfd hcf h3f) R0 R0 R0 (RS 68 A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h7f h9f h3f hf3 hf3 hcf) R0 R0 R0 (RS
    98 B)) DPEmpty DPEmpty)) (DPNode (MkDag 5 (bs6 hcf h9f hfe h5f h72 hfe) R0 R0 R0 (RS 52 D)) (DPNode (MkDag 1
    (bs6 h9f h3f h9f hf3 hf3 hcf) R0 R0 R0 (RS 84 A)) DPEmpty DPEmpty) (DPNode (MkDag 3 (bs6 h7d hcf h3f hb9 hfe
    h79) R0 R0 R0 (RS 114 B)) DPEmpty DPEmpty))) (DPNode (MkDag 12 (bs6 hfc hfc hbc hfc hbe h7f) (RS 27 D) R0 R0
    (RS 28 D)) (DPNode (MkDag 1 (bs6 hbf h2f h9f hf3 hf3 hcf) R0 (RS 44 C) R0 R0) (DPNode (MkDag 14 (bs6 h97 hb9
    h7b hfd hcf h3f) R0 (RS 76 A) R0 (RS 76 A)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 hfc hff hf3 hcb hf3 hf3) R0
    R0 (RS 108 E) (RS 109 B)) DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hfc hf9 hff hb9 hfe h79) R0 R0 (RS 60 E) (RS
    61 B)) (DPNode (MkDag 6 (bs6 hf3 hdf hf3 hcf h2f he7) R0 R0 (RS 92 E) (RS 7 C)) DPEmpty DPEmpty) (DPNode (MkDag
    6 (bs6 h9f hcb hf3 hcf h2f he7) R0 (RS 124 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 7 (bs6 h9e h7f h72 hff
    hf3 hf9) R0 (RS 73 A) R0 (RS 73 A)) (DPNode (MkDag 11 (bs6 hf7 h3c hbc hf7 hff hf3) R0 (RS 24 C) R0 R0) (DPNode
    (MkDag 1 (bs6 h3f h3f hf3 hcb hf3 hf3) R0 R0 R0 (RS 40 A)) (DPNode (MkDag 3 (bs6 h9f hcb hff hb9 hfe h79) R0
    (RS 72 A) R0 (RS 72 A)) DPEmpty DPEmpty) (DPNode (MkDag 5 (bs6 hbe h79 hfe h5f h72 hfe) R0 R0 (RS 104 E) R0)
    DPEmpty DPEmpty)) (DPNode (MkDag 3 (bs6 hbf hf9 hff hb9 hfe h79) R0 (RS 4 C) R0 R0) (DPNode (MkDag 3 (bs6 h9f
    hcf h3f hb9 hfe h79) R0 R0 R0 (RS 88 A)) DPEmpty DPEmpty) (DPNode (MkDag 14 (bs6 h7c hbe h5f hfd hcf h3f) (RS
    11 B) R0 R0 R0) DPEmpty DPEmpty))) (DPNode (MkDag 1 (bs6 h79 hfc hf3 hcb hf3 hf3) (RS 32 B) R0 R0 R0) (DPNode
    (MkDag 3 (bs6 hbf hcf h3f hb9 hfe h79) R0 R0 (RS 48 E) R0) (DPNode (MkDag 2 (bs6 h9f h3f h97 hcf h2f h9f) R0
    (RS 80 C) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 2 (bs6 h7f h3f h97 hcf h2f h9f) (RS 10 B) R0 R0 R0) DPEmpty
    DPEmpty)) (DPNode (MkDag 5 (bs6 h7f h3e h7e h5f h72 hfe) (RS 64 B) R0 R0 (RS 65 B)) (DPNode (MkDag 5 (bs6 h3f
    hfe h7e h5f h72 hfe) R0 R0 R0 (RS 9 B)) DPEmpty DPEmpty) (DPNode (MkDag 1 (bs6 h9f h9f h3f hf3 hf3 hcf) R0 (RS
    63 B) R0 R0) DPEmpty DPEmpty))))))).

Definition dagTree_69 : DagNTree :=
  MkDagNTree (MkDag 0 (bs4 he7 h97 hff h97) (RS 0 D) R0 R0 (RS 1 B)) (DPNode (MkDag 1 (bs4 he5 hf3 hcf h9f) (RS 1
    D) R0 R0 (RS 2 B)) (DPNode (MkDag 2 (bs4 he5 hf3 hfb h9f) (RS 2 D) R0 R0 (RS 3 B)) (DPNode (MkDag 4 (bs4 hbd
    hcb hdc hfd) R0 R0 (RS 5 E) R0) (DPNode (MkDag 4 (bs4 hbf hcb hdc hfd) R0 R0 (RS 9 E) R0) (DPNode (MkDag 9 (bs4
    hdf hf2 hf9 hf9) R0 R0 R0 (RS 17 A)) DPEmpty DPEmpty) (DPNode (MkDag 13 (bs4 h7f h3e h5e h7e) R0 R0 R0 (RS 25
    B)) DPEmpty DPEmpty)) (DPNode (MkDag 6 (bs4 hcb hf2 hf9 he7) R0 R0 R0 (RS 13 B)) (DPNode (MkDag 11 (bs4 h7b hfc
    hff hee) (RS 21 B) R0 R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 12 (bs4 hbe h7e h5f h72) R0 R0 (RS 29 E) R0)
    DPEmpty DPEmpty))) (DPNode (MkDag 4 (bs4 haf hcb hdc hfd) R0 R0 (RS 7 E) R0) (DPNode (MkDag 5 (bs4 hb9 h7c hfd
    hcf) R0 (RS 11 C) R0 R0) (DPNode (MkDag 9 (bs4 hff hf2 hf9 hf9) (RS 18 D) R0 R0 (RS 19 D)) DPEmpty DPEmpty)
    (DPNode (MkDag 14 (bs4 h9f h3f hfc hf9) R0 (RS 27 C) R0 R0) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs4 h5f h72 hf9
    hfd) (RS 15 B) R0 R0 R0) (DPNode (MkDag 11 (bs4 h7f hfc hff hee) (RS 23 A) R0 R0 R0) DPEmpty DPEmpty) (DPNode
    (MkDag 15 (bs4 h9f h2f hfc hff) R0 (RS 31 A) R0 R0) DPEmpty DPEmpty)))) (DPNode (MkDag 3 (bs4 he5 hf3 hf3 he5)
    (RS 3 D) R0 R0 (RS 4 C)) (DPNode (MkDag 4 (bs4 h3d hcb hdc hfd) R0 R0 R0 (RS 6 C)) (DPNode (MkDag 4 (bs4 h3f
    hcb hdc hfd) R0 R0 R0 (RS 10 A)) (DPNode (MkDag 9 (bs4 hbf hf2 hf9 hf9) R0 (RS 18 C) R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 13 (bs4 hff h3e h5e h7e) (RS 25 D) R0 R0 (RS 26 A)) DPEmpty DPEmpty)) (DPNode (MkDag 7 (bs4 h79
    hf2 hf9 he7) (RS 14 B) R0 R0 R0) (DPNode (MkDag 11 (bs4 h5f hfc hff hee) (RS 22 B) R0 R0 R0) DPEmpty DPEmpty)
    (DPNode (MkDag 12 (bs4 h3e h7e h5f h72) R0 R0 R0 (RS 30 A)) DPEmpty DPEmpty))) (DPNode (MkDag 4 (bs4 h2f hcb
    hdc hfd) R0 R0 R0 (RS 8 C)) (DPNode (MkDag 5 (bs4 hf9 h7c hfd hcf) (RS 11 D) R0 R0 (RS 12 D)) (DPNode (MkDag 10
    (bs4 hcb hee h7f h9e) R0 R0 R0 (RS 20 B)) DPEmpty DPEmpty) (DPNode (MkDag 12 (bs4 hf3 hee h5f h72) (RS 27 D) R0
    R0 (RS 28 C)) DPEmpty DPEmpty)) (DPNode (MkDag 8 (bs4 h7f h72 hf9 hfd) (RS 16 D) R0 R0 R0) (DPNode (MkDag 12
    (bs4 h9e h7f hff hf2) R0 (RS 24 B) R0 R0) DPEmpty DPEmpty) (DPNode (MkDag 15 (bs4 h97 hf3 hf2 hff) R0 R0 R0 R0)
    DPEmpty DPEmpty))))).

Local Open Scope sym_scope.

Definition dagTree (L : nat) : DagNTree :=
  match L with
  | 0%nat => dagTree_0
  | 1%nat => dagTree_1
  | 2%nat => dagTree_2
  | 3%nat => dagTree_3
  | 4%nat => dagTree_4
  | 5%nat => dagTree_5
  | 6%nat => dagTree_6
  | 7%nat => dagTree_7
  | 8%nat => dagTree_8
  | 9%nat => dagTree_9
  | 10%nat => dagTree_10
  | 11%nat => dagTree_11
  | 12%nat => dagTree_12
  | 13%nat => dagTree_13
  | 14%nat => dagTree_14
  | 15%nat => dagTree_15
  | 16%nat => dagTree_16
  | 17%nat => dagTree_17
  | 18%nat => dagTree_18
  | 19%nat => dagTree_19
  | 20%nat => dagTree_20
  | 21%nat => dagTree_21
  | 22%nat => dagTree_22
  | 23%nat => dagTree_23
  | 24%nat => dagTree_24
  | 25%nat => dagTree_25
  | 26%nat => dagTree_26
  | 27%nat => dagTree_27
  | 28%nat => dagTree_28
  | 29%nat => dagTree_29
  | 30%nat => dagTree_30
  | 31%nat => dagTree_31
  | 32%nat => dagTree_32
  | 33%nat => dagTree_33
  | 34%nat => dagTree_34
  | 35%nat => dagTree_35
  | 36%nat => dagTree_36
  | 37%nat => dagTree_37
  | 38%nat => dagTree_38
  | 39%nat => dagTree_39
  | 40%nat => dagTree_40
  | 41%nat => dagTree_41
  | 42%nat => dagTree_42
  | 43%nat => dagTree_43
  | 44%nat => dagTree_44
  | 45%nat => dagTree_45
  | 46%nat => dagTree_46
  | 47%nat => dagTree_47
  | 48%nat => dagTree_48
  | 49%nat => dagTree_49
  | 50%nat => dagTree_50
  | 51%nat => dagTree_51
  | 52%nat => dagTree_52
  | 53%nat => dagTree_53
  | 54%nat => dagTree_54
  | 55%nat => dagTree_55
  | 56%nat => dagTree_56
  | 57%nat => dagTree_57
  | 58%nat => dagTree_58
  | 59%nat => dagTree_59
  | 60%nat => dagTree_60
  | 61%nat => dagTree_61
  | 62%nat => dagTree_62
  | 63%nat => dagTree_63
  | 64%nat => dagTree_64
  | 65%nat => dagTree_65
  | 66%nat => dagTree_66
  | 67%nat => dagTree_67
  | 68%nat => dagTree_68
  | 69%nat => dagTree_69
  | _ => emptyDagTree
  end.

Definition dagGet (L : nat) (id : N) : DagNode :=
  ntree_get (dagTree L) id.

Definition nbytesOf (L : nat) : nat :=
  match L with
  | 1%nat => 5%nat
  | 2%nat => 5%nat
  | 3%nat => 5%nat
  | 4%nat => 4%nat
  | 6%nat => 6%nat
  | 7%nat => 6%nat
  | 8%nat => 6%nat
  | 9%nat => 6%nat
  | 10%nat => 6%nat
  | 11%nat => 6%nat
  | 12%nat => 6%nat
  | 13%nat => 6%nat
  | 14%nat => 6%nat
  | 15%nat => 6%nat
  | 16%nat => 5%nat
  | 17%nat => 2%nat
  | 19%nat => 5%nat
  | 20%nat => 5%nat
  | 21%nat => 5%nat
  | 22%nat => 5%nat
  | 23%nat => 5%nat
  | 25%nat => 6%nat
  | 27%nat => 5%nat
  | 28%nat => 5%nat
  | 29%nat => 5%nat
  | 30%nat => 2%nat
  | 32%nat => 6%nat
  | 34%nat => 6%nat
  | 35%nat => 6%nat
  | 36%nat => 6%nat
  | 37%nat => 6%nat
  | 38%nat => 6%nat
  | 39%nat => 4%nat
  | 41%nat => 5%nat
  | 42%nat => 5%nat
  | 43%nat => 5%nat
  | 44%nat => 5%nat
  | 45%nat => 5%nat
  | 47%nat => 4%nat
  | 48%nat => 4%nat
  | 50%nat => 5%nat
  | 51%nat => 5%nat
  | 52%nat => 5%nat
  | 53%nat => 5%nat
  | 54%nat => 5%nat
  | 55%nat => 5%nat
  | 56%nat => 5%nat
  | 58%nat => 4%nat
  | 60%nat => 6%nat
  | 61%nat => 5%nat
  | 63%nat => 4%nat
  | 65%nat => 6%nat
  | 66%nat => 6%nat
  | 67%nat => 6%nat
  | 68%nat => 6%nat
  | 69%nat => 4%nat
  | _ => 0%nat
  end.

Definition stageBase (s : nat) : nat :=
  match s with
  | 0%nat => 0%nat
  | 1%nat => 5%nat
  | 2%nat => 18%nat
  | 3%nat => 24%nat
  | 4%nat => 26%nat
  | 5%nat => 31%nat
  | 6%nat => 33%nat
  | 7%nat => 40%nat
  | 8%nat => 46%nat
  | 9%nat => 49%nat
  | 10%nat => 57%nat
  | 11%nat => 59%nat
  | 12%nat => 62%nat
  | 13%nat => 64%nat
  | _ => 0%nat
  end.

Definition stageDepth (s : nat) : nat :=
  match s with
  | 0%nat => 4%nat
  | 1%nat => 12%nat
  | 2%nat => 5%nat
  | 3%nat => 1%nat
  | 4%nat => 4%nat
  | 5%nat => 1%nat
  | 6%nat => 6%nat
  | 7%nat => 5%nat
  | 8%nat => 2%nat
  | 9%nat => 7%nat
  | 10%nat => 1%nat
  | 11%nat => 2%nat
  | 12%nat => 1%nat
  | 13%nat => 5%nat
  | _ => 0%nat
  end.

Definition stageWallCnt (s : nat) : nat :=
  match s with
  | 0%nat => 26%nat
  | 1%nat => 16%nat
  | 2%nat => 14%nat
  | 3%nat => 13%nat
  | 4%nat => 5%nat
  | 5%nat => 14%nat
  | 6%nat => 13%nat
  | 7%nat => 27%nat
  | 8%nat => 15%nat
  | 9%nat => 14%nat
  | 10%nat => 14%nat
  | 11%nat => 13%nat
  | 12%nat => 14%nat
  | 13%nat => 0%nat
  | _ => 0%nat
  end.

Definition stageInitLid (s : nat) : N :=
  match s with
  | 0%nat => 1%N
  | 1%nat => 0%N
  | 2%nat => 0%N
  | 3%nat => 0%N
  | 4%nat => 0%N
  | 5%nat => 0%N
  | 6%nat => 0%N
  | 7%nat => 0%N
  | 8%nat => 0%N
  | 9%nat => 0%N
  | 10%nat => 0%N
  | 11%nat => 0%N
  | 12%nat => 0%N
  | 13%nat => 0%N
  | _ => 0%N
  end.

Definition stageInitQ (s : nat) : Q :=
  match s with
  | 0%nat => B
  | 1%nat => D
  | 2%nat => B
  | 3%nat => A
  | 4%nat => B
  | 5%nat => B
  | 6%nat => D
  | 7%nat => D
  | 8%nat => A
  | 9%nat => B
  | 10%nat => D
  | 11%nat => E
  | 12%nat => B
  | 13%nat => A
  | _ => A
  end.

Definition stageInitBytes (s : nat) : list Byte :=
  match s with
  | 0%nat => [h09; h24; h12]
  | 1%nat => [h4c; h0a; h48; h24]
  | 2%nat => [ha4; h4c; h24; h90; h48]
  | 3%nat => [h10; h00; h02; h29; h41; h02]
  | 4%nat => [h26; h49; h02; h41; h26]
  | 5%nat => [ha6; h04; h09]
  | 6%nat => [h94; h00; h49; h52; h82; h04]
  | 7%nat => [h1c; h20; h41; h02; h24; h48; h48; h09; h12]
  | 8%nat => [h10; h64; h92; h10; h24]
  | 9%nat => [h06; h04; h00; h00; h20; h41; h02]
  | 10%nat => [h50; h26; h48; h48; h09; h12]
  | 11%nat => [h20; h49; h48; h09; h12]
  | 12%nat => []
  | 13%nat => [h10; h64; h90; h90; h04; h90; h00; h32; h01]
  | _ => []
  end.

Definition stagePushIds (s : nat) : list N :=
  match s with
  | 0%nat => [48%N; 19%N; 12%N; 26%N]
  | 1%nat => [55%N; 14%N; 8%N; 29%N; 23%N; 12%N; 13%N; 14%N; 13%N; 14%N; 27%N; 16%N]
  | 2%nat => [56%N; 40%N; 15%N; 7%N; 14%N]
  | 3%nat => [13%N]
  | 4%nat => [3%N; 14%N; 9%N; 5%N]
  | 5%nat => [14%N]
  | 6%nat => [42%N; 12%N; 36%N; 7%N; 14%N; 13%N]
  | 7%nat => [59%N; 24%N; 17%N; 4%N; 27%N]
  | 8%nat => [19%N; 15%N]
  | 9%nat => [0%N; 14%N; 13%N; 9%N; 5%N; 2%N; 14%N]
  | 10%nat => [14%N]
  | 11%nat => [13%N; 0%N]
  | 12%nat => [14%N]
  | 13%nat => [45%N; 23%N; 16%N; 16%N; 0%N]
  | _ => []
  end.

Definition stageBridgeFuel (s : nat) : nat :=
  match s with
  | 0%nat => 247%nat
  | 1%nat => 782%nat
  | 2%nat => 366%nat
  | 3%nat => 210%nat
  | 4%nat => 207%nat
  | 5%nat => 272%nat
  | 6%nat => 1004%nat
  | 7%nat => 550%nat
  | 8%nat => 258%nat
  | 9%nat => 470%nat
  | 10%nat => 183%nat
  | 11%nat => 124%nat
  | 12%nat => 862%nat
  | 13%nat => 350%nat
  | _ => 0%nat
  end.

Definition crysBasePh (id : N) : Phase :=
  match id with
  | 0%N => P0
  | 1%N => P5
  | 2%N => P5
  | 3%N => P7
  | 4%N => P8
  | 5%N => P9
  | 6%N => P9
  | 7%N => P0
  | _ => P0
  end.

Definition crysBaseBits (id : N) : list bool :=
  match id with
  | 0%N => [true; false; true; true; true]
  | 1%N => [false; true; true; true; true]
  | 2%N => [true; true; true; true; true]
  | 3%N => [true; false; false; true; true]
  | 4%N => [true; true; true; true; false]
  | 5%N => [true; false; true; true; true]
  | 6%N => [true; true; true; true; true]
  | 7%N => [true; true; true; true; true]
  | _ => []
  end.

Fixpoint StageNodeTape (basePred : N -> side -> Prop) (baseL : nat)
    (d : nat) (id : N) (sR : side) : Prop :=
  match d with
  | O => basePred id sR
  | S d' =>
    let 'MkDag npar nslice _ _ _ _ := dagGet (baseL + S d')%nat id in
    exists sRp, StageNodeTape basePred baseL d' npar sRp /\
      sR = bytesToRight nslice sRp
  end.

Definition CrysBasePred (id : N) (sR : side) : Prop :=
  exists c : nat, sR = bitsToSide (crysBaseBits id) (crysTape (crysBasePh id) c).

Fixpoint BasePred (s : nat) (id : N) (sR : side) : Prop :=
  match s with
  | O => CrysBasePred id sR
  | S s' =>
    id = 0%N /\
    exists wid : N, (wid < N.of_nat (stageWallCnt s'))%N /\
      StageNodeTape (BasePred s') (stageBase s') (stageDepth s') wid sR
  end.

Definition NodeTape (s d : nat) (id : N) (sR : side) : Prop :=
  StageNodeTape (BasePred s) (stageBase s) d id sR.

Definition RuleSound (s d : nat) : Prop :=
  let L := (stageBase s + d)%nat in
  forall (id : N) (q : Q) (sL sR : side) (idOut : N) (qOut : Q),
    NodeTape s d id sR ->
    getRuleSlot (dagGet L id) q = RS idOut qOut ->
    exists sR', NodeTape s d idOut sR' /\
      (sL {{q}}> sR -->* sL <{{qOut}} sR').

Definition checkCrysBaseSlot (id : N) (q : Q) : bool :=
  match getRuleSlot (ntree_get dagTree_0 id) q with
  | R0 => true
  | RS idOut qOut =>
    match crysBaseBits id with
    | [] => false
    | c0 :: r0 =>
      match simCrysWall 120%nat (crysBasePh id) q [c0] r0 with
      | Some (ph', q', rb') =>
        phaseEqb ph' (crysBasePh idOut) && qEqb q' qOut && boolListEqb rb' (crysBaseBits idOut)
      | None => false
      end
    end
  end.

Definition checkCrysBaseNode (id : N) : bool :=
  checkCrysBaseSlot id A && checkCrysBaseSlot id B &&
  checkCrysBaseSlot id D && checkCrysBaseSlot id F.

Definition checkCrysBase : bool :=
  checkCrysBaseNode 0%N && checkCrysBaseNode 1%N &&
  checkCrysBaseNode 2%N && checkCrysBaseNode 3%N &&
  checkCrysBaseNode 4%N && checkCrysBaseNode 5%N &&
  checkCrysBaseNode 6%N && checkCrysBaseNode 7%N.

Lemma crys_base_valid : checkCrysBase = true.
Proof. vm_check_eq. Qed.

Lemma checkCrysBaseSlot_sound (id : N) (q : Q) (idOut : N) (qOut : Q) (sL sR : side) :
  CrysBasePred id sR ->
  getRuleSlot (ntree_get dagTree_0 id) q = RS idOut qOut ->
  checkCrysBaseSlot id q = true ->
  exists sR', CrysBasePred idOut sR' /\
    (sL {{q}}> sR -->* sL <{{qOut}} sR').
Proof.
  intros [c ->] Hsl Hchk.
  unfold checkCrysBaseSlot in Hchk. rewrite Hsl in Hchk.
  destruct (crysBaseBits id) as [|c0 r0] eqn:Hcb; [discriminate |].
  destruct (simCrysWall 120%nat (crysBasePh id) q [c0] r0)
    as [[[ph' q'] rb'] |] eqn:Hw; [| discriminate].
  apply andb_prop in Hchk as [H1 Hrb].
  apply andb_prop in H1 as [Hph Hq].
  apply phaseEqb_eq in Hph. apply qEqb_eq in Hq. apply boolListEqb_eq in Hrb.
  subst ph' q' rb'.
  destruct (simCrysWall_sound _ _ _ _ _ _ _ _ Hw c sL) as [c' Hrc].
  exists (bitsToSide (crysBaseBits idOut) (crysTape (crysBasePh idOut) c')).
  split; [exists c'; reflexivity |].
  simpl bitsToSide in Hrc |- *. exact Hrc.
Qed.

Lemma checkCrysBaseNode_sound (id : N) (q : Q) (idOut : N) (qOut : Q) (sL sR : side) :
  CrysBasePred id sR ->
  getRuleSlot (ntree_get dagTree_0 id) q = RS idOut qOut ->
  checkCrysBaseNode id = true ->
  exists sR', CrysBasePred idOut sR' /\
    (sL {{q}}> sR -->* sL <{{qOut}} sR').
Proof.
  intros Hnt Hsl Hnode.
  unfold checkCrysBaseNode in Hnode.
  apply andb_prop in Hnode as [H123 Hs5].
  apply andb_prop in H123 as [H12 Hs3].
  apply andb_prop in H12 as [Hs0 Hs1].
  destruct q.
  - exact (checkCrysBaseSlot_sound id A idOut qOut sL sR Hnt Hsl Hs0).
  - exact (checkCrysBaseSlot_sound id B idOut qOut sL sR Hnt Hsl Hs1).
  - destruct (ntree_get dagTree_0 id); simpl in Hsl; discriminate.
  - exact (checkCrysBaseSlot_sound id D idOut qOut sL sR Hnt Hsl Hs3).
  - destruct (ntree_get dagTree_0 id); simpl in Hsl; discriminate.
  - exact (checkCrysBaseSlot_sound id F idOut qOut sL sR Hnt Hsl Hs5).
Qed.

Lemma ruleSound_stage0_base : RuleSound 0%nat 0%nat.
Proof.
  intros id q sL sR idOut qOut Hnt Hsl.
  unfold dagGet in Hsl; simpl dagTree in Hsl.
  pose proof crys_base_valid as Hv. unfold checkCrysBase in Hv.
  repeat (apply andb_prop in Hv as [Hv ?]).
  destruct id as [| [ [ [p|p|] | [p|p|] |] | [ [p|p|] | [p|p|] |] | ] ];
    try (simpl in Hsl; destruct q; discriminate);
    eapply checkCrysBaseNode_sound; eauto.
Qed.

Arguments dagTree : simpl never.
Arguments dagGet : simpl never.

Fixpoint checkRuleLoop (tbl : B8Table) (sliceFuel : nat) (pTree : DagNTree)
    (tgtP : N) (tgtSlice : list Byte) (tgtQ : Q)
    (fuel : nat) (curP : N) (side_b : bool) (q : Q)
    (rb : list Byte) (cb : Byte) (lb : list Byte) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match simSliceBytes tbl sliceFuel side_b q rb cb lb with
    | SliceTail qOut outSlice =>
      qEqb qOut tgtQ && N.eqb curP tgtP && sliceEqb outSlice tgtSlice
    | SliceWall qOut outB l' =>
      match getRuleSlot (ntree_get pTree curP) qOut with
      | R0 => false
      | RS nextP nextQ =>
        checkRuleLoop tbl sliceFuel pTree tgtP tgtSlice tgtQ fuel' nextP false nextQ [] outB l'
      end
    | _ => false
    end
  end.

Lemma checkRuleLoop_sound sliceFuel s d :
  RuleSound s d ->
  forall tgtP tgtSlice tgtQ fuel curP side_b q rb cb lb (sL sRp : side),
    NodeTape s d curP sRp ->
    checkRuleLoop theB8Table sliceFuel (dagTree (stageBase s + d)%nat)
      tgtP tgtSlice tgtQ fuel curP side_b q rb cb lb = true ->
    exists sRp', NodeTape s d tgtP sRp' /\
      (byteEntryCfg side_b q cb (bytesToLeft lb sL) (bytesToRight rb sRp) -->*
       sL <{{tgtQ}} bytesToRight tgtSlice sRp').
Proof.
  intros HRS tgtP tgtSlice tgtQ fuel.
  induction fuel as [|fuel IH]; intros curP side_b q rb cb lb sL sRp Hnt Hchk;
    cbn [checkRuleLoop] in Hchk; [discriminate |].
  pose proof (simSliceBytes_sound sliceFuel side_b q rb cb lb sL sRp) as Hsim.
  destruct (simSliceBytes theB8Table sliceFuel side_b q rb cb lb)
    as [qOut outB l' | qOut outSlice | |]; try discriminate.
  - fold (dagGet (stageBase s + d)%nat curP) in Hchk.
    destruct (getRuleSlot (dagGet (stageBase s + d)%nat curP) qOut)
      as [|nextP nextQ] eqn:Hsl; [discriminate |].
    destruct (HRS curP qOut (bytesToLeft (outB :: l') sL) sRp nextP nextQ Hnt Hsl)
      as [sRp1 [Hnt1 Hwall]].
    destruct (IH nextP false nextQ [] outB l' sL sRp1 Hnt1 Hchk)
      as [sRp' [Hnt' Hrest]].
    exists sRp'. split; [exact Hnt' |].
    exact (ev_trans _ _ _ Hsim (ev_trans _ _ _ Hwall Hrest)).
  - apply andb_prop in Hchk as [H1 Hs].
    apply andb_prop in H1 as [Hq Hp].
    apply qEqb_eq in Hq. apply N.eqb_eq in Hp. apply sliceEqb_eq in Hs.
    subst qOut curP outSlice.
    exists sRp. split; [exact Hnt | exact Hsim].
Qed.
Arguments checkRuleLoop : simpl never.

Definition checkSlot (tbl : B8Table) (sliceFuel loopFuel : nat) (pTree cTree : DagNTree)
    (srcP : N) (srcSlice : list Byte) (qin : Q) (sl : RuleSlot) : bool :=
  match sl with
  | R0 => true
  | RS idOut qOut =>
    match srcSlice with
    | [] => false
    | cb0 :: rb0 =>
      let 'MkDag tgtP tgtSlice _ _ _ _ := ntree_get cTree idOut in
      checkRuleLoop tbl sliceFuel pTree tgtP tgtSlice qOut loopFuel srcP true qin rb0 cb0 []
    end
  end.

Definition checkDagNode (tbl : B8Table) (sliceFuel loopFuel : nat) (pTree cTree : DagNTree)
    (dn : DagNode) : bool :=
  let 'MkDag srcP srcSlice s0 s1 s3 s5 := dn in
  checkSlot tbl sliceFuel loopFuel pTree cTree srcP srcSlice A s0 &&
  checkSlot tbl sliceFuel loopFuel pTree cTree srcP srcSlice B s1 &&
  checkSlot tbl sliceFuel loopFuel pTree cTree srcP srcSlice D s3 &&
  checkSlot tbl sliceFuel loopFuel pTree cTree srcP srcSlice F s5.

Lemma checkSlot_sound sliceFuel loopFuel s d :
  RuleSound s d ->
  forall id qin idOut qOut srcP srcSlice s0 s1 s3 s5 (sL sR : side),
    dagGet (stageBase s + S d)%nat id = MkDag srcP srcSlice s0 s1 s3 s5 ->
    NodeTape s (S d) id sR ->
    checkSlot theB8Table sliceFuel loopFuel
      (dagTree (stageBase s + d)%nat) (dagTree (stageBase s + S d)%nat)
      srcP srcSlice qin (RS idOut qOut) = true ->
    exists sR', NodeTape s (S d) idOut sR' /\ (sL {{qin}}> sR -->* sL <{{qOut}} sR').
Proof.
  intros HRS id qin idOut qOut srcP srcSlice s0 s1 s3 s5 sL sR Hget Hnt Hslot.
  unfold NodeTape in Hnt; cbn [StageNodeTape] in Hnt. rewrite Hget in Hnt.
  destruct Hnt as [sRp [HntP ->]].
  cbn [checkSlot] in Hslot.
  destruct srcSlice as [|cb0 rb0]; [discriminate |].
  fold (dagGet (stageBase s + S d)%nat idOut) in Hslot.
  destruct (dagGet (stageBase s + S d)%nat idOut) as [tgtP tgtSlice t0 t1 t3 t5] eqn:Htgt.
  destruct (checkRuleLoop_sound sliceFuel s d HRS tgtP tgtSlice qOut loopFuel
              srcP true qin rb0 cb0 [] sL sRp HntP Hslot) as [sRp' [HntP' Hrc]].
  exists (bytesToRight tgtSlice sRp').
  split.
  - unfold NodeTape; cbn [StageNodeTape]. rewrite Htgt.
    exists sRp'. split; [exact HntP' | reflexivity].
  - exact Hrc.
Qed.

Definition checkLayerTrees (tbl : B8Table) (sliceFuel loopFuel : nat)
    (pTree cTree : DagNTree) : bool :=
  ntree_forall (checkDagNode tbl sliceFuel loopFuel pTree cTree) cTree.

Definition checkLayerAt (tbl : B8Table) (sliceFuel loopFuel s d : nat) : bool :=
  checkLayerTrees tbl sliceFuel loopFuel
    (dagTree (stageBase s + d)%nat) (dagTree (stageBase s + S d)%nat).

Lemma checkLayer_sound sliceFuel loopFuel s d :
  RuleSound s d ->
  checkLayerAt theB8Table sliceFuel loopFuel s d = true ->
  RuleSound s (S d).
Proof.
  intros HRS Htree id q sL sR idOut qOut Hnt Hsl.
  unfold checkLayerAt, checkLayerTrees in Htree.
  assert (Hnode : checkDagNode theB8Table sliceFuel loopFuel
                    (dagTree (stageBase s + d)%nat) (dagTree (stageBase s + S d)%nat)
                    (dagGet (stageBase s + S d)%nat id) = true).
  { unfold dagGet.
     exact (ntree_forall_sound
       (checkDagNode theB8Table sliceFuel loopFuel
         (dagTree (stageBase s + d)%nat) (dagTree (stageBase s + S d)%nat))
       (dagTree (stageBase s + S d)%nat) eq_refl Htree id). }
  destruct (dagGet (stageBase s + S d)%nat id) as [srcP srcSlice s0 s1 s3 s5] eqn:Hget.
  cbn [checkDagNode] in Hnode.
  apply andb_prop in Hnode as [H123 Hs5].
  apply andb_prop in H123 as [H12 Hs3].
  apply andb_prop in H12 as [Hs0 Hs1].
  cbn [getRuleSlot] in Hsl.
  destruct q; try discriminate.
  - subst s0. exact (checkSlot_sound sliceFuel loopFuel s d HRS id A idOut qOut _ _ _ _ _ _ _ _ Hget Hnt Hs0).
  - subst s1. exact (checkSlot_sound sliceFuel loopFuel s d HRS id B idOut qOut _ _ _ _ _ _ _ _ Hget Hnt Hs1).
  - subst s3. exact (checkSlot_sound sliceFuel loopFuel s d HRS id D idOut qOut _ _ _ _ _ _ _ _ Hget Hnt Hs3).
  - subst s5. exact (checkSlot_sound sliceFuel loopFuel s d HRS id F idOut qOut _ _ _ _ _ _ _ _ Hget Hnt Hs5).
Qed.

(* Wall Closure across Stages 0..12 *)

Definition checkWallSlot (topTree : DagNTree) (wcN wid : N) (q : Q) (bsl : RuleSlot) : bool :=
  match bsl with
  | R0 => true
  | RS bid bq =>
    N.eqb bid 0%N &&
    match getRuleSlot (ntree_get topTree wid) q with
    | R0 => false
    | RS tid tq => N.ltb tid wcN && qEqb tq bq
    end
  end.

Definition checkWallNode (topTree baseTree : DagNTree) (wcN wid : N) : bool :=
  let 'MkDag _ _ w0 w1 w3 w5 := ntree_get baseTree 0%N in
  checkWallSlot topTree wcN wid A w0 &&
  checkWallSlot topTree wcN wid B w1 &&
  checkWallSlot topTree wcN wid D w3 &&
  checkWallSlot topTree wcN wid F w5.

Fixpoint checkWallLoop (topTree baseTree : DagNTree) (wcN : N) (lo cnt : nat) : bool :=
  match cnt with
  | O => true
  | S cnt' =>
    checkWallNode topTree baseTree wcN (N.of_nat lo) &&
    checkWallLoop topTree baseTree wcN (S lo) cnt'
  end.

Definition checkStageWall (s : nat) : bool :=
  let topL := (stageBase s + stageDepth s)%nat in
  let nextBaseL := stageBase (S s) in
  let wc := stageWallCnt s in
  Nat.leb 1%nat wc &&
  checkWallLoop (dagTree topL) (dagTree nextBaseL) (N.of_nat wc) 0%nat wc.

Definition checkAllWalls : bool :=
  checkStageWall 0%nat && checkStageWall 1%nat && checkStageWall 2%nat && checkStageWall 3%nat &&
  checkStageWall 4%nat && checkStageWall 5%nat && checkStageWall 6%nat && checkStageWall 7%nat &&
  checkStageWall 8%nat && checkStageWall 9%nat && checkStageWall 10%nat && checkStageWall 11%nat &&
  checkStageWall 12%nat.

Lemma all_walls_valid : checkAllWalls = true.
Proof. vm_check_eq. Qed.

Lemma checkStageWall_of_all (s : nat) : (s < 13)%nat -> checkStageWall s = true.
Proof.
  intros Hs.
  pose proof all_walls_valid as Hv. unfold checkAllWalls in Hv.
  repeat (apply andb_prop in Hv as [Hv ?]).
  do 13 (destruct s as [|s]; [assumption |]).
  lia.
Qed.

Lemma checkWallLoop_sound topTree baseTree wcN lo cnt :
  checkWallLoop topTree baseTree wcN lo cnt = true ->
  forall i : nat, (lo <= i)%nat -> (i < lo + cnt)%nat ->
    checkWallNode topTree baseTree wcN (N.of_nat i) = true.
Proof.
  revert lo. induction cnt as [|cnt IH]; intros lo Hchk i Hlo Hhi; [lia |].
  simpl in Hchk. apply andb_prop in Hchk as [Hcur Hrest].
  destruct (PeanoNat.Nat.eq_dec i lo) as [-> | Hneq].
  - exact Hcur.
  - apply (IH (S lo) Hrest i); lia.
Qed.

Lemma checkWallSlot_sound topTree wcN wid q idOutBase qOutBase :
  checkWallSlot topTree wcN wid q (RS idOutBase qOutBase) = true ->
  idOutBase = 0%N /\
  exists tid : N, (tid < wcN)%N /\
    getRuleSlot (ntree_get topTree wid) q = RS tid qOutBase.
Proof.
  intros H. simpl in H.
  apply andb_prop in H as [Hbid Htop].
  apply N.eqb_eq in Hbid.
  destruct (getRuleSlot (ntree_get topTree wid) q) as [|tid tq] eqn:Hsl; [discriminate |].
  apply andb_prop in Htop as [Hlt Hq].
  apply N.ltb_lt in Hlt. apply qEqb_eq in Hq. subst tq.
  split; [exact Hbid | exists tid; split; [exact Hlt | reflexivity]].
Qed.

Lemma wallClosure_sound (s : nat) :
  (s < 13)%nat ->
  RuleSound s (stageDepth s) ->
  checkStageWall s = true ->
  RuleSound (S s) 0%nat.
Proof.
  intros _ Htop Hchk id q sL sR idOut qOut Hnt Hsl.
  unfold NodeTape in Hnt; cbn [StageNodeTape BasePred] in Hnt.
  destruct Hnt as [Hid [wid [HwidLt HwidTape]]]. subst id.
  unfold checkStageWall in Hchk.
  apply andb_prop in Hchk as [_ Hloop].
  assert (Hi : (N.to_nat wid < stageWallCnt s)%nat) by lia.
  pose proof (checkWallLoop_sound
    (dagTree (stageBase s + stageDepth s)%nat) (dagTree (stageBase (S s)))
    (N.of_nat (stageWallCnt s)) 0%nat (stageWallCnt s) Hloop
    (N.to_nat wid) (PeanoNat.Nat.le_0_l _) Hi) as Hwn.
  rewrite N2Nat.id in Hwn.
  rewrite Nat.add_0_r in Hsl. unfold dagGet in Hsl.
  unfold checkWallNode in Hwn.
  destruct (ntree_get (dagTree (stageBase (S s))) 0%N) as [bp bs w0 w1 w3 w5].
  apply andb_prop in Hwn as [H123 Hw5].
  apply andb_prop in H123 as [H12 Hw3].
  apply andb_prop in H12 as [Hw0 Hw1].
  assert (Hws : checkWallSlot (dagTree (stageBase s + stageDepth s)%nat)
                  (N.of_nat (stageWallCnt s)) wid q (RS idOut qOut) = true).
  { simpl in Hsl. destruct q; try discriminate; subst; assumption. }
  destruct (checkWallSlot_sound _ _ _ _ _ _ Hws) as [-> [tid [HtidLt HtopSl]]].
  fold (dagGet (stageBase s + stageDepth s)%nat wid) in HtopSl.
  destruct (Htop wid q sL sR tid qOut HwidTape HtopSl) as [sR' [Hnt' Hrc]].
  exists sR'. split; [| exact Hrc].
  unfold NodeTape; simpl.
  split; [reflexivity | exists tid; split; [exact HtidLt | exact Hnt']].
Qed.

Lemma layer_valid_1 : checkLayerAt theB8Table 160%nat 360%nat 0%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_2 : checkLayerAt theB8Table 160%nat 360%nat 0%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_3 : checkLayerAt theB8Table 160%nat 360%nat 0%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_4 : checkLayerAt theB8Table 160%nat 360%nat 0%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_6 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_7 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_8 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_9 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_10 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_11 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 5%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_12 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 6%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_13 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 7%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_14 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 8%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_15 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 9%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_16 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 10%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_17 : checkLayerAt theB8Table 160%nat 360%nat 1%nat 11%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_19 : checkLayerAt theB8Table 160%nat 360%nat 2%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_20 : checkLayerAt theB8Table 160%nat 360%nat 2%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_21 : checkLayerAt theB8Table 160%nat 360%nat 2%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_22 : checkLayerAt theB8Table 160%nat 360%nat 2%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_23 : checkLayerAt theB8Table 160%nat 360%nat 2%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_25 : checkLayerAt theB8Table 160%nat 360%nat 3%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_27 : checkLayerAt theB8Table 160%nat 360%nat 4%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_28 : checkLayerAt theB8Table 160%nat 360%nat 4%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_29 : checkLayerAt theB8Table 160%nat 360%nat 4%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_30 : checkLayerAt theB8Table 160%nat 360%nat 4%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_32 : checkLayerAt theB8Table 160%nat 360%nat 5%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_34 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_35 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_36 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_37 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_38 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_39 : checkLayerAt theB8Table 160%nat 360%nat 6%nat 5%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_41 : checkLayerAt theB8Table 160%nat 360%nat 7%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_42 : checkLayerAt theB8Table 160%nat 360%nat 7%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_43 : checkLayerAt theB8Table 160%nat 360%nat 7%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_44 : checkLayerAt theB8Table 160%nat 360%nat 7%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_45 : checkLayerAt theB8Table 160%nat 360%nat 7%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_47 : checkLayerAt theB8Table 160%nat 360%nat 8%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_48 : checkLayerAt theB8Table 160%nat 360%nat 8%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_50 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_51 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_52 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_53 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_54 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_55 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 5%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_56 : checkLayerAt theB8Table 160%nat 360%nat 9%nat 6%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_58 : checkLayerAt theB8Table 160%nat 360%nat 10%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_60 : checkLayerAt theB8Table 160%nat 360%nat 11%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_61 : checkLayerAt theB8Table 160%nat 360%nat 11%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_63 : checkLayerAt theB8Table 160%nat 360%nat 12%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_65 : checkLayerAt theB8Table 160%nat 360%nat 13%nat 0%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_66 : checkLayerAt theB8Table 160%nat 360%nat 13%nat 1%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_67 : checkLayerAt theB8Table 160%nat 360%nat 13%nat 2%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_68 : checkLayerAt theB8Table 160%nat 360%nat 13%nat 3%nat = true.
Proof. vm_check_eq. Qed.

Lemma layer_valid_69 : checkLayerAt theB8Table 160%nat 360%nat 13%nat 4%nat = true.
Proof. vm_check_eq. Qed.

Lemma ruleSound_stage0 (d : nat) : (d <= 4)%nat -> RuleSound 0%nat d.
Proof.
  intros Hd.
  pose proof ruleSound_stage0_base as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 0%nat 0%nat Hr0 layer_valid_1) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 0%nat 1%nat Hr1 layer_valid_2) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 0%nat 2%nat Hr2 layer_valid_3) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 0%nat 3%nat Hr3 layer_valid_4) as Hr4.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  lia.
Qed.

Lemma ruleSound_stage1 (d : nat) : (d <= 12)%nat -> RuleSound 1%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 0%nat ltac:(lia) (ruleSound_stage0 4%nat ltac:(lia)) (checkStageWall_of_all 0%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 0%nat Hr0 layer_valid_6) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 1%nat Hr1 layer_valid_7) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 2%nat Hr2 layer_valid_8) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 3%nat Hr3 layer_valid_9) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 4%nat Hr4 layer_valid_10) as Hr5.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 5%nat Hr5 layer_valid_11) as Hr6.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 6%nat Hr6 layer_valid_12) as Hr7.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 7%nat Hr7 layer_valid_13) as Hr8.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 8%nat Hr8 layer_valid_14) as Hr9.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 9%nat Hr9 layer_valid_15) as Hr10.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 10%nat Hr10 layer_valid_16) as Hr11.
  pose proof (checkLayer_sound 160%nat 360%nat 1%nat 11%nat Hr11 layer_valid_17) as Hr12.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  destruct d as [|d]; [exact Hr6 |].
  destruct d as [|d]; [exact Hr7 |].
  destruct d as [|d]; [exact Hr8 |].
  destruct d as [|d]; [exact Hr9 |].
  destruct d as [|d]; [exact Hr10 |].
  destruct d as [|d]; [exact Hr11 |].
  destruct d as [|d]; [exact Hr12 |].
  lia.
Qed.

Lemma ruleSound_stage2 (d : nat) : (d <= 5)%nat -> RuleSound 2%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 1%nat ltac:(lia) (ruleSound_stage1 12%nat ltac:(lia)) (checkStageWall_of_all 1%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 2%nat 0%nat Hr0 layer_valid_19) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 2%nat 1%nat Hr1 layer_valid_20) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 2%nat 2%nat Hr2 layer_valid_21) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 2%nat 3%nat Hr3 layer_valid_22) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 2%nat 4%nat Hr4 layer_valid_23) as Hr5.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  lia.
Qed.

Lemma ruleSound_stage3 (d : nat) : (d <= 1)%nat -> RuleSound 3%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 2%nat ltac:(lia) (ruleSound_stage2 5%nat ltac:(lia)) (checkStageWall_of_all 2%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 3%nat 0%nat Hr0 layer_valid_25) as Hr1.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  lia.
Qed.

Lemma ruleSound_stage4 (d : nat) : (d <= 4)%nat -> RuleSound 4%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 3%nat ltac:(lia) (ruleSound_stage3 1%nat ltac:(lia)) (checkStageWall_of_all 3%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 4%nat 0%nat Hr0 layer_valid_27) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 4%nat 1%nat Hr1 layer_valid_28) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 4%nat 2%nat Hr2 layer_valid_29) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 4%nat 3%nat Hr3 layer_valid_30) as Hr4.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  lia.
Qed.

Lemma ruleSound_stage5 (d : nat) : (d <= 1)%nat -> RuleSound 5%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 4%nat ltac:(lia) (ruleSound_stage4 4%nat ltac:(lia)) (checkStageWall_of_all 4%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 5%nat 0%nat Hr0 layer_valid_32) as Hr1.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  lia.
Qed.

Lemma ruleSound_stage6 (d : nat) : (d <= 6)%nat -> RuleSound 6%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 5%nat ltac:(lia) (ruleSound_stage5 1%nat ltac:(lia)) (checkStageWall_of_all 5%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 0%nat Hr0 layer_valid_34) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 1%nat Hr1 layer_valid_35) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 2%nat Hr2 layer_valid_36) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 3%nat Hr3 layer_valid_37) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 4%nat Hr4 layer_valid_38) as Hr5.
  pose proof (checkLayer_sound 160%nat 360%nat 6%nat 5%nat Hr5 layer_valid_39) as Hr6.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  destruct d as [|d]; [exact Hr6 |].
  lia.
Qed.

Lemma ruleSound_stage7 (d : nat) : (d <= 5)%nat -> RuleSound 7%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 6%nat ltac:(lia) (ruleSound_stage6 6%nat ltac:(lia)) (checkStageWall_of_all 6%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 7%nat 0%nat Hr0 layer_valid_41) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 7%nat 1%nat Hr1 layer_valid_42) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 7%nat 2%nat Hr2 layer_valid_43) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 7%nat 3%nat Hr3 layer_valid_44) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 7%nat 4%nat Hr4 layer_valid_45) as Hr5.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  lia.
Qed.

Lemma ruleSound_stage8 (d : nat) : (d <= 2)%nat -> RuleSound 8%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 7%nat ltac:(lia) (ruleSound_stage7 5%nat ltac:(lia)) (checkStageWall_of_all 7%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 8%nat 0%nat Hr0 layer_valid_47) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 8%nat 1%nat Hr1 layer_valid_48) as Hr2.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  lia.
Qed.

Lemma ruleSound_stage9 (d : nat) : (d <= 7)%nat -> RuleSound 9%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 8%nat ltac:(lia) (ruleSound_stage8 2%nat ltac:(lia)) (checkStageWall_of_all 8%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 0%nat Hr0 layer_valid_50) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 1%nat Hr1 layer_valid_51) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 2%nat Hr2 layer_valid_52) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 3%nat Hr3 layer_valid_53) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 4%nat Hr4 layer_valid_54) as Hr5.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 5%nat Hr5 layer_valid_55) as Hr6.
  pose proof (checkLayer_sound 160%nat 360%nat 9%nat 6%nat Hr6 layer_valid_56) as Hr7.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  destruct d as [|d]; [exact Hr6 |].
  destruct d as [|d]; [exact Hr7 |].
  lia.
Qed.

Lemma ruleSound_stage10 (d : nat) : (d <= 1)%nat -> RuleSound 10%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 9%nat ltac:(lia) (ruleSound_stage9 7%nat ltac:(lia)) (checkStageWall_of_all 9%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 10%nat 0%nat Hr0 layer_valid_58) as Hr1.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  lia.
Qed.

Lemma ruleSound_stage11 (d : nat) : (d <= 2)%nat -> RuleSound 11%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 10%nat ltac:(lia) (ruleSound_stage10 1%nat ltac:(lia)) (checkStageWall_of_all 10%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 11%nat 0%nat Hr0 layer_valid_60) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 11%nat 1%nat Hr1 layer_valid_61) as Hr2.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  lia.
Qed.

Lemma ruleSound_stage12 (d : nat) : (d <= 1)%nat -> RuleSound 12%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 11%nat ltac:(lia) (ruleSound_stage11 2%nat ltac:(lia)) (checkStageWall_of_all 11%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 12%nat 0%nat Hr0 layer_valid_63) as Hr1.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  lia.
Qed.

Lemma ruleSound_stage13 (d : nat) : (d <= 5)%nat -> RuleSound 13%nat d.
Proof.
  intros Hd.
  pose proof (wallClosure_sound 12%nat ltac:(lia) (ruleSound_stage12 1%nat ltac:(lia)) (checkStageWall_of_all 12%nat ltac:(lia))) as Hr0.
  pose proof (checkLayer_sound 160%nat 360%nat 13%nat 0%nat Hr0 layer_valid_65) as Hr1.
  pose proof (checkLayer_sound 160%nat 360%nat 13%nat 1%nat Hr1 layer_valid_66) as Hr2.
  pose proof (checkLayer_sound 160%nat 360%nat 13%nat 2%nat Hr2 layer_valid_67) as Hr3.
  pose proof (checkLayer_sound 160%nat 360%nat 13%nat 3%nat Hr3 layer_valid_68) as Hr4.
  pose proof (checkLayer_sound 160%nat 360%nat 13%nat 4%nat Hr4 layer_valid_69) as Hr5.
  destruct d as [|d]; [exact Hr0 |].
  destruct d as [|d]; [exact Hr1 |].
  destruct d as [|d]; [exact Hr2 |].
  destruct d as [|d]; [exact Hr3 |].
  destruct d as [|d]; [exact Hr4 |].
  destruct d as [|d]; [exact Hr5 |].
  lia.
Qed.

Lemma ruleSound_all (s d : nat) :
  (s <= 13)%nat -> (d <= stageDepth s)%nat -> RuleSound s d.
Proof.
  intros Hs Hd.
  destruct s as [|s]; [exact (ruleSound_stage0 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage1 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage2 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage3 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage4 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage5 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage6 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage7 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage8 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage9 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage10 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage11 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage12 d Hd) |].
  destruct s as [|s]; [exact (ruleSound_stage13 d Hd) |].
  lia.
Qed.

(* ========================================================================== *)
(* Section 7: Unified Stage Bridge & Final Halt Soundness                     *)
(* ========================================================================== *)

Fixpoint simTailBridge (tbl : B8Table) (topTree : DagNTree)
    (tgtLid : N) (tgtQ : Q) (tgtBytes : list Byte)
    (fuel : nat) (lid : N) (side_b : bool) (q : Q)
    (rb : list Byte) (cb : Byte) (lb : list Byte) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    let hit :=
      match rb, side_b with
      | [], false => N.eqb lid tgtLid && qEqb q tgtQ && bytesEqZeroPad (cb :: lb) tgtBytes
      | _, _ => false
      end in
    if hit then true
    else
      match b8EntryT tbl side_b q cb with
      | B8Wall qOut outB =>
        match rb with
        | [] =>
          match getRuleSlot (ntree_get topTree lid) qOut with
          | R0 => false
          | RS nextId nextQ =>
            simTailBridge tbl topTree tgtLid tgtQ tgtBytes fuel' nextId false nextQ [] outB lb
          end
        | pb :: r' =>
          simTailBridge tbl topTree tgtLid tgtQ tgtBytes fuel' lid true qOut r' pb (outB :: lb)
        end
      | B8Tail qOut outB =>
        let '(nb, l') := popByte lb in
        simTailBridge tbl topTree tgtLid tgtQ tgtBytes fuel' lid false qOut (outB :: rb) nb l'
      | _ => false
      end
  end.

Lemma simTailBridge_sound s :
  RuleSound s (stageDepth s) ->
  forall tgtLid tgtQ tgtBytes fuel lid side_b q rb cb lb (sR : side),
    NodeTape s (stageDepth s) lid sR ->
    simTailBridge theB8Table (dagTree (stageBase s + stageDepth s)%nat)
      tgtLid tgtQ tgtBytes fuel lid side_b q rb cb lb = true ->
    exists sR', NodeTape s (stageDepth s) tgtLid sR' /\
      (byteEntryCfg side_b q cb (bytesToLeft lb 0inf) (bytesToRight rb sR) -->*
       bytesToLeft tgtBytes 0inf <{{tgtQ}} sR').
Proof.
  intros Htop tgtLid tgtQ tgtBytes fuel.
  induction fuel as [|fuel IH]; intros lid side_b q rb cb lb sR Hnt Hchk;
    cbn [simTailBridge] in Hchk; [discriminate |].
  destruct (match rb, side_b with
            | [], false => N.eqb lid tgtLid && qEqb q tgtQ && bytesEqZeroPad (cb :: lb) tgtBytes
            | _, _ => false
            end) eqn:Hhit.
  - destruct rb as [|? ?]; [| discriminate].
    destruct side_b; [discriminate |].
    apply andb_prop in Hhit as [H1 Hbytes].
    apply andb_prop in H1 as [Hlid Hq].
    apply N.eqb_eq in Hlid. apply qEqb_eq in Hq.
    pose proof (bytesEqZeroPad_sound (cb :: lb) tgtBytes Hbytes) as HeqB.
    subst lid q.
    exists sR. split; [exact Hnt |].
    unfold byteEntryCfg; simpl bytesToRight.
    change (byteBitsToSide cb (bytesToLeft lb 0inf)) with (bytesToLeft (cb :: lb) 0inf).
    rewrite HeqB. apply evstep_refl.
  - pose proof (b8Entry_sound side_b q cb (bytesToLeft lb 0inf) (bytesToRight rb sR)) as Hb8.
    destruct (b8EntryT theB8Table side_b q cb) as [qOut outB | qOut outB | |]; try discriminate.
    + destruct rb as [|pb r'].
      * fold (dagGet (stageBase s + stageDepth s)%nat lid) in Hchk.
        destruct (getRuleSlot (dagGet (stageBase s + stageDepth s)%nat lid) qOut)
          as [|nextId nextQ] eqn:Hsl; [discriminate |].
        simpl bytesToRight in Hb8.
        destruct (Htop lid qOut (bytesToLeft (outB :: lb) 0inf) sR nextId nextQ Hnt Hsl)
          as [sR1 [Hnt1 Hwall]].
        destruct (IH nextId false nextQ [] outB lb sR1 Hnt1 Hchk)
          as [sR' [Hnt' Hrest]].
        exists sR'. split; [exact Hnt' |].
        exact (ev_trans _ _ _ Hb8 (ev_trans _ _ _ Hwall Hrest)).
      * destruct (IH lid true qOut r' pb (outB :: lb) sR Hnt Hchk)
          as [sR' [Hnt' Hrest]].
        exists sR'. split; [exact Hnt' |].
        exact (ev_trans _ _ _ Hb8 Hrest).
    + pose proof (popByte_spec lb) as Hpb.
      destruct (popByte lb) as [nb l']; simpl in Hpb.
      destruct (IH lid false qOut (outB :: rb) nb l' sR Hnt Hchk)
        as [sR' [Hnt' Hrest]].
      exists sR'. split; [exact Hnt' |].
      cbn [byteEntryCfg bytesToRight] in Hrest.
      rewrite <- Hpb in Hrest.
      exact (ev_trans _ _ _ Hb8 Hrest).
Qed.
Arguments simTailBridge : simpl never.

Fixpoint simTailHalt (tbl : B8Table) (topTree : DagNTree)
    (fuel : nat) (lid : N) (side_b : bool) (q : Q)
    (rb : list Byte) (cb : Byte) (lb : list Byte) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match b8EntryT tbl side_b q cb with
    | B8Wall qOut outB =>
      match rb with
      | [] =>
        match getRuleSlot (ntree_get topTree lid) qOut with
        | R0 => false
        | RS nextId nextQ =>
          simTailHalt tbl topTree fuel' nextId false nextQ [] outB lb
        end
      | pb :: r' =>
        simTailHalt tbl topTree fuel' lid true qOut r' pb (outB :: lb)
      end
    | B8Tail qOut outB =>
      let '(nb, l') := popByte lb in
      simTailHalt tbl topTree fuel' lid false qOut (outB :: rb) nb l'
    | B8Halt => true
    | B8Fail => false
    end
  end.

Lemma simTailHalt_sound s :
  RuleSound s (stageDepth s) ->
  forall fuel lid side_b q rb cb lb (sR : side),
    NodeTape s (stageDepth s) lid sR ->
    simTailHalt theB8Table (dagTree (stageBase s + stageDepth s)%nat)
      fuel lid side_b q rb cb lb = true ->
    halts tm (byteEntryCfg side_b q cb (bytesToLeft lb 0inf) (bytesToRight rb sR)).
Proof.
  intros Htop fuel.
  induction fuel as [|fuel IH]; intros lid side_b q rb cb lb sR Hnt Hchk;
    cbn [simTailHalt] in Hchk; [discriminate |].
  pose proof (b8Entry_sound side_b q cb (bytesToLeft lb 0inf) (bytesToRight rb sR)) as Hb8.
  destruct (b8EntryT theB8Table side_b q cb) as [qOut outB | qOut outB | |]; try discriminate.
  - destruct rb as [|pb r'].
    + fold (dagGet (stageBase s + stageDepth s)%nat lid) in Hchk.
      destruct (getRuleSlot (dagGet (stageBase s + stageDepth s)%nat lid) qOut)
        as [|nextId nextQ] eqn:Hsl; [discriminate |].
      simpl bytesToRight in Hb8.
      destruct (Htop lid qOut (bytesToLeft (outB :: lb) 0inf) sR nextId nextQ Hnt Hsl)
        as [sR1 [Hnt1 Hwall]].
      pose proof (IH nextId false nextQ [] outB lb sR1 Hnt1 Hchk) as Hih.
      exact (evstep_halts _ _ Hb8 (evstep_halts _ _ Hwall Hih)).
    + pose proof (IH lid true qOut r' pb (outB :: lb) sR Hnt Hchk) as Hih.
      exact (evstep_halts _ _ Hb8 Hih).
  - pose proof (popByte_spec lb) as Hpb.
    destruct (popByte lb) as [nb l']; simpl in Hpb.
    pose proof (IH lid false qOut (outB :: rb) nb l' sR Hnt Hchk) as Hih.
    cbn [byteEntryCfg bytesToRight] in Hih.
    rewrite <- Hpb in Hih.
    exact (evstep_halts _ _ Hb8 Hih).
  - exact Hb8.
Qed.
Arguments simTailHalt : simpl never.

Fixpoint simStagePush (tbl : B8Table) (sliceFuel : nat) (isHalt : bool) (baseL : nat)
    (tgtLid : N) (tgtQ : Q) (tgtBytes : list Byte)
    (tailFuel fuel cd : nat) (lid : N) (side_b : bool) (q : Q)
    (cb : Byte) (lb rest : list Byte) (pushes : list N) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match simSliceBytes tbl sliceFuel side_b q [] cb lb with
    | SliceHalt => isHalt
    | SliceWall qOut outB l' =>
      let curL := (baseL + cd)%nat in
      match getRuleSlot (dagGet curL lid) qOut with
      | R0 => false
      | RS nextId nextQ =>
        simStagePush tbl sliceFuel isHalt baseL tgtLid tgtQ tgtBytes
          tailFuel fuel' cd nextId false nextQ outB l' rest pushes
      end
    | SliceTail qOut outSlice =>
      match pushes with
      | [] => false
      | nid :: ps' =>
        let cd' := S cd in
        let nxtL := (baseL + cd')%nat in
        let 'MkDag npar nslice _ _ _ _ := dagGet nxtL nid in
        if (N.eqb npar lid && sliceEqb nslice outSlice)%bool then
          match ps' with
          | [] =>
            let '(tcb, tlb) := popByte rest in
            if isHalt then
              simTailHalt tbl (dagTree nxtL) tailFuel nid false qOut [] tcb tlb
            else
              simTailBridge tbl (dagTree nxtL) tgtLid tgtQ tgtBytes tailFuel nid false qOut [] tcb tlb
          | _ :: _ =>
            match popNBytes (nbytesOf (S nxtL)) rest with
            | (nb :: lNext, rst') =>
              simStagePush tbl sliceFuel isHalt baseL tgtLid tgtQ tgtBytes
                tailFuel fuel' cd' nid false qOut nb lNext rst' ps'
            | ([], _) => false
            end
          end
        else false
      end
    | SliceFail => false
    end
  end.

Lemma simStagePush_bridge_sound sliceFuel s :
  (s <= 13)%nat ->
  forall tgtLid tgtQ tgtBytes tailFuel fuel cd lid side_b q cb lb rest pushes (sR : side),
    (cd + length pushes = stageDepth s)%nat ->
    NodeTape s cd lid sR ->
    simStagePush theB8Table sliceFuel false (stageBase s) tgtLid tgtQ tgtBytes
      tailFuel fuel cd lid side_b q cb lb rest pushes = true ->
    exists sR', NodeTape s (stageDepth s) tgtLid sR' /\
      (byteEntryCfg side_b q cb (bytesToLeft lb (bytesToLeft rest 0inf)) sR -->*
       bytesToLeft tgtBytes 0inf <{{tgtQ}} sR').
Proof.
  intros Hs tgtLid tgtQ tgtBytes tailFuel fuel.
  induction fuel as [|fuel IH]; intros cd lid side_b q cb lb rest pushes sR Hcd Hnt Hchk;
    cbn [simStagePush] in Hchk; [discriminate |].
  pose proof (simSliceBytes_sound sliceFuel side_b q [] cb lb (bytesToLeft rest 0inf) sR) as Hsim.
  simpl bytesToRight in Hsim.
  destruct (simSliceBytes theB8Table sliceFuel side_b q [] cb lb)
    as [qOut outB l' | qOut outSlice | |]; try discriminate.
  - destruct (getRuleSlot (dagGet (stageBase s + cd)%nat lid) qOut)
      as [|nextId nextQ] eqn:Hsl; [discriminate |].
    assert (HcdLe : (cd <= stageDepth s)%nat) by lia.
    destruct (ruleSound_all s cd Hs HcdLe lid qOut
                (bytesToLeft (outB :: l') (bytesToLeft rest 0inf)) sR nextId nextQ Hnt Hsl)
      as [sR1 [Hnt1 Hwall]].
    destruct (IH cd nextId false nextQ outB l' rest pushes sR1 Hcd Hnt1 Hchk)
      as [sR' [Hnt' Hrest]].
    exists sR'. split; [exact Hnt' |].
    exact (ev_trans _ _ _ Hsim (ev_trans _ _ _ Hwall Hrest)).
  - destruct pushes as [|nid ps']; [discriminate |].
    destruct (dagGet (stageBase s + S cd)%nat nid) as [npar nslice s0 s1 s3 s5] eqn:Hget.
    destruct ((N.eqb npar lid && sliceEqb nslice outSlice)%bool) eqn:Heq; [| discriminate].
    apply andb_prop in Heq as [Hp HsEq].
    apply N.eqb_eq in Hp. apply sliceEqb_eq in HsEq. subst npar nslice.
    assert (Hnt' : NodeTape s (S cd) nid (bytesToRight outSlice sR)).
    { unfold NodeTape; cbn [StageNodeTape]. rewrite Hget.
       exists sR. split; [exact Hnt | reflexivity]. }
    destruct ps' as [|p2 ps''].
    + assert (HcdTop : S cd = stageDepth s) by (simpl in Hcd; lia).
      pose proof (popByte_spec rest) as Hpb.
      destruct (popByte rest) as [tcb tlb]; simpl in Hpb.
      rewrite HcdTop in Hnt', Hchk.
      destruct (simTailBridge_sound s (ruleSound_all s (stageDepth s) Hs (PeanoNat.Nat.le_refl _))
                  tgtLid tgtQ tgtBytes tailFuel nid false qOut [] tcb tlb
                  (bytesToRight outSlice sR) Hnt' Hchk) as [sR' [HntEnd Htail]].
      exists sR'. split; [exact HntEnd |].
      cbn [byteEntryCfg bytesToRight] in Htail.
      rewrite <- Hpb in Htail.
      exact (ev_trans _ _ _ Hsim Htail).
    + pose proof (popNBytes_spec (nbytesOf (S (stageBase s + S cd))) rest) as Hpn.
      destruct (popNBytes (nbytesOf (S (stageBase s + S cd))) rest) as [[|nb lNext] rst'];
        [discriminate |].
      simpl in Hpn.
      assert (Hcd' : (S cd + length (p2 :: ps'') = stageDepth s)%nat) by (simpl in Hcd |- *; lia).
      destruct (IH (S cd) nid false qOut nb lNext rst' (p2 :: ps'')
                  (bytesToRight outSlice sR) Hcd' Hnt' Hchk) as [sR' [HntEnd Hih]].
      exists sR'. split; [exact HntEnd |].
      cbn [byteEntryCfg] in Hih.
      rewrite <- Hpn in Hih.
      exact (ev_trans _ _ _ Hsim Hih).
Qed.

Lemma simStagePush_halt_sound sliceFuel s :
  (s <= 13)%nat ->
  forall tailFuel fuel cd lid side_b q cb lb rest pushes (sR : side),
    (cd + length pushes = stageDepth s)%nat ->
    NodeTape s cd lid sR ->
    simStagePush theB8Table sliceFuel true (stageBase s) 0%N A []
      tailFuel fuel cd lid side_b q cb lb rest pushes = true ->
    halts tm (byteEntryCfg side_b q cb (bytesToLeft lb (bytesToLeft rest 0inf)) sR).
Proof.
  intros Hs tailFuel fuel.
  induction fuel as [|fuel IH]; intros cd lid side_b q cb lb rest pushes sR Hcd Hnt Hchk;
    cbn [simStagePush] in Hchk; [discriminate |].
  pose proof (simSliceBytes_sound sliceFuel side_b q [] cb lb (bytesToLeft rest 0inf) sR) as Hsim.
  simpl bytesToRight in Hsim.
  destruct (simSliceBytes theB8Table sliceFuel side_b q [] cb lb)
    as [qOut outB l' | qOut outSlice | |]; try discriminate.
  - destruct (getRuleSlot (dagGet (stageBase s + cd)%nat lid) qOut)
      as [|nextId nextQ] eqn:Hsl; [discriminate |].
    assert (HcdLe : (cd <= stageDepth s)%nat) by lia.
    destruct (ruleSound_all s cd Hs HcdLe lid qOut
                (bytesToLeft (outB :: l') (bytesToLeft rest 0inf)) sR nextId nextQ Hnt Hsl)
      as [sR1 [Hnt1 Hwall]].
    pose proof (IH cd nextId false nextQ outB l' rest pushes sR1 Hcd Hnt1 Hchk) as Hih.
    exact (evstep_halts _ _ Hsim (evstep_halts _ _ Hwall Hih)).
  - destruct pushes as [|nid ps']; [discriminate |].
    destruct (dagGet (stageBase s + S cd)%nat nid) as [npar nslice s0 s1 s3 s5] eqn:Hget.
    destruct ((N.eqb npar lid && sliceEqb nslice outSlice)%bool) eqn:Heq; [| discriminate].
    apply andb_prop in Heq as [Hp HsEq].
    apply N.eqb_eq in Hp. apply sliceEqb_eq in HsEq. subst npar nslice.
    assert (Hnt' : NodeTape s (S cd) nid (bytesToRight outSlice sR)).
    { unfold NodeTape; cbn [StageNodeTape]. rewrite Hget.
       exists sR. split; [exact Hnt | reflexivity]. }
    destruct ps' as [|p2 ps''].
    + assert (HcdTop : S cd = stageDepth s) by (simpl in Hcd; lia).
      pose proof (popByte_spec rest) as Hpb.
      destruct (popByte rest) as [tcb tlb]; simpl in Hpb.
      rewrite HcdTop in Hnt', Hchk.
      pose proof (simTailHalt_sound s (ruleSound_all s (stageDepth s) Hs (PeanoNat.Nat.le_refl _))
                    tailFuel nid false qOut [] tcb tlb
                    (bytesToRight outSlice sR) Hnt' Hchk) as Htail.
      cbn [byteEntryCfg bytesToRight] in Htail.
      rewrite <- Hpb in Htail.
      exact (evstep_halts _ _ Hsim Htail).
    + pose proof (popNBytes_spec (nbytesOf (S (stageBase s + S cd))) rest) as Hpn.
      destruct (popNBytes (nbytesOf (S (stageBase s + S cd))) rest) as [[|nb lNext] rst'];
        [discriminate |].
      simpl in Hpn.
      assert (Hcd' : (S cd + length (p2 :: ps'') = stageDepth s)%nat) by (simpl in Hcd |- *; lia).
      pose proof (IH (S cd) nid false qOut nb lNext rst' (p2 :: ps'')
                    (bytesToRight outSlice sR) Hcd' Hnt' Hchk) as Hih.
      cbn [byteEntryCfg] in Hih.
      rewrite <- Hpn in Hih.
      exact (evstep_halts _ _ Hsim Hih).
  - exact Hsim.
Qed.
Arguments simStagePush : simpl never.

Definition checkStageBridge (s : nat) : bool :=
  match popNBytes (nbytesOf (S (stageBase s))) (stageInitBytes s) with
  | (cb :: lb, rest) =>
    simStagePush theB8Table 160%nat false (stageBase s) 0%N (stageInitQ (S s)) (stageInitBytes (S s))
      (stageBridgeFuel s) (stageBridgeFuel s) 0%nat (stageInitLid s) false (stageInitQ s)
      cb lb rest (stagePushIds s)
  | ([], _) => false
  end.

Definition checkAllBridges : bool :=
  checkStageBridge 0%nat && checkStageBridge 1%nat && checkStageBridge 2%nat && checkStageBridge 3%nat &&
  checkStageBridge 4%nat && checkStageBridge 5%nat && checkStageBridge 6%nat && checkStageBridge 7%nat &&
  checkStageBridge 8%nat && checkStageBridge 9%nat && checkStageBridge 10%nat && checkStageBridge 11%nat &&
  checkStageBridge 12%nat.

Lemma all_bridges_valid : checkAllBridges = true.
Proof. vm_check_eq. Qed.

Lemma checkStageBridge_of_all (s : nat) : (s < 13)%nat -> checkStageBridge s = true.
Proof.
  intros Hs.
  pose proof all_bridges_valid as Hv. unfold checkAllBridges in Hv.
  repeat (apply andb_prop in Hv as [Hv ?]).
  do 13 (destruct s as [|s]; [assumption |]).
  lia.
Qed.

Definition checkStageHalt : bool :=
  match popNBytes (nbytesOf (S (stageBase 13%nat))) (stageInitBytes 13%nat) with
  | (cb :: lb, rest) =>
    simStagePush theB8Table 160%nat true (stageBase 13%nat) 0%N A []
      (stageBridgeFuel 13%nat) (stageBridgeFuel 13%nat) 0%nat (stageInitLid 13%nat) false
      (stageInitQ 13%nat) cb lb rest (stagePushIds 13%nat)
  | ([], _) => false
  end.

Lemma stage_halt_valid : checkStageHalt = true.
Proof. vm_check_eq. Qed.

Lemma stagePushIds_len (s : nat) : (s <= 13)%nat -> length (stagePushIds s) = stageDepth s.
Proof.
  intros Hs. do 14 (destruct s as [|s]; [reflexivity |]). lia.
Qed.

Lemma stageWallCnt_pos (s : nat) : (s < 13)%nat -> (0 < N.of_nat (stageWallCnt s))%N.
Proof.
  intros Hs. do 13 (destruct s as [|s]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma stageInitLid_succ (s : nat) : (s < 13)%nat -> stageInitLid (S s) = 0%N.
Proof.
  intros Hs. do 13 (destruct s as [|s]; [reflexivity |]). lia.
Qed.

Lemma stageBridge_step (s : nat) (sR : side) :
  (s < 13)%nat ->
  NodeTape s 0%nat (stageInitLid s) sR ->
  exists sR', NodeTape (S s) 0%nat (stageInitLid (S s)) sR' /\
    (bytesToLeft (stageInitBytes s) 0inf <{{stageInitQ s}} sR -->*
     bytesToLeft (stageInitBytes (S s)) 0inf <{{stageInitQ (S s)}} sR').
Proof.
  intros Hs Hnt.
  pose proof (checkStageBridge_of_all s Hs) as Hchk.
  unfold checkStageBridge in Hchk.
  pose proof (popNBytes_spec (nbytesOf (S (stageBase s))) (stageInitBytes s)) as Hpn.
  destruct (popNBytes (nbytesOf (S (stageBase s))) (stageInitBytes s)) as [[|cb lb] rest];
    [discriminate |].
  simpl in Hpn.
  assert (Hcd : (0 + length (stagePushIds s) = stageDepth s)%nat)
    by (exact (stagePushIds_len s ltac:(lia))).
  destruct (simStagePush_bridge_sound 160%nat s ltac:(lia) 0%N (stageInitQ (S s)) (stageInitBytes (S s))
              (stageBridgeFuel s) (stageBridgeFuel s) 0%nat (stageInitLid s) false (stageInitQ s)
              cb lb rest (stagePushIds s) sR Hcd Hnt Hchk) as [sR' [HntTop Hrc]].
  exists sR'. split.
  - rewrite (stageInitLid_succ s Hs).
    unfold NodeTape; simpl.
    split; [reflexivity | exists 0%N; split; [exact (stageWallCnt_pos s Hs) | exact HntTop]].
  - rewrite Hpn. exact Hrc.
Qed.

Lemma stage13_halts (sR : side) :
  NodeTape 13%nat 0%nat (stageInitLid 13%nat) sR ->
  halts tm (bytesToLeft (stageInitBytes 13%nat) 0inf <{{stageInitQ 13%nat}} sR).
Proof.
  intros Hnt.
  exact (simStagePush_halt_sound 160%nat 13%nat (PeanoNat.Nat.le_refl _)
    (stageBridgeFuel 13%nat) (stageBridgeFuel 13%nat) 0%nat (stageInitLid 13%nat) false
    (stageInitQ 13%nat) h10 [h64; h90; h90; h04; h90] [h00; h32; h01]
    (stagePushIds 13%nat) sR eq_refl Hnt stage_halt_valid).
Qed.

(* Link 1b: Blank Tape -> Stage 0 Entry & Top-Level Halting Theorem *)

Lemma rb303_eq_crysTape : bitsToSide rb303 0inf = crysTape P0 1%nat.
Proof.
  rewrite bitsToSide_eq_str. unfold crysTape.
  rewrite <- !Str_app_assoc.
  reflexivity.
Qed.

Definition tail0_21 : list bool := [true; false; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; true; false; false; true].

Lemma lb303_split : lb303 = [false; false; false; false; false] ++ tail0_21.
Proof. reflexivity. Qed.

Lemma tail0_21_eq_stage0 :
  bitsToSide tail0_21 0inf = bytesToLeft (stageInitBytes 0%nat) 0inf.
Proof.
  rewrite <- (bitsToSide_zeros 3%nat) at 1.
  rewrite <- bitsToSide_app.
  unfold stageInitBytes, bytesToLeft, byteBitsToSide.
  reflexivity.
Qed.

Definition checkLink1b : bool :=
  match simCrysWall 120%nat P1 C [false; false; false; false; false] [] with
  | Some (ph', q', rb') =>
    phaseEqb ph' (crysBasePh (stageInitLid 0%nat)) &&
    qEqb q' (stageInitQ 0%nat) &&
    boolListEqb rb' (crysBaseBits (stageInitLid 0%nat))
  | None => false
  end.

Lemma link1b_valid : checkLink1b = true.
Proof. vm_check_eq. Qed.

Lemma link1b_reaches :
  exists sR0, NodeTape 0%nat 0%nat (stageInitLid 0%nat) sR0 /\
    (c0 -->* bytesToLeft (stageInitBytes 0%nat) 0inf <{{stageInitQ 0%nat}} sR0).
Proof.
  pose proof link1_reaches as H1.
  rewrite rb303_eq_crysTape, lb303_split, bitsToSide_app, tail0_21_eq_stage0 in H1.
  destruct (crystal_bounce P0 1%nat
    (bitsToSide [false; false; false; false; false] (bytesToLeft (stageInitBytes 0%nat) 0inf)))
    as [c1 Hcb].
  simpl fst in Hcb; simpl snd in Hcb; simpl nextPhase in Hcb.
  pose proof link1b_valid as Hv. unfold checkLink1b in Hv.
  destruct (simCrysWall 120%nat P1 C [false; false; false; false; false] [])
    as [[[ph' q'] rb'] |] eqn:Hw; [| discriminate].
  apply andb_prop in Hv as [Hv1 Hrb].
  apply andb_prop in Hv1 as [Hph Hq].
  apply phaseEqb_eq in Hph. apply qEqb_eq in Hq. apply boolListEqb_eq in Hrb.
  subst ph' q' rb'.
  destruct (simCrysWall_sound _ _ _ _ _ _ _ _ Hw c1 (bytesToLeft (stageInitBytes 0%nat) 0inf))
    as [c2 Hrc].
  change (bitsToSide [] (crysTape P1 c1)) with (crysTape P1 c1) in Hrc.
  exists (bitsToSide (crysBaseBits (stageInitLid 0%nat)) (crysTape (crysBasePh (stageInitLid 0%nat)) c2)).
  split; [exists c2; reflexivity |].
  exact (ev_trans _ _ _ H1 (ev_trans _ _ _ Hcb Hrc)).
Qed.

Lemma main_halts : halts tm c0.
Proof.
  destruct link1b_reaches as [sR0 [Hnt0 Hr0]].
  destruct (stageBridge_step 0%nat sR0 ltac:(lia) Hnt0) as [sR1 [Hnt1 Hr1]].
  destruct (stageBridge_step 1%nat sR1 ltac:(lia) Hnt1) as [sR2 [Hnt2 Hr2]].
  destruct (stageBridge_step 2%nat sR2 ltac:(lia) Hnt2) as [sR3 [Hnt3 Hr3]].
  destruct (stageBridge_step 3%nat sR3 ltac:(lia) Hnt3) as [sR4 [Hnt4 Hr4]].
  destruct (stageBridge_step 4%nat sR4 ltac:(lia) Hnt4) as [sR5 [Hnt5 Hr5]].
  destruct (stageBridge_step 5%nat sR5 ltac:(lia) Hnt5) as [sR6 [Hnt6 Hr6]].
  destruct (stageBridge_step 6%nat sR6 ltac:(lia) Hnt6) as [sR7 [Hnt7 Hr7]].
  destruct (stageBridge_step 7%nat sR7 ltac:(lia) Hnt7) as [sR8 [Hnt8 Hr8]].
  destruct (stageBridge_step 8%nat sR8 ltac:(lia) Hnt8) as [sR9 [Hnt9 Hr9]].
  destruct (stageBridge_step 9%nat sR9 ltac:(lia) Hnt9) as [sR10 [Hnt10 Hr10]].
  destruct (stageBridge_step 10%nat sR10 ltac:(lia) Hnt10) as [sR11 [Hnt11 Hr11]].
  destruct (stageBridge_step 11%nat sR11 ltac:(lia) Hnt11) as [sR12 [Hnt12 Hr12]].
  destruct (stageBridge_step 12%nat sR12 ltac:(lia) Hnt12) as [sR13 [Hnt13 Hr13]].
  pose proof (stage13_halts sR13 Hnt13) as Hh.
  exact (evstep_halts _ _ Hr0
    (evstep_halts _ _ Hr1
      (evstep_halts _ _ Hr2
        (evstep_halts _ _ Hr3
          (evstep_halts _ _ Hr4
            (evstep_halts _ _ Hr5
              (evstep_halts _ _ Hr6
                (evstep_halts _ _ Hr7
                  (evstep_halts _ _ Hr8
                    (evstep_halts _ _ Hr9
                      (evstep_halts _ _ Hr10
                        (evstep_halts _ _ Hr11
                          (evstep_halts _ _ Hr12
                            (evstep_halts _ _ Hr13 Hh)))))))))))))).
Qed.

End M5.

Theorem halt : halts tm c0.
Proof. exact M5.main_halts. Qed.
