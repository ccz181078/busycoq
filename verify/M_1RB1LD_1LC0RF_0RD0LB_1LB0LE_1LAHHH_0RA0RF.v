(* PR #91: compute slice returns on demand. At each stage boundary,
   check that the reachable wall family can be treated as one interface
   for the next stage. No return-rule DAGs are stored in the source. *)

From BusyCoq Require Import Individual62.
Require Import String List PeanoNat NArith PArith ZifyNat ZifyN Lia.
Import ListNotations.
Open Scope bool_scope.
Open Scope list_scope.
Open Scope sym_scope.

From BusyCoq Require HashTable.
From Coq Require Uint63.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF").

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

Local Notation h00 := (MkB X0 X0). Local Notation h01 := (MkB X0 X1). Local Notation h02 := (MkB X0 X2). Local Notation h04 := (MkB X0 X4). Local Notation h06 := (MkB X0 X6). Local Notation h09 := (MkB X0 X9). Local Notation h0a := (MkB X0 XA). Local Notation h10 := (MkB X1 X0). Local Notation h12 := (MkB X1 X2). Local Notation h1c := (MkB X1 XC). Local Notation h20 := (MkB X2 X0). Local Notation h24 := (MkB X2 X4). Local Notation h26 := (MkB X2 X6). Local Notation h29 := (MkB X2 X9). Local Notation h32 := (MkB X3 X2). Local Notation h41 := (MkB X4 X1). Local Notation h48 := (MkB X4 X8). Local Notation h49 := (MkB X4 X9). Local Notation h4c := (MkB X4 XC). Local Notation h50 := (MkB X5 X0). Local Notation h52 := (MkB X5 X2). Local Notation h64 := (MkB X6 X4). Local Notation h82 := (MkB X8 X2). Local Notation h90 := (MkB X9 X0). Local Notation h92 := (MkB X9 X2). Local Notation h94 := (MkB X9 X4). Local Notation ha4 := (MkB XA X4). Local Notation ha6 := (MkB XA X6). Definition nibEqb (x y : Nib) : bool :=
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
  | B8Wall qOut outB =>
    byteEntryCfg side_b q b sL sR -->* byteBitsToSide outB sL {{qOut}}> sR
  | B8Tail qOut outB =>
    byteEntryCfg side_b q b sL sR -->* sL <{{qOut}} byteBitsRevToSide outB sR
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

Definition stageWidths : list (list nat) :=
  [[5;5;5;4];[6;6;6;6;6;6;6;6;6;6;5;2];[5;5;5;5;5];[6];[5;5;5;2];[6];[6;6;6;6;6;4];[5;5;5;5;5];[4;4];[5;5;5;5;5;5;5];[4];[6;5];[4];[6;6;6;6;4]].
Definition stageReplies : list (list (Q * Q)) :=
  [[];[(F,D)];[(A,B)];[(B,C)];[(A,D);(F,B)];[(F,D)];[(B,A);(F,A)];[(F,D)];[(B,C)];[(B,A);(F,A)];[(F,D)];[(F,B)];[(A,D);(F,B)];[(B,C)]].

(* A label identifies the bottom of the wall, not the unbounded
   counter. Within a stage all cached returns use the same bottom rules. *)
Definition Wall := (list (list Byte) * N)%type.
Definition addSlice bs (w : Wall) : Wall := (bs :: fst w, snd w).
Definition BottomCall := N -> Q -> option (N * Q).

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

Module NKey <: HashTable.HashableType.
  Definition K := N.
  Definition K_hash := HashTable.HashConcat.N_hash.
  Definition K_eq := N.eqb.
  Definition K_eq_spec := N.eqb_spec.
End NKey.

Module SliceKey := HashTable.ListHash ByteKey.
Module SlicesKey := HashTable.ListHash SliceKey.
Module WallKey := HashTable.ProdHash SlicesKey NKey.
Module CacheKey := HashTable.ProdHash WallKey QKey.
Module CacheVal <: HashTable.ValueType.
  Definition V := (Wall * Q)%type.
End CacheVal.
Module Cache := HashTable.HashMap CacheKey CacheVal.

Definition Memo := Cache.hmap_t.
Definition WallResult := (option (Wall * Q) * Memo)%type.
Definition WallCall := Wall -> Q -> Memo -> WallResult.
Definition freshMemo (_ : unit) : Memo :=
  Cache.hmap_make (Uint63.of_Z (BinNums.Zpos 10007%positive)).

Fixpoint returnSlice (call : WallCall) (fuel : nat)
    (w : Wall) (dir : bool) (q : Q) (rb : list Byte)
    (b : Byte) (lb : list Byte) (t : Memo) : WallResult :=
  match fuel with
  | O => (None,t)
  | S fuel' =>
    match simSliceBytes theB8Table 160 dir q rb b lb with
    | SliceTail q' out => (Some (addSlice out w,q'),t)
    | SliceWall p a l =>
      match call w p t with
      | (Some (w',p'),t') => returnSlice call fuel' w' false p' [] a l t'
      | (None,t') => (None,t')
      end
    | _ => (None,t)
    end
  end.

Definition memoCall (w : Wall) q (f : Memo -> WallResult) (t : Memo) : WallResult :=
  match Cache.hmap_get (w,q) t with
  | Some out => (Some out,t)
  | None =>
    match f t with
    | (Some out,t') => (Some out, Cache.hmap_set (w,q) out t')
    | (None,t') => (None,t')
    end
  end.

Fixpoint returnWall (base : BottomCall) (depth : nat) (w : Wall) (q : Q) (t : Memo) : WallResult :=
  memoCall w q (fun t0 =>
    match w with
    | ([],i) => (option_map (fun '(j,p) => (([],j),p)) (base i q),t0)
    | ((b::rb)::slices,i) =>
      match depth with
      | O => (None,t0)
      | S d => returnSlice (returnWall base d) 360 (slices,i) true q rb b [] t0
      end
    | _ => (None,t0)
    end) t.

Definition wallCall base : WallCall :=
  fun w => returnWall base (length (fst w)) w.

Definition Target := option (Q * list Byte).
Definition RunResult := (option (option Wall) * Memo)%type.

Definition hits (target : Target) (dir : bool) q (rb : list Byte) b lb : bool :=
  match target, dir, rb with
  | Some (p,bs), false, [] => qEqb q p && bytesEqZeroPad (b::lb) bs
  | _,_,_ => false
  end.

Fixpoint runTail (call : WallCall) target (fuel : nat) (w : Wall)
    (dir : bool) (q : Q) (rb : list Byte) (b : Byte) (lb : list Byte) (t : Memo)
    : RunResult :=
  match fuel with
  | O => (None,t)
  | S f =>
    if hits target dir q rb b lb then (Some (Some w),t)
    else
      match b8EntryT theB8Table dir q b with
      | B8Wall p a =>
        match rb with
        | c::r => runTail call target f w true p r c (a::lb) t
        | [] =>
          match call w p t with
          | (Some (w',p'),t') => runTail call target f w' false p' [] a lb t'
          | (None,t') => (None,t')
          end
        end
      | B8Tail p a =>
        let '(c,l) := popByte lb in
        runTail call target f w false p (a::rb) c l t
      | B8Halt => (Some None,t)
      | B8Fail => (None,t)
      end
  end.

Fixpoint runCuts (call : WallCall) target (fuel : nat) (w : Wall)
    (q : Q) (b : Byte) (lb rest : list Byte) (widths : list nat) (t : Memo)
    : RunResult :=
  match fuel with
  | O => (None,t)
  | S f =>
    match simSliceBytes theB8Table 160 false q [] b lb with
    | SliceWall p a l =>
      match call w p t with
      | (Some (w',p'),t') => runCuts call target f w' p' a l rest widths t'
      | (None,t') => (None,t')
      end
    | SliceTail p out =>
      let w' := addSlice out w in
      match widths with
      | [] =>
        let '(a,l) := popByte rest in
        runTail call target 1100 w' false p [] a l t
      | n::ns =>
        match popNBytes n rest with
        | (a::l,rest') => runCuts call target f w' p a l rest' ns t
        | ([],_) => (None,t)
        end
      end
    | SliceHalt => (Some None,t)
    | SliceFail => (None,t)
    end
  end.

Definition runStage base i q bs widths target : RunResult :=
  match widths with
  | [] => (None,freshMemo tt)
  | n::ns =>
    let t := freshMemo tt in
    match popNBytes n bs with
    | (b::lb, rest) => runCuts (wallCall base) target 1100 ([],i) q b lb rest ns t
    | ([],_) => (None,t)
    end
  end.

Definition crystalPairEq ph bs i :=
  phaseEqb ph (crysBasePh i) && boolListEqb bs (crysBaseBits i).

Definition crystalCall : BottomCall := fun i q =>
  match crysBaseBits i with
  | [] => None
  | b::bs =>
    match simCrysWall 120 (crysBasePh i) q [b] bs with
    | Some (ph,p,bs') =>
      option_map (fun j => (j,p)) (find (crystalPairEq ph bs') [0%N;1%N;2%N;3%N;4%N;5%N;6%N;7%N])
    | None => None
    end
  end.

Definition repliesCall (replies : list (Q * Q)) : BottomCall :=
  fun _ q => option_map (fun p => (0%N,snd p)) (find (fun p => qEqb q (fst p)) replies).

Fixpoint nextWalls (call : WallCall) (replies : list (Q * Q)) (w : Wall) (t : Memo)
    : option (list Wall) * Memo :=
  match replies with
  | [] => (Some [],t)
  | (q,p)::rs =>
    match call w q t with
    | (Some(w',p'),t') =>
      if qEqb p p' then
        let '(out,t'') := nextWalls call rs w t' in (option_map (cons w') out,t'')
      else (None,t')
    | (None,t') => (None,t')
    end
  end.

Definition inWalls (ws : list Wall) w := existsb (WallKey.K_eq w) ws.

(* Explore the small family reachable from the actual bridge output.
   The independent audit below checks its closure. *)
Fixpoint collectFamily (call : WallCall) replies (fuel : nat) (todo seen : list Wall) (t : Memo)
    : option (list Wall) * Memo :=
  match fuel with
  | O => (None,t)
  | S f =>
    match todo with
    | [] => (Some seen,t)
    | w::ws =>
      if inWalls seen w then collectFamily call replies f ws seen t
      else
        match nextWalls call replies w t with
        | (Some out,t') => collectFamily call replies f (out++ws) (w::seen) t'
        | (None,t') => (None,t')
        end
    end
  end.

Fixpoint auditFamily (call : WallCall) replies (family todo : list Wall) (t : Memo) : bool :=
  match todo with
  | [] => true
  | w::ws =>
    match nextWalls call replies w t with
    | (Some out,t') => forallb (inWalls family) out && auditFamily call replies family ws t'
    | (None,_) => false
    end
  end.

Definition closed (base : BottomCall) replies w t : option (list Wall) :=
  let call := wallCall base in
  match collectFamily call replies 128 [w] [] t with
  | (Some family,t') =>
    if inWalls family w && auditFamily call replies family family t'
    then Some family else None
  | _ => None
  end.

Definition entry s := (stageInitQ s,stageInitBytes s).

Fixpoint executeStages (widths : list (list nat)) (replies : list (list (Q*Q)))
    (s : nat) (base : BottomCall) (i : N) : nat * bool :=
  match widths,replies with
  | ns::more, rs::later =>
    let target := match more with [] => None | _ => Some (entry (S s)) end in
    match runStage base i (stageInitQ s) (stageInitBytes s) ns target with
    | (Some None,_) => (s,true)
    | (Some (Some w),t) =>
      match closed base rs w t with
      | Some _ => executeStages more later (S s) (repliesCall rs) 0%N
      | None => (s,false)
      end
    | _ => (s,false)
    end
  | _,_ => (s,false)
  end.

Definition stageProgress :=
  executeStages stageWidths (tl stageReplies ++ [[]]) 0%nat crystalCall 1%N.

Definition Bottom := N -> side -> Prop.
Definition BottomSound (inv : Bottom) (call : BottomCall) :=
  forall i q j p sL sR, call i q = Some (j,p) -> inv i sR ->
    exists sR', inv j sR' /\ (sL {{q}}> sR -->* sL <{{p}} sR').

Fixpoint stackTape (base : side -> Prop) (slices : list (list Byte)) (sR : side) : Prop :=
  match slices with
  | [] => base sR
  | bs :: rest => exists s, stackTape base rest s /\ sR = bytesToRight bs s
  end.

Definition wallTape (inv : Bottom) (w : Wall) := stackTape (inv (snd w)) (fst w).

Definition returnSpec inv (src out : Wall * Q) :=
  forall sL sR, wallTape inv (fst src) sR ->
    exists sR', wallTape inv (fst out) sR' /\ (sL {{snd src}}> sR -->* sL <{{snd out}} sR').

Definition memoValid inv (t : Memo) :=
  Cache.hmap_WF t /\
  forall key value, Cache.hmap_get key t = Some value -> returnSpec inv key value.

Definition returnSound inv key (p : WallResult) :=
  let '(ret,t') := p in memoValid inv t' /\
    match ret with Some out => returnSpec inv key out | None => True end.

Definition CallSound inv (call : WallCall) :=
  forall w q t, memoValid inv t -> returnSound inv (w,q) (call w q t).

Lemma memo_empty inv : memoValid inv (freshMemo tt).
Proof.
  unfold freshMemo. split; [apply Cache.hmap_make_WF|].
  intros k v; rewrite Cache.hmap_get_make; discriminate.
Qed.

Lemma memo_insert inv t k v : memoValid inv t -> returnSpec inv k v ->
  memoValid inv (Cache.hmap_set k v t).
Proof.
  intros [Hwf Hmemo] Hv; split; [now apply Cache.hmap_set_WF|].
  intros key value.
  destruct (CacheKey.K_eq_spec key k) as [->|Hne].
  - rewrite Cache.hmap_get_set_same by exact Hwf. now intros [= <-].
  - rewrite Cache.hmap_get_set_other by assumption. apply Hmemo.
Qed.

Local Opaque Cache.hmap_get Cache.hmap_set.

Lemma memoCall_sound inv w q f t :
  memoValid inv t ->
  (forall t0, memoValid inv t0 -> returnSound inv (w,q) (f t0)) ->
  returnSound inv (w,q) (memoCall w q f t).
Proof.
  intros Ht Hf. unfold memoCall, returnSound.
  remember (Cache.hmap_get (@pair Wall QKey.K w q) t) as hit eqn:E; symmetry in E.
  destruct hit as [v|].
  - exact (conj Ht (proj2 Ht _ _ E)).
  - specialize (Hf t Ht). destruct (f t) as [[v|] t'] eqn:Ef; try rewrite Ef; [|exact Hf].
    destruct Hf as [Ht' Hv]. exact (conj (memo_insert _ _ _ _ Ht' Hv) Hv).
Qed.

Definition sliceSpec inv w dir q rb b lb (out : Wall * Q) :=
  forall sL sR, wallTape inv w sR ->
    exists sR', wallTape inv (fst out) sR' /\
      (byteEntryCfg dir q b (bytesToLeft lb sL) (bytesToRight rb sR)
       -->* sL <{{snd out}} sR').

Lemma returnSlice_sound inv call (Hcall : CallSound inv call) fuel :
  forall w dir q rb b lb t, memoValid inv t ->
    let '(ret,t') := returnSlice call fuel w dir q rb b lb t in
    memoValid inv t' /\
      match ret with Some out => sliceSpec inv w dir q rb b lb out | None => True end.
Proof.
  induction fuel as [|f IH]; intros w dir q rb b lb t Ht.
  - exact (conj Ht I).
  - cbn [returnSlice].
    destruct (simSliceBytes theB8Table 160 dir q rb b lb) as [p a l|p out| |] eqn:Es;
      try exact (conj Ht I).
    + pose proof (Hcall w p t Ht) as Hr.
      destruct (call w p t) as [[[w' p']|] t']; [|exact Hr].
      destruct Hr as [Ht' Hr].
      specialize (IH w' false p' [] a l t' Ht').
      destruct (returnSlice call f w' false p' [] a l t') as [[v|] t'']; [|exact IH].
      destruct IH as [Ht'' Hn]. split; [exact Ht''|].
      intros sL sR Hw.
      pose proof (simSliceBytes_sound 160 dir q rb b lb sL sR) as Hs.
      rewrite Es in Hs.
      destruct (Hr (bytesToLeft (a::l) sL) sR Hw) as [sR' [Hw' Hret]].
      destruct (Hn sL sR' Hw') as [sR'' [Hw'' Hnext]].
      exists sR''. split; [exact Hw''|].
      exact (ev_trans _ _ _ Hs (ev_trans _ _ _ Hret Hnext)).
    + split; [exact Ht|]. intros sL sR Hw.
      exists (bytesToRight out sR). split; [now exists sR|].
      pose proof (simSliceBytes_sound 160 dir q rb b lb sL sR) as Hs.
      now rewrite Es in Hs.
Qed.

Lemma returnWall_sound inv base (Hb : BottomSound inv base) depth :
  CallSound inv (returnWall base depth).
Proof.
  induction depth as [|d IH]; intros [slices i] q t Ht;
    cbn [returnWall]; apply memoCall_sound; [exact Ht| |exact Ht|];
    intros t0 Ht0; destruct slices as [|[|b rb] slices]; try exact (conj Ht0 I).
  1,2: destruct (base i q) as [[j p]|] eqn:E; split; try exact Ht0; try exact I;
    intros sL sR H; exact (Hb i q j p sL sR E H).
  pose proof (returnSlice_sound inv _ IH 360 (slices,i) true q rb b [] t0 Ht0) as H.
  destruct (returnSlice (returnWall base d) 360 (slices,i) true q rb b [] t0)
    as [[v|] t']; [|exact H].
  destruct H as [Ht' Hslice]. split; [exact Ht'|].
  intros sL sR [s [Hw ->]]. exact (Hslice sL s Hw).
Qed.

Lemma wallCall_sound inv base : BottomSound inv base -> CallSound inv (wallCall base).
Proof. intros Hb w. exact (returnWall_sound inv base Hb (length (fst w)) w). Qed.

Definition outcome inv target ans (cfg : Q * tape) :=
  match ans with
  | None => halts tm cfg
  | Some w =>
    match target with
    | Some (p,bs) =>
      exists sR, wallTape inv w sR /\ (cfg -->* bytesToLeft bs 0inf <{{p}} sR)
    | None => False
    end
  end.

Definition runSound inv target cfg (p : RunResult) :=
  let '(ret,t') := p in
  memoValid inv t' /\ match ret with
  | Some ans => outcome inv target ans cfg
  | None => True
  end.

Lemma runSound_step inv target cfg cfg' ret :
  cfg -->* cfg' -> runSound inv target cfg' ret -> runSound inv target cfg ret.
Proof.
  intros Hstep. destruct ret as [[[w|]|] t]; intros [Ht H]; split; try assumption.
  - destruct target as [[p bs]|]; [|contradiction].
    destruct H as [s [Hs Hrc]]. exists s; split; [exact Hs|exact (ev_trans _ _ _ Hstep Hrc)].
  - exact (evstep_halts _ _ Hstep H).
Qed.

Lemma hits_sound target dir q rb b lb sR :
  hits target dir q rb b lb = true ->
  exists p bs, target = Some (p,bs) /\
    byteEntryCfg dir q b (bytesToLeft lb 0inf) (bytesToRight rb sR) =
    (bytesToLeft bs 0inf <{{p}} sR).
Proof.
  destruct target as [[p bs]|], dir, rb; try discriminate.
  cbn [hits]. intros H. apply andb_prop in H as [Hq Hb].
  apply qEqb_eq in Hq. subst q.
  exists p, bs. split; [reflexivity|].
  exact (f_equal (fun sL => sL <{{p}} sR) (bytesEqZeroPad_sound _ _ Hb)).
Qed.

Local Opaque b8EntryT simSliceBytes wallCall.

Lemma runTail_sound inv call (Hcall : CallSound inv call) target fuel :
  forall w dir q rb b lb t sR, memoValid inv t -> wallTape inv w sR ->
    runSound inv target (byteEntryCfg dir q b (bytesToLeft lb 0inf) (bytesToRight rb sR))
      (runTail call target fuel w dir q rb b lb t).
Proof.
  induction fuel as [|f IH]; intros w dir q rb b lb t sR Ht Hw.
  - exact (conj Ht I).
  - cbn [runTail]. destruct (hits target dir q rb b lb) eqn:Eh.
    + destruct (hits_sound _ _ _ _ _ _ sR Eh) as [p [bs [-> ->]]].
      split; [exact Ht|]. exists sR; split; [exact Hw|apply evstep_refl].
    + pose proof (b8Entry_sound dir q b (bytesToLeft lb 0inf) (bytesToRight rb sR)) as Hb.
      destruct (b8EntryT theB8Table dir q b) as [p a|p a| |]; try exact (conj Ht I).
      * destruct rb as [|c r].
        -- pose proof (Hcall w p t Ht) as H.
           destruct (call w p t) as [[[w' p']|] t']; [|exact H].
           destruct H as [Ht' Hr].
           destruct (Hr (bytesToLeft (a::lb) 0inf) sR Hw) as [sR' [Hw' Hret]].
           exact (runSound_step _ _ _ _ _ (ev_trans _ _ _ Hb Hret)
             (IH w' false p' [] a lb t' sR' Ht' Hw')).
        -- exact (runSound_step _ _ _ _ _ Hb (IH w true p r c (a::lb) t sR Ht Hw)).
      * pose proof (popByte_spec lb) as E.
        destruct (popByte lb) as [c l]. cbn [fst snd] in E.
        pose proof (IH w false p (a::rb) c l t sR Ht Hw) as H.
        cbn [byteEntryCfg] in H. rewrite <- E in H.
        exact (runSound_step _ _ _ _ _ Hb H).
      * exact (conj Ht Hb).
Qed.

Local Opaque runTail.

Lemma runCuts_sound inv call (Hcall : CallSound inv call) target fuel :
  forall w q b lb rest widths t sR, memoValid inv t -> wallTape inv w sR ->
    runSound inv target (byteEntryCfg false q b (bytesToLeft lb (bytesToLeft rest 0inf)) sR)
      (runCuts call target fuel w q b lb rest widths t).
Proof.
  induction fuel as [|f IH]; intros w q b lb rest widths t sR Ht Hw.
  - exact (conj Ht I).
  - cbn [runCuts].
    pose proof (simSliceBytes_sound 160 false q [] b lb (bytesToLeft rest 0inf) sR) as Hs.
    destruct (simSliceBytes theB8Table 160 false q [] b lb) as [p a l|p out| |];
      try exact (conj Ht I).
    + pose proof (Hcall w p t Ht) as H.
      destruct (call w p t) as [[[w' p']|] t']; [|exact H].
      destruct H as [Ht' Hr].
      destruct (Hr (bytesToLeft (a::l) (bytesToLeft rest 0inf)) sR Hw) as [sR' [Hw' Hret]].
      exact (runSound_step _ _ _ _ _ (ev_trans _ _ _ Hs Hret)
        (IH w' p' a l rest widths t' sR' Ht' Hw')).
    + assert (Hw' : wallTape inv (addSlice out w) (bytesToRight out sR)) by now exists sR.
      destruct widths as [|n ns].
      * pose proof (popByte_spec rest) as E.
        destruct (popByte rest) as [c l]. cbn [fst snd] in E.
        pose proof (runTail_sound inv call Hcall target 1100
          _ false p [] c l t _ Ht Hw') as H.
        cbn [byteEntryCfg bytesToRight] in H. rewrite <- E in H.
        exact (runSound_step _ _ _ _ _ Hs H).
      * pose proof (popNBytes_spec n rest) as E.
        destruct (popNBytes n rest) as [[|c l] rst]; [exact (conj Ht I)|].
        cbn [fst snd bytesToLeft] in E.
        pose proof (IH _ p c l rst ns t _ Ht Hw') as H.
        cbn [byteEntryCfg] in H. rewrite <- E in H.
        exact (runSound_step _ _ _ _ _ Hs H).
    + exact (conj Ht Hs).
Qed.

Local Opaque runCuts.

Lemma runStage_sound inv base (Hb : BottomSound inv base) i q bs widths target sR :
  inv i sR -> runSound inv target (bytesToLeft bs 0inf <{{q}} sR)
    (runStage base i q bs widths target).
Proof.
  intros Hw. unfold runStage. destruct widths as [|n ns]; [exact (conj (memo_empty _) I)|].
  pose proof (popNBytes_spec n bs) as E.
  destruct (popNBytes n bs) as [[|b lb] rest]; [exact (conj (memo_empty _) I)|].
  cbn [fst snd bytesToLeft] in E. rewrite E.
  exact (runCuts_sound inv _ (wallCall_sound inv base Hb) target 1100
    ([],i) q b lb rest ns _ sR (memo_empty inv) Hw).
Qed.

Local Transparent b8EntryT simSliceBytes wallCall runTail runCuts.

Lemma crystalCall_sound :
  BottomSound (fun i sR => exists c, sR = bitsToSide (crysBaseBits i) (crysTape (crysBasePh i) c))
    crystalCall.
Proof.
  intros i q j p sL sR H [c ->]. unfold crystalCall in H.
  destruct (crysBaseBits i) as [|b bs]; [discriminate|].
  destruct (simCrysWall 120 (crysBasePh i) q [b] bs) as [[[ph q'] rb]|] eqn:E;
    [|discriminate].
  destruct (find (crystalPairEq ph rb) _) as [k|] eqn:Ek; [|discriminate].
  injection H as <- <-.
  apply find_some in Ek as [_ Hk]. unfold crystalPairEq in Hk.
  apply andb_prop in Hk as [Hph Hb].
  apply phaseEqb_eq in Hph; apply boolListEqb_eq in Hb; subst ph rb.
  destruct (simCrysWall_sound _ _ _ _ _ _ _ _ E c sL) as [c' Hrc].
  eexists. split; [now exists c'|exact Hrc].
Qed.

Lemma inWalls_spec ws w : inWalls ws w = true <-> In w ws.
Proof.
  unfold inWalls. rewrite existsb_exists. split.
  - intros [x [Hx E]].
    apply (proj2 (Bool.reflect_iff _ _ (WallKey.K_eq_spec w x))) in E. now subst.
  - intros Hw. exists w; split; [exact Hw|].
    apply (proj1 (Bool.reflect_iff _ _ (WallKey.K_eq_spec w w))). reflexivity.
Qed.

Lemma nextWalls_sound inv call (Hcall : CallSound inv call) replies w t :
  memoValid inv t ->
  let '(ret,t') := nextWalls call replies w t in
  memoValid inv t' /\ match ret with
    | None => True
    | Some out =>
      forall q p, In (q,p) replies ->
        exists w', In w' out /\ returnSpec inv (w,q) (w',p)
    end.
Proof.
  revert t. induction replies as [|[q p] rs IH]; intros t Ht.
  - split; [exact Ht|contradiction].
  - cbn [nextWalls].
    pose proof (Hcall w q t Ht) as H.
    destruct (call w q t) as [[[w' p']|] t']; [|exact H].
    destruct H as [Ht' Hr].
    destruct (qEqb p p') eqn:E; [|exact (conj Ht' I)].
    apply qEqb_eq in E; subst p'.
    specialize (IH t' Ht').
    destruct (nextWalls call rs w t') as [[out|] t'']; [|exact IH].
    destruct IH as [Ht'' Hrs]. split; [exact Ht''|].
    intros q0 p0 [E|Hin].
    + inversion E; subst. exists w'; split; [now left|exact Hr].
    + destruct (Hrs _ _ Hin) as [v [Hv Hret]]. exists v; split; [now right|exact Hret].
Qed.

Lemma collectFamily_memo inv call (Hcall : CallSound inv call) rs fuel :
  forall todo seen t, memoValid inv t ->
    memoValid inv (snd (collectFamily call rs fuel todo seen t)).
Proof.
  induction fuel as [|f IH]; intros todo seen t Ht; [exact Ht|].
  cbn [collectFamily]. destruct todo as [|w ws]; [exact Ht|].
  destruct (inWalls seen w); [now apply IH|].
  pose proof (nextWalls_sound inv call Hcall rs w t Ht) as H.
  destruct (nextWalls call rs w t) as [[out|] t']; destruct H;
    [now apply IH|assumption].
Qed.

Lemma auditFamily_sound inv call (Hcall : CallSound inv call) rs family todo t :
  memoValid inv t -> auditFamily call rs family todo t = true ->
  forall w q p, In w todo -> In (q,p) rs ->
    exists w', In w' family /\ returnSpec inv (w,q) (w',p).
Proof.
  revert t. induction todo as [|x xs IH]; intros t Ht Ha w q p Hin Hrs; [contradiction|].
  cbn [auditFamily] in Ha.
  pose proof (nextWalls_sound inv call Hcall rs x t Ht) as H.
  destruct (nextWalls call rs x t) as [[out|] t']; [|discriminate].
  destruct H as [Ht' H]. apply andb_prop in Ha as [Ha Hr].
  destruct Hin as [->|Hin]; [|exact (IH t' Ht' Hr w q p Hin Hrs)].
  destruct (H q p Hrs) as [w' [Hw' Hret]].
  apply forallb_forall with (x := w') in Ha; [|exact Hw'].
  exists w'; split; [now apply inWalls_spec|exact Hret].
Qed.

Definition FamilyBottom inv family : Bottom :=
  fun _ sR => exists w, In w family /\ wallTape inv w sR.

Local Opaque wallCall collectFamily auditFamily.

Lemma closed_sound inv base (Hb : BottomSound inv base) rs w t family sR :
  memoValid inv t -> wallTape inv w sR -> closed base rs w t = Some family ->
  FamilyBottom inv family 0%N sR /\ BottomSound (FamilyBottom inv family) (repliesCall rs).
Proof.
  intros Ht Hw Hcl. unfold closed in Hcl.
  pose proof (wallCall_sound inv base Hb) as Hcall.
  pose proof (collectFamily_memo inv _ Hcall rs 128 [w] [] t Ht) as Ht'.
  destruct (collectFamily (wallCall base) rs 128 [w] [] t) as [[ws|] t']; [|discriminate].
  destruct (inWalls ws w && auditFamily (wallCall base) rs ws ws t') eqn:E; [|discriminate].
  injection Hcl as <-. apply andb_prop in E as [Hin Hcl].
  split.
  - exists w. split; [now apply inWalls_spec|exact Hw].
  - intros i q j p sL s E [x [Hx Htape]]. unfold repliesCall in E.
    destruct (find (fun e => qEqb q (fst e)) rs) as [[q' p']|] eqn:Ef; [|discriminate].
    injection E as <- <-.
    apply find_some in Ef as [Hrs E]. cbn [fst] in E. apply qEqb_eq in E. subst q'.
    destruct (auditFamily_sound inv _ Hcall rs ws ws t' Ht' Hcl x q p' Hx Hrs)
      as [v [Hv Hret]].
    destruct (Hret sL s Htape) as [s' [Hv' Hr]].
    exists s'; split; [now exists v|exact Hr].
Qed.

Local Opaque runStage closed stageInitQ stageInitBytes.

Lemma executeStages_sound widths :
  forall replies s inv base i sR, BottomSound inv base -> inv i sR ->
    snd (executeStages widths replies s base i) = true ->
    halts tm (bytesToLeft (stageInitBytes s) 0inf <{{stageInitQ s}} sR).
Proof.
  induction widths as [|ns more IH]; intros replies s inv base i sR Hb Hw E;
    cbn [executeStages snd] in E; [discriminate|].
  destruct replies as [|rs later]; [discriminate|].
  set (target := match more with [] => None | _ => Some (entry (S s)) end) in *.
  pose proof (runStage_sound inv base Hb i (stageInitQ s) (stageInitBytes s) ns target sR Hw) as H.
  destruct (runStage base i (stageInitQ s) (stageInitBytes s) ns target) as [[[w|]|] t];
    try discriminate; destruct H as [Ht H]; [|exact H].
  destruct (closed base rs w t) as [family|] eqn:Ecl; [|discriminate].
  destruct more as [|cs more]; [contradiction|].
  destruct H as [sR' [Hw' Hreach]].
  destruct (closed_sound inv base Hb rs w t family sR' Ht Hw' Ecl) as [Hfam Hnext].
  exact (evstep_halts _ _ Hreach
    (IH later (S s) _ _ 0%N sR' Hnext Hfam E)).
Qed.

Local Transparent wallCall collectFamily auditFamily runStage closed stageInitQ stageInitBytes.
Local Transparent Cache.hmap_get Cache.hmap_set.

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
    phaseEqb ph' (crysBasePh 1%N) &&
    qEqb q' (stageInitQ 0%nat) &&
    boolListEqb rb' (crysBaseBits 1%N)
  | None => false
  end.

Lemma link1b_valid : checkLink1b = true.
Proof. vm_check_eq. Qed.

Lemma link1b_reaches :
  exists sR0, (exists c, sR0 = bitsToSide (crysBaseBits 1%N) (crysTape (crysBasePh 1%N) c)) /\
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
  exists (bitsToSide (crysBaseBits 1%N) (crysTape (crysBasePh 1%N) c2)).
  split; [exists c2; reflexivity |].
  exact (ev_trans _ _ _ H1 (ev_trans _ _ _ Hcb Hrc)).
Qed.

Local Opaque executeStages.

Lemma stageProgress_sound : snd stageProgress = true -> halts tm c0.
Proof.
  unfold stageProgress. intros E. destruct link1b_reaches as [sR [Hw H]].
  exact (evstep_halts _ _ H (executeStages_sound stageWidths (tl stageReplies ++ [[]]) 0%nat
    _ crystalCall 1%N sR crystalCall_sound Hw E)).
Qed.

Local Transparent executeStages.

Theorem halt : halts tm c0.
Proof. apply stageProgress_sound. vm_check_eq. Qed.

End TM1.
