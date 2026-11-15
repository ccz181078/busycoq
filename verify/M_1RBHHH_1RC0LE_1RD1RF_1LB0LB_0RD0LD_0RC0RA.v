(* 1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA halts. *)

From BusyCoq Require Import Individual62 BigUint.
From Coq Require Import List Bool PeanoNat Lia ZArith ZifyNat String.
From Coq Require Uint63.
Import ListNotations.

Open Scope list_scope.
Open Scope nat_scope.

Definition tm : TM :=
  TM_from_str "1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA".

Module M566.

Local Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Lemma etrans {c1 c2 c3 : Q * tape} :
  c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma evstep_eq {c1 c1' c2 c2' : Q * tape} :
  c1' -->* c2' -> c1 = c1' -> c2' = c2 -> c1 -->* c2.
Proof. intros H -> <-. exact H. Qed.

Lemma refl_eq {c1 c2 : Q * tape} :
  c1 = c2 -> c1 -->* c2.
Proof. intros ->. apply evstep_refl. Qed.

Lemma halts_eq {c1 c1' : Q * tape} :
  c1 = c1' -> halts tm c1' -> halts tm c1.
Proof. intros -> H. exact H. Qed.

(* ========================================================================== *)
(* Layer 0: Reflective Local Symbolic Window Evaluator (runLocal)             *)
(* ========================================================================== *)

Record LocalCfg := mkLocal {
  lc_q : Q;
  lc_dir : dir;
  lc_l : list Sym;
  lc_r : list Sym
}.

Inductive LocalRes :=
  | LCont (lc : LocalCfg)
  | LHalt
  | LOob.

Definition consNorm (isBlank : bool) (w : Sym) (xs : list Sym) : list Sym :=
  match isBlank, xs, w with
  | true, [], S0 => []
  | _, _, _ => w :: xs
  end.

Lemma consNorm_spec (isBlank : bool) (w : Sym) (xs : list Sym) (rest : side) :
  (isBlank = true -> rest = const S0) ->
  consNorm isBlank w xs *> rest = w >> (xs *> rest).
Proof.
  intro hb. destruct isBlank.
  - destruct xs as [|x xs'].
    + destruct w; [cbn; rewrite (hb eq_refl); apply const_unfold | reflexivity].
    + reflexivity.
  - reflexivity.
Qed.

Definition popSym (isBlank : bool) (xs : list Sym) : option (Sym * list Sym) :=
  match xs with
  | b :: xt => Some (b, xt)
  | [] => if isBlank then Some (S0, []) else None
  end.

Lemma popSym_spec (isBlank : bool) (xs : list Sym) (rest : side) (h : Sym) (xt : list Sym) :
  (isBlank = true -> rest = const S0) ->
  popSym isBlank xs = Some (h, xt) ->
  xs *> rest = h >> (xt *> rest).
Proof.
  intros hb H. destruct xs as [|b xs']; cbn in H.
  - destruct isBlank; [|discriminate].
    inversion H; subst h xt.
    cbn. rewrite (hb eq_refl). apply const_unfold.
  - inversion H; subst h xt. reflexivity.
Qed.

Definition evalLocal (lc : LocalCfg) (lrest rrest : side) : Q * tape :=
  match lc_dir lc with
  | L => (lc_l lc *> lrest) <{{lc_q lc}} (lc_r lc *> rrest)
  | R => (lc_l lc *> lrest) {{lc_q lc}}> (lc_r lc *> rrest)
  end.

Definition localStep (blankL blankR : bool) (lc : LocalCfg) : LocalRes :=
  match lc_dir lc with
  | L =>
    match popSym blankL (lc_l lc) with
    | None => LOob
    | Some (h, lt) =>
      match tm (lc_q lc, h) with
      | None => LHalt
      | Some (w, L, nq) => LCont (mkLocal nq L lt (consNorm blankR w (lc_r lc)))
      | Some (w, R, nq) => LCont (mkLocal nq R (consNorm blankL w lt) (lc_r lc))
      end
    end
  | R =>
    match popSym blankR (lc_r lc) with
    | None => LOob
    | Some (h, rt) =>
      match tm (lc_q lc, h) with
      | None => LHalt
      | Some (w, L, nq) => LCont (mkLocal nq L (lc_l lc) (consNorm blankR w rt))
      | Some (w, R, nq) => LCont (mkLocal nq R (consNorm blankL w (lc_l lc)) rt)
      end
    end
  end.

Fixpoint runLocal (blankL blankR : bool) (n : nat) (lc : LocalCfg) : LocalRes :=
  match n with
  | 0 => LCont lc
  | S n' =>
    match localStep blankL blankR lc with
    | LCont lc' => runLocal blankL blankR n' lc'
    | LHalt => LHalt
    | LOob => LOob
    end
  end.

Lemma localStep_cont_sound (blankL blankR : bool) (lc lc' : LocalCfg)
  (lrest rrest : side) :
  localStep blankL blankR lc = LCont lc' ->
  (blankL = true -> lrest = const S0) ->
  (blankR = true -> rrest = const S0) ->
  evalLocal lc lrest rrest --> evalLocal lc' lrest rrest.
Proof.
  destruct lc as [q d l r].
  intros Hstep hL hR.
  destruct d; cbn [localStep lc_dir lc_q lc_l lc_r] in Hstep.
  - destruct (popSym blankL l) as [[h lt]|] eqn:Epop; [|discriminate].
    pose proof (popSym_spec blankL l lrest h lt hL Epop) as Hl.
    destruct (tm (q, h)) as [[[w d'] nq]|] eqn:Etm; [|discriminate].
    destruct d'; inversion Hstep; subst lc'; clear Hstep;
      cbn [evalLocal lc_dir lc_q lc_l lc_r]; rewrite Hl.
    + rewrite (consNorm_spec blankR w r rrest hR).
      exact (step_left Etm).
    + rewrite (consNorm_spec blankL w lt lrest hL).
      exact (step_right Etm).
  - destruct (popSym blankR r) as [[h rt]|] eqn:Epop; [|discriminate].
    pose proof (popSym_spec blankR r rrest h rt hR Epop) as Hr.
    destruct (tm (q, h)) as [[[w d'] nq]|] eqn:Etm; [|discriminate].
    destruct d'; inversion Hstep; subst lc'; clear Hstep;
      cbn [evalLocal lc_dir lc_q lc_l lc_r]; rewrite Hr.
    + rewrite (consNorm_spec blankR w rt rrest hR).
      exact (step_left Etm).
    + rewrite (consNorm_spec blankL w l lrest hL).
      exact (step_right Etm).
Qed.

Lemma localStep_halt_sound (blankL blankR : bool) (lc : LocalCfg)
  (lrest rrest : side) :
  localStep blankL blankR lc = LHalt ->
  (blankL = true -> lrest = const S0) ->
  (blankR = true -> rrest = const S0) ->
  halted tm (evalLocal lc lrest rrest).
Proof.
  destruct lc as [q d l r].
  intros Hstep hL hR.
  destruct d; cbn [localStep lc_dir lc_q lc_l lc_r] in Hstep.
  - destruct (popSym blankL l) as [[h lt]|] eqn:Epop; [|discriminate].
    pose proof (popSym_spec blankL l lrest h lt hL Epop) as Hl.
    destruct (tm (q, h)) as [[[w d'] nq]|] eqn:Etm; [destruct d'; discriminate|].
    cbn [evalLocal lc_dir lc_q lc_l lc_r]. rewrite Hl. exact Etm.
  - destruct (popSym blankR r) as [[h rt]|] eqn:Epop; [|discriminate].
    pose proof (popSym_spec blankR r rrest h rt hR Epop) as Hr.
    destruct (tm (q, h)) as [[[w d'] nq]|] eqn:Etm; [destruct d'; discriminate|].
    cbn [evalLocal lc_dir lc_q lc_l lc_r]. rewrite Hr. exact Etm.
Qed.

Lemma runLocal_cont_sound (blankL blankR : bool) (n : nat) :
  forall (lc lc' : LocalCfg) (lrest rrest : side),
    runLocal blankL blankR n lc = LCont lc' ->
    (blankL = true -> lrest = const S0) ->
    (blankR = true -> rrest = const S0) ->
    evalLocal lc lrest rrest -->* evalLocal lc' lrest rrest.
Proof.
  induction n as [|n IH]; intros lc lc' lrest rrest Hrun hL hR; cbn [runLocal] in Hrun.
  - inversion Hrun; subst lc'. apply evstep_refl.
  - destruct (localStep blankL blankR lc) as [lc1 | |] eqn:Estep; [|discriminate|discriminate].
    eapply evstep_step.
    + exact (localStep_cont_sound blankL blankR lc lc1 lrest rrest Estep hL hR).
    + exact (IH lc1 lc' lrest rrest Hrun hL hR).
Qed.

Lemma runLocal_halt_sound (blankL blankR : bool) (n : nat) :
  forall (lc : LocalCfg) (lrest rrest : side),
    runLocal blankL blankR n lc = LHalt ->
    (blankL = true -> lrest = const S0) ->
    (blankR = true -> rrest = const S0) ->
    halts tm (evalLocal lc lrest rrest).
Proof.
  induction n as [|n IH]; intros lc lrest rrest Hrun hL hR; cbn [runLocal] in Hrun.
  - discriminate.
  - destruct (localStep blankL blankR lc) as [lc1 | |] eqn:Estep; [| |discriminate].
    + eapply halts_step.
      * exact (IH lc1 lrest rrest Hrun hL hR).
      * exact (localStep_cont_sound blankL blankR lc lc1 lrest rrest Estep hL hR).
    + apply halted_halts.
      exact (localStep_halt_sound blankL blankR lc lrest rrest Estep hL hR).
Qed.

Ltac vm_refl :=
  lazymatch goal with
  | |- _ = ?rhs => vm_cast_no_check (eq_refl rhs)
  end.

Lemma runLocal_ff (n : nat) (q : Q) (d : dir) (l r : list Sym)
  (q' : Q) (d' : dir) (l' r' : list Sym) (lrest rrest : side) :
  runLocal false false n (mkLocal q d l r) = LCont (mkLocal q' d' l' r') ->
  evalLocal (mkLocal q d l r) lrest rrest -->*
  evalLocal (mkLocal q' d' l' r') lrest rrest.
Proof.
  intro H. apply (runLocal_cont_sound false false n _ _ lrest rrest H); discriminate.
Qed.

Lemma runLocal_tf (n : nat) (q : Q) (d : dir) (l r : list Sym)
  (q' : Q) (d' : dir) (l' r' : list Sym) (rrest : side) :
  runLocal true false n (mkLocal q d l r) = LCont (mkLocal q' d' l' r') ->
  evalLocal (mkLocal q d l r) (const S0) rrest -->*
  evalLocal (mkLocal q' d' l' r') (const S0) rrest.
Proof.
  intro H. apply (runLocal_cont_sound true false n _ _ (const S0) rrest H);
    [intro; reflexivity | discriminate].
Qed.

Lemma runLocal_ft (n : nat) (q : Q) (d : dir) (l r : list Sym)
  (q' : Q) (d' : dir) (l' r' : list Sym) (lrest : side) :
  runLocal false true n (mkLocal q d l r) = LCont (mkLocal q' d' l' r') ->
  evalLocal (mkLocal q d l r) lrest (const S0) -->*
  evalLocal (mkLocal q' d' l' r') lrest (const S0).
Proof.
  intro H. apply (runLocal_cont_sound false true n _ _ lrest (const S0) H);
    [discriminate | intro; reflexivity].
Qed.

Lemma runLocal_tt (n : nat) (q : Q) (d : dir) (l r : list Sym)
  (q' : Q) (d' : dir) (l' r' : list Sym) :
  runLocal true true n (mkLocal q d l r) = LCont (mkLocal q' d' l' r') ->
  evalLocal (mkLocal q d l r) (const S0) (const S0) -->*
  evalLocal (mkLocal q' d' l' r') (const S0) (const S0).
Proof.
  intro H. apply (runLocal_cont_sound true true n _ _ (const S0) (const S0) H);
    intro; reflexivity.
Qed.

Lemma runLocal_ff_halt (n : nat) (q : Q) (d : dir) (l r : list Sym)
  (lrest rrest : side) :
  runLocal false false n (mkLocal q d l r) = LHalt ->
  halts tm (evalLocal (mkLocal q d l r) lrest rrest).
Proof.
  intro H. apply (runLocal_halt_sound false false n _ lrest rrest H); discriminate.
Qed.

(* ========================================================================== *)
(* Layer 1: Macro Words, Tape Encodings, and Sweep / Turnaround Lemmas        *)
(* ========================================================================== *)

Inductive Delim :=
  | P1 | P2 | P3 | W1 | W2 | W3 | W4.

Definition Stack := list (BigUint * Delim).
Definition RevBs := list (bool * BigUint).

Definition L6 : list Sym := [S1; S1; S1; S1; S1; S0].
Definition L6_1 : list Sym := [S1; S1; S1; S1; S1; S1].
Definition L11 : list Sym := [S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S1].
Definition LSep (b : bool) : list Sym :=
  if b then [S1; S1; S1; S0; S1; S0; S1; S0; S1; S1; S1; S0]
       else [S1; S1; S1; S0; S1; S1; S1; S0].
Definition R6 : list Sym := [S1; S0; S0; S0; S0; S0].
Definition R9 : list Sym := [S1; S0; S0; S0; S0; S1; S0; S0; S0].
Definition SEP : list Sym := [S0; S0; S0; S0; S0; S0; S1; S0; S0; S0].
Definition RSep (b : bool) : list Sym :=
  if b then [S1; S0; S1; S0; S1; S0] else [S1; S0].

Definition bitsDelim (d : Delim) : list Sym :=
  match d with
  | P1 => [S1; S0; S1; S0; S0; S0; S0; S0]
  | P2 => [S1; S0; S0; S0; S0; S0; S1; S0]
  | P3 => [S1; S0; S0; S0; S0; S0; S1; S0; S1; S0; S1; S0]
  | W1 => [S1; S0; S1; S0; S1; S1; S0; S0; S0]
  | W2 => [S1; S1; S0; S0; S0]
  | W3 => [S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S0]
  | W4 => [S1; S0; S0]
  end.

Fixpoint encStack (st : Stack) : list Sym :=
  match st with
  | [] => []
  | (n, d) :: rest => R9 ^^ (BigUint.to_nat n) ++ bitsDelim d ++ encStack rest
  end.

Lemma encStack_app (a b : Stack) :
  encStack (a ++ b) = encStack a ++ encStack b.
Proof.
  induction a as [|[n d] r IH]; [reflexivity|].
  cbn [app encStack]. rewrite IH, !app_assoc. reflexivity.
Qed.

Fixpoint encChain (ch : RevBs) : list Sym :=
  match ch with
  | [] => []
  | (p, b) :: rest => encChain rest ++ RSep p ++ R6 ^^ (BigUint.to_nat b)
  end.

Fixpoint encLChain (ch : RevBs) : list Sym :=
  match ch with
  | [] => []
  | (p, b) :: rest => L6 ^^ (BigUint.to_nat b - 1) ++ LSep p ++ encLChain rest
  end.

Fixpoint AllPos (ch : RevBs) : Prop :=
  match ch with
  | [] => True
  | (_, b) :: rest => 1 <= BigUint.to_nat b /\ AllPos rest
  end.

Definition cfgB (l r : side) : Q * tape := l <{{B}} r.
Definition cfgC (l r : side) : Q * tape := l {{C}}> r.

Definition hubCfg (st : Stack) (tail : side) : Q * tape :=
  cfgC (L11 *> const S0) (([S0; S0; S0; S0; S0] ++ encStack st) *> tail).

Definition hub_halts (st : Stack) : Prop :=
  forall tail : side, halts tm (hubCfg st tail).

Lemma truncate_sound (k : nat) (st : Stack) :
  hub_halts (firstn k st) -> hub_halts st.
Proof.
  intros H tail. unfold hubCfg.
  rewrite <- (firstn_skipn k st), encStack_app, app_assoc, Str_app_assoc.
  apply H.
Qed.

(* Verified Local Micro-Lemmas via runLocal *)

Lemma rule_B_L6 (l r : side) :
  cfgB (L6 *> l) r -->* cfgB l (R6 *> r).
Proof.
  apply (runLocal_ff 6 B L L6 [] B L [] R6 l r).
  vm_refl.
Qed.

Lemma rule_B_LSep (p : bool) (l r : side) :
  cfgB (LSep p *> l) r -->* cfgB l ((R6 ++ RSep p) *> r).
Proof.
  destruct p.
  - apply (runLocal_ff 24 B L (LSep true) [] B L [] (R6 ++ RSep true) l r).
    vm_refl.
  - apply (runLocal_ff 12 B L (LSep false) [] B L [] (R6 ++ RSep false) l r).
    vm_refl.
Qed.

Lemma rule_B_wall (r : side) :
  cfgB (L6_1 *> const S0) (R6 *> r) -->*
  cfgC (([S1; S1; S0] ++ L6 ++ L6_1) *> const S0) r.
Proof.
  apply (runLocal_tf 45 B L L6_1 R6 C R ([S1; S1; S0] ++ L6 ++ L6_1) [] r).
  vm_refl.
Qed.

Lemma rule_C_R6 (l r : side) :
  cfgC ([S1; S1; S0] *> l) (R6 *> r) -->*
  cfgC (([S1; S1; S0] ++ L6) *> l) r.
Proof.
  apply (runLocal_ff 12 C R [S1; S1; S0] R6 C R ([S1; S1; S0] ++ L6) [] l r).
  vm_refl.
Qed.

Lemma rule_C_RSep_R6 (p : bool) (l r : side) :
  cfgC ([S1; S1; S0] *> l) ((RSep p ++ R6) *> r) -->*
  cfgC (([S1; S1; S0] ++ LSep p) *> l) r.
Proof.
  destruct p.
  - apply (runLocal_ff 18 C R [S1; S1; S0] (RSep true ++ R6) C R ([S1; S1; S0] ++ LSep true) [] l r).
    vm_refl.
  - apply (runLocal_ff 14 C R [S1; S1; S0] (RSep false ++ R6) C R ([S1; S1; S0] ++ LSep false) [] l r).
    vm_refl.
Qed.

Lemma local_C_R9 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 0) *> l) (R9 *> r) -->*
  cfgB l ((R6 ^^ 2 ++ []) *> r).
Proof.
  apply (runLocal_ff 20 C R ([S1; S1; S0] ++ L6 ^^ 0) R9 B L [] (R6 ^^ 2 ++ []) l r).
  vm_refl.
Qed.

Lemma local_C_P1_R9 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 1) *> l) ((bitsDelim P1 ++ R9) *> r) -->*
  cfgB l ((R6 ^^ 2 ++ (RSep false ++ R6 ^^ 2)) *> r).
Proof.
  apply (runLocal_ff 52 C R ([S1; S1; S0] ++ L6 ^^ 1) (bitsDelim P1 ++ R9)
    B L [] (R6 ^^ 2 ++ (RSep false ++ R6 ^^ 2)) l r).
  vm_refl.
Qed.

Lemma local_C_P2_R9 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 1) *> l) ((bitsDelim P2 ++ R9) *> r) -->*
  cfgB l ((R6 ^^ 3 ++ (RSep false ++ R6 ^^ 1)) *> r).
Proof.
  apply (runLocal_ff 52 C R ([S1; S1; S0] ++ L6 ^^ 1) (bitsDelim P2 ++ R9)
    B L [] (R6 ^^ 3 ++ (RSep false ++ R6 ^^ 1)) l r).
  vm_refl.
Qed.

Lemma local_C_P3_R9 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 1) *> l) ((bitsDelim P3 ++ R9) *> r) -->*
  cfgB l ((R6 ^^ 3 ++ (RSep true ++ R6 ^^ 1)) *> r).
Proof.
  apply (runLocal_ff 68 C R ([S1; S1; S0] ++ L6 ^^ 1) (bitsDelim P3 ++ R9)
    B L [] (R6 ^^ 3 ++ (RSep true ++ R6 ^^ 1)) l r).
  vm_refl.
Qed.

Lemma local_W1_h1 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 0) *> l) ((bitsDelim W1 ++ R9) *> r) -->*
  cfgB l ((R6 ^^ 1 ++ ([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0])) *> r).
Proof.
  apply (runLocal_ff 34 C R ([S1; S1; S0] ++ L6 ^^ 0) (bitsDelim W1 ++ R9)
    B L [] (R6 ^^ 1 ++ ([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0])) l r).
  vm_refl.
Qed.

Lemma local_W1_h2 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 1) *> l) (([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0]) *> r) -->*
  cfgB l ((R6 ^^ 1 ++ (SEP ++ bitsDelim P1)) *> r).
Proof.
  apply (runLocal_ff 88 C R ([S1; S1; S0] ++ L6 ^^ 1) ([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0])
    B L [] (R6 ^^ 1 ++ (SEP ++ bitsDelim P1)) l r).
  vm_refl.
Qed.

Lemma local_W2_h1 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 0) *> l) ((bitsDelim W2 ++ R9) *> r) -->*
  cfgB l ((R6 ^^ 2 ++ [S0; S1; S0; S0; S0]) *> r).
Proof.
  apply (runLocal_ff 18 C R ([S1; S1; S0] ++ L6 ^^ 0) (bitsDelim W2 ++ R9)
    B L [] (R6 ^^ 2 ++ [S0; S1; S0; S0; S0]) l r).
  vm_refl.
Qed.

Lemma local_W2_h2 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) ([S0; S1; S0; S0; S0] *> r) -->*
  cfgB l ((R6 ^^ 1 ++ ([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0])) *> r).
Proof.
  apply (runLocal_ff 50 C R ([S1; S1; S0] ++ L6 ^^ 2) [S0; S1; S0; S0; S0]
    B L [] (R6 ^^ 1 ++ ([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0])) l r).
  vm_refl.
Qed.

Lemma local_W2_h3 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) (([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0]) *> r) -->*
  cfgB l ((R6 ^^ 1 ++ (SEP ++ bitsDelim W3)) *> r).
Proof.
  apply (runLocal_ff 50 C R ([S1; S1; S0] ++ L6 ^^ 2) ([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0])
    B L [] (R6 ^^ 1 ++ (SEP ++ bitsDelim W3)) l r).
  vm_refl.
Qed.

Lemma local_W3_h1 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 0) *> l) (bitsDelim W3 *> r) -->*
  cfgB l ((R6 ^^ 2 ++ [S0; S0; S0; S0]) *> r).
Proof.
  apply (runLocal_ff 20 C R ([S1; S1; S0] ++ L6 ^^ 0) (bitsDelim W3)
    B L [] (R6 ^^ 2 ++ [S0; S0; S0; S0]) l r).
  vm_refl.
Qed.

Lemma local_W3_h2 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) ([S0; S0; S0; S0] *> r) -->*
  cfgB l ((R6 ^^ 1 ++ (SEP ++ bitsDelim W4)) *> r).
Proof.
  apply (runLocal_ff 50 C R ([S1; S1; S0] ++ L6 ^^ 2) [S0; S0; S0; S0]
    B L [] (R6 ^^ 1 ++ (SEP ++ bitsDelim W4)) l r).
  vm_refl.
Qed.

Lemma local_W4_halt (l r : side) :
  halts tm (cfgC ([S1; S1; S0] *> l) ((bitsDelim W4 ++ R9 ++ [S1]) *> r)).
Proof.
  apply (runLocal_ff_halt 31 C R [S1; S1; S0] (bitsDelim W4 ++ R9 ++ [S1]) l r).
  vm_refl.
Qed.

Lemma local_B2_step (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) (SEP *> r) -->*
  cfgB l ((R6 ^^ 1 ++ (SEP ++ R9)) *> r).
Proof.
  apply (runLocal_ff 50 C R ([S1; S1; S0] ++ L6 ^^ 2) SEP
    B L [] (R6 ^^ 1 ++ (SEP ++ R9)) l r).
  vm_refl.
Qed.

Lemma local_B2_rem0 (p : bool) (l r : side) :
  cfgC (([S1; S1; S0] ++ LSep p ++ L6 ^^ 2) *> l) (SEP *> r) -->*
  cfgB l ((R6 ++ SEP ++ bitsDelim (if p then P3 else P2) ++ R9) *> r).
Proof.
  destruct p.
  - apply (runLocal_ff 84 C R ([S1; S1; S0] ++ LSep true ++ L6 ^^ 2) SEP
      B L [] (R6 ++ SEP ++ bitsDelim P3 ++ R9) l r).
    vm_refl.
  - apply (runLocal_ff 62 C R ([S1; S1; S0] ++ LSep false ++ L6 ^^ 2) SEP
      B L [] (R6 ++ SEP ++ bitsDelim P2 ++ R9) l r).
    vm_refl.
Qed.

Lemma local_B2_rem1_S1_h1 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ++ LSep false ++ L6 ^^ 2) *> l) (SEP *> r) -->*
  cfgB l ((R6 ^^ 4 ++ [S0; S0; S1; S0; S0; S0] ++ R9) *> r).
Proof.
  apply (runLocal_ff 68 C R ([S1; S1; S0] ++ L6 ++ LSep false ++ L6 ^^ 2) SEP
    B L [] (R6 ^^ 4 ++ [S0; S0; S1; S0; S0; S0] ++ R9) l r).
  vm_refl.
Qed.

Lemma local_B2_rem1_S1_h2 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) ([S0; S0; S1; S0; S0; S0] *> r) -->*
  cfgB l ((R6 ^^ 1 ++ (SEP ++ bitsDelim W2)) *> r).
Proof.
  apply (runLocal_ff 50 C R ([S1; S1; S0] ++ L6 ^^ 2) [S0; S0; S1; S0; S0; S0]
    B L [] (R6 ^^ 1 ++ (SEP ++ bitsDelim W2)) l r).
  vm_refl.
Qed.

Lemma local_B2_rem1_S3_h1 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ++ LSep true ++ L6 ^^ 2) *> l) (SEP *> r) -->*
  cfgB l ((R6 ^^ 3 ++ [S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0] ++ R9) *> r).
Proof.
  apply (runLocal_ff 80 C R ([S1; S1; S0] ++ L6 ++ LSep true ++ L6 ^^ 2) SEP
    B L [] (R6 ^^ 3 ++ [S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0] ++ R9) l r).
  vm_refl.
Qed.

Lemma local_B2_rem1_S3_h2 (l r : side) :
  cfgC (([S1; S1; S0] ++ L6 ^^ 2) *> l) (([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) *> r) -->*
  cfgB l ((R6 ^^ 2 ++ (SEP ++ bitsDelim W1)) *> r).
Proof.
  apply (runLocal_ff 94 C R ([S1; S1; S0] ++ L6 ^^ 2) ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0])
    B L [] (R6 ^^ 2 ++ (SEP ++ bitsDelim W1)) l r).
  vm_refl.
Qed.

Lemma rule_hub_exit (r : side) :
  cfgB (L6_1 *> const S0) ((R6 ++ SEP) *> r) -->*
  cfgC (L11 *> const S0) (([S0; S0; S0; S0; S0] ++ R9) *> r).
Proof.
  apply (runLocal_tf 81 B L L6_1 (R6 ++ SEP) C R L11 ([S0; S0; S0; S0; S0] ++ R9) r).
  vm_refl.
Qed.

Lemma rule_hub_entry (r : side) :
  cfgC (L11 *> const S0) ([S0; S0; S0; S0; S0] *> r) -->*
  cfgB (L6_1 *> const S0) ((R6 ++ RSep true ++ R6) *> r).
Proof.
  apply (runLocal_tf 156 C R L11 [S0; S0; S0; S0; S0] B L L6_1 (R6 ++ RSep true ++ R6) r).
  vm_refl.
Qed.

Lemma local_hit7_h1 (l : side) :
  cfgC (([S1; S1; S0] ++ LSep true ++ L6 ^^ 2) *> l) ([S1; S0; S1; S0; S1] *> const S0) -->*
  cfgB l ((R6 ^^ 3 ++ ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) ++ [S1; S0; S1; S0; S1]) *> const S0).
Proof.
  apply (runLocal_ft 118 C R ([S1; S1; S0] ++ LSep true ++ L6 ^^ 2) [S1; S0; S1; S0; S1]
    B L [] (R6 ^^ 3 ++ ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) ++ [S1; S0; S1; S0; S1]) l).
  vm_refl.
Qed.

Lemma R9_2_split :
  R9 ^^ 2 = R9 ++ [S1] ++ [S0; S0; S0; S0; S1; S0; S0; S0].
Proof. reflexivity. Qed.

(* Tape power normalization lemmas *)

Lemma lpow_0 (xs : list Sym) : xs ^^ 0 = [].
Proof. reflexivity. Qed.

Lemma lpow_1 (xs : list Sym) : xs ^^ 1 = xs.
Proof. cbn. apply app_nil_r. Qed.

Lemma lpow_S_l (xs : list Sym) (n : nat) : xs ^^ (S n) = xs ++ xs ^^ n.
Proof. reflexivity. Qed.

Lemma lpow_S_r (xs : list Sym) (n : nat) : xs ^^ (S n) = xs ^^ n ++ xs.
Proof. cbn. symmetry. apply lpow_shift. Qed.

Lemma Str_lpow_0 (xs : list Sym) (r : side) : xs ^^ 0 *> r = r.
Proof. reflexivity. Qed.

Lemma Str_lpow_1 (xs : list Sym) (r : side) : xs ^^ 1 *> r = xs *> r.
Proof. rewrite lpow_1. reflexivity. Qed.

Lemma Str_lpow_add (xs : list Sym) (a b : nat) (r : side) :
  xs ^^ a *> xs ^^ b *> r = xs ^^ (a + b) *> r.
Proof. rewrite <- Str_app_assoc, <- lpow_add. reflexivity. Qed.

Lemma Str_lpow_1l (xs : list Sym) (b : nat) (r : side) :
  xs *> xs ^^ b *> r = xs ^^ (1 + b) *> r.
Proof. change (1 + b) with (S b). rewrite lpow_S_l, Str_app_assoc. reflexivity. Qed.

Lemma Str_lpow_1r (xs : list Sym) (a : nat) (r : side) :
  xs ^^ a *> xs *> r = xs ^^ (a + 1) *> r.
Proof. rewrite <- (lpow_1 xs) at 2. apply Str_lpow_add. Qed.

Lemma Str_lpow_11 (xs : list Sym) (r : side) :
  xs *> xs *> r = xs ^^ 2 *> r.
Proof. change (xs ^^ 2) with (xs ++ xs ++ []). rewrite app_nil_r, Str_app_assoc. reflexivity. Qed.

Lemma Str_lpow_cong (xs : list Sym) (a b : nat) (r1 r2 : side) :
  a = b -> r1 = r2 -> (xs ^^ a) *> r1 = (xs ^^ b) *> r2.
Proof. intros -> ->. reflexivity. Qed.

Lemma Str_lpow_cong_1l (xs : list Sym) (a : nat) (r1 r2 : side) :
  a = 1 -> r1 = r2 -> (xs ^^ a) *> r1 = xs *> r2.
Proof. intros -> ->. apply Str_lpow_1. Qed.

Lemma Str_lpow_cong_1r (xs : list Sym) (b : nat) (r1 r2 : side) :
  b = 1 -> r1 = r2 -> xs *> r1 = (xs ^^ b) *> r2.
Proof. intros -> ->. symmetry. apply Str_lpow_1. Qed.

Lemma Str_lpow_cong_0l (xs : list Sym) (a : nat) (r1 r2 : side) :
  a = 0 -> r1 = r2 -> (xs ^^ a) *> r1 = r2.
Proof. intros -> ->. reflexivity. Qed.

Lemma Str_lpow_cong_0r (xs : list Sym) (b : nat) (r1 r2 : side) :
  b = 0 -> r1 = r2 -> r1 = (xs ^^ b) *> r2.
Proof. intros -> ->. reflexivity. Qed.

Lemma cfgB_cong (l1 l2 r1 r2 : side) :
  l1 = l2 -> r1 = r2 -> cfgB l1 r1 = cfgB l2 r2.
Proof. intros -> ->. reflexivity. Qed.

Lemma cfgC_cong (l1 l2 r1 r2 : side) :
  l1 = l2 -> r1 = r2 -> cfgC l1 r1 = cfgC l2 r2.
Proof. intros -> ->. reflexivity. Qed.

Local Opaque cfgB cfgC lpow L6 L6_1 L11 LSep R6 R9 SEP RSep bitsDelim.

Ltac progress_cbn :=
  lazymatch goal with
  | |- ?g =>
    cbn [Str_app app encChain encLChain];
    lazymatch goal with
    | |- ?g' => tryif constr_eq g g' then fail else idtac
    end
  end.

Ltac step_norm1 :=
  match goal with
  | |- context [ (?xs ++ ?ys) *> ?zs ] => rewrite (Str_app_assoc xs ys zs)
  | |- context [ (?xs ^^ 0) *> ?zs ] => rewrite (Str_lpow_0 xs zs)
  | |- context [ ?xs ^^ 0 ] => rewrite (lpow_0 xs)
  | |- _ => progress_cbn
  end.

Ltac step_norm2 :=
  match goal with
  | |- context [ (?xs ^^ ?a) *> (?xs ^^ ?b) *> ?zs ] => rewrite (Str_lpow_add xs a b zs)
  | |- context [ ?xs *> (?xs ^^ ?b) *> ?zs ] => rewrite (Str_lpow_1l xs b zs)
  | |- context [ (?xs ^^ ?a) *> ?xs *> ?zs ] => rewrite (Str_lpow_1r xs a zs)
  | |- context [ ?xs *> ?xs *> ?zs ] => rewrite (Str_lpow_11 xs zs)
  end.

Ltac norm_tape :=
  unfold hubCfg;
  change sym with Sym in *;
  repeat step_norm1;
  repeat step_norm2.

Ltac step_side_eq :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- ?l = ?r =>
    tryif is_evar l then reflexivity else
    tryif is_evar r then reflexivity else
    lazymatch goal with
    | |- Cons ?s ?r1 = Cons ?s ?r2 =>
        apply (f_equal (Cons s))
    | |- (?xs ^^ ?a) *> ?r1 = (?xs ^^ ?b) *> ?r2 =>
        apply Str_lpow_cong; [lia |]
    | |- (?xs ^^ ?a) *> ?r1 = ?xs *> ?r2 =>
        apply Str_lpow_cong_1l; [lia |]
    | |- ?xs *> ?r1 = (?xs ^^ ?b) *> ?r2 =>
        apply Str_lpow_cong_1r; [lia |]
    | |- (?xs ^^ ?a) *> ?r1 = ?r2 =>
        apply Str_lpow_cong_0l; [lia |]
    | |- ?r1 = (?xs ^^ ?b) *> ?r2 =>
        apply Str_lpow_cong_0r; [lia |]
    | |- ?u *> ?r1 = ?u *> ?r2 =>
        apply (f_equal (Str_app u))
    end
  end.

Ltac tape_eq :=
  norm_tape;
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- cfgB _ _ = cfgB _ _ => apply cfgB_cong; [repeat step_side_eq | repeat step_side_eq]
  | |- cfgC _ _ = cfgC _ _ => apply cfgC_cong; [repeat step_side_eq | repeat step_side_eq]
  | |- _ => repeat step_side_eq
  end.

(* Sweep and Round-Trip Building Blocks *)

Lemma rule_B_L6_pow (k : nat) :
  forall (l r : side),
    cfgB (L6 ^^ k *> l) r -->* cfgB l (R6 ^^ k *> r).
Proof.
  induction k as [|k IH]; intros l r.
  - apply refl_eq; tape_eq.
  - rewrite lpow_S_l, lpow_S_r, !Str_app_assoc.
    eapply etrans; [apply rule_B_L6 | apply IH].
Qed.

Lemma rule_C_R6_pow (k : nat) :
  forall (l r : side),
    cfgC ([S1; S1; S0] *> l) (R6 ^^ k *> r) -->*
    cfgC (([S1; S1; S0] ++ L6 ^^ k) *> l) r.
Proof.
  induction k as [|k IH]; intros l r.
  - apply refl_eq; tape_eq.
  - rewrite lpow_S_l, lpow_S_r, !Str_app_assoc.
    eapply etrans.
    + apply rule_C_R6.
    + eapply evstep_eq; [apply (IH (L6 *> l) r) | tape_eq | tape_eq].
Qed.

Lemma rule_C_chain (ch : RevBs) :
  AllPos ch ->
  forall (l r : side),
    cfgC ([S1; S1; S0] *> l) (encChain ch *> r) -->*
    cfgC (([S1; S1; S0] ++ encLChain ch) *> l) r.
Proof.
  induction ch as [|[p b] rest IH]; intros hpos l r.
  - cbn [encChain encLChain].
    apply refl_eq; tape_eq.
  - destruct hpos as [hb hrest].
    cbn [encChain encLChain].
    eapply etrans.
    + eapply evstep_eq;
      [apply (IH hrest l ((RSep p ++ R6 ^^ (BigUint.to_nat b)) *> r)) | tape_eq | reflexivity].
    + eapply etrans.
      * assert (Hsplit : R6 ^^ (BigUint.to_nat b) = R6 ^^ 1 ++ R6 ^^ (BigUint.to_nat b - 1)).
        { rewrite <- lpow_add. f_equal. lia. }
        eapply evstep_eq;
        [apply (rule_C_RSep_R6 p (encLChain rest *> l) (R6 ^^ (BigUint.to_nat b - 1) *> r)) | rewrite Hsplit; tape_eq | reflexivity].
      * eapply evstep_eq;
        [apply (rule_C_R6_pow (BigUint.to_nat b - 1) (LSep p *> (encLChain rest *> l)) r) | tape_eq | tape_eq].
Qed.

Lemma rule_B_chain (ch : RevBs) :
  AllPos ch ->
  forall (l r : side),
    cfgB (encLChain ch *> l) (R6 *> r) -->*
    cfgB l ((R6 ++ encChain ch) *> r).
Proof.
  induction ch as [|[p b] rest IH]; intros hpos l r.
  - cbn [encChain encLChain].
    apply refl_eq; tape_eq.
  - destruct hpos as [hb hrest].
    cbn [encChain encLChain].
    eapply etrans.
    + eapply evstep_eq;
      [apply (rule_B_L6_pow (BigUint.to_nat b - 1) (LSep p *> (encLChain rest *> l)) (R6 *> r)) | tape_eq | reflexivity].
    + eapply etrans.
      * eapply evstep_eq;
        [apply (rule_B_LSep p (encLChain rest *> l) (R6 ^^ (BigUint.to_nat b) *> r)) | tape_eq | reflexivity].
      * eapply evstep_eq;
        [apply (IH hrest l ((RSep p ++ R6 ^^ (BigUint.to_nat b)) *> r)) | tape_eq | tape_eq].
Qed.

Lemma sweepOut_base (a : nat) (r : side) :
  cfgB (L6_1 *> const S0) (R6 ^^ (a + 1) *> r) -->*
  cfgC ([S1; S1; S0] *> (L6 ^^ (a + 1) *> (L6_1 *> const S0))) r.
Proof.
  eapply etrans.
  - assert (H : R6 ^^ (a + 1) = R6 ^^ 1 ++ R6 ^^ a) by (rewrite <- lpow_add; f_equal; lia).
    eapply evstep_eq;
    [apply (rule_B_wall (R6 ^^ a *> r)) | rewrite H; tape_eq | reflexivity].
  - eapply evstep_eq;
    [apply (rule_C_R6_pow a (L6 *> (L6_1 *> const S0)) r) | tape_eq | tape_eq].
Qed.

Lemma sweepOut_chain (a b : nat) (ch : RevBs) (p : bool) (r : side) :
  AllPos ch ->
  cfgB (L6_1 *> const S0) ((R6 ^^ (a + 1) ++ encChain ch ++ RSep p ++ R6 ^^ (b + 1)) *> r) -->*
  cfgC ([S1; S1; S0] *>
    (L6 ^^ b *> (LSep p *> (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0)))))) r.
Proof.
  intro hpos.
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_base a ((encChain ch ++ RSep p ++ R6 ^^ (b + 1)) *> r)) | tape_eq | reflexivity].
  - eapply etrans.
    + eapply evstep_eq;
      [apply (rule_C_chain ch hpos (L6 ^^ (a + 1) *> (L6_1 *> const S0))
        ((RSep p ++ R6 ^^ (b + 1)) *> r)) | tape_eq | reflexivity].
    + eapply etrans.
      * assert (H : R6 ^^ (b + 1) = R6 ^^ 1 ++ R6 ^^ b) by (rewrite <- lpow_add; f_equal; lia).
        eapply evstep_eq;
        [apply (rule_C_RSep_R6 p (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0)))
          (R6 ^^ b *> r)) | rewrite H; tape_eq | reflexivity].
      * eapply evstep_eq;
        [apply (rule_C_R6_pow b
          (LSep p *> (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0)))) r) | tape_eq | tape_eq].
Qed.

Lemma sweepBack_chain (a b : nat) (ch : RevBs) (p : bool) (r : side) :
  AllPos ch ->
  cfgB (L6 ^^ b *> (LSep p *> (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0))))) r -->*
  cfgB (L6_1 *> const S0) ((R6 ^^ (a + 2) ++ encChain ch ++ RSep p ++ R6 ^^ b) *> r).
Proof.
  intro hpos.
  eapply etrans.
  - apply (rule_B_L6_pow b (LSep p *> (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0)))) r).
  - eapply etrans.
    + apply (rule_B_LSep p (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0))) (R6 ^^ b *> r)).
    + eapply etrans.
      * eapply evstep_eq;
        [apply (rule_B_chain ch hpos (L6 ^^ (a + 1) *> (L6_1 *> const S0))
          ((RSep p ++ R6 ^^ b) *> r)) | tape_eq | reflexivity].
      * eapply evstep_eq;
        [apply (rule_B_L6_pow (a + 1) (L6_1 *> const S0)
          ((R6 ++ encChain ch ++ RSep p ++ R6 ^^ b) *> r)) | tape_eq | tape_eq].
Qed.

Lemma roundTrip (a b d e : nat) (ch : RevBs) (p : bool)
  (rhs rhs' : list Sym) (r : side) :
  AllPos ch ->
  (forall l : side,
    cfgC (([S1; S1; S0] ++ L6 ^^ d) *> l) (rhs *> r) -->*
    cfgB l ((R6 ^^ e ++ rhs') *> r)) ->
  cfgB (L6_1 *> const S0)
    ((R6 ^^ (a + 1) ++ encChain ch ++ RSep p ++ R6 ^^ (b + d + 1) ++ rhs) *> r) -->*
  cfgB (L6_1 *> const S0)
    ((R6 ^^ (a + 2) ++ encChain ch ++ RSep p ++ R6 ^^ (b + e) ++ rhs') *> r).
Proof.
  intros hpos hlocal.
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_chain a (b + d) ch p (rhs *> r) hpos) | tape_eq | reflexivity].
  - eapply etrans.
    + assert (Hsplit : L6 ^^ (b + d) = L6 ^^ d ++ L6 ^^ b)
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (hlocal (L6 ^^ b *> (LSep p *> (encLChain ch *> (L6 ^^ (a + 1) *> (L6_1 *> const S0)))))) | rewrite Hsplit; tape_eq | reflexivity].
    + eapply evstep_eq;
      [apply (sweepBack_chain a b ch p ((R6 ^^ e ++ rhs') *> r) hpos) | tape_eq | tape_eq].
Qed.

Lemma bounce1_pow (n : nat) :
  forall (a r6 : nat) (ch : RevBs) (p : bool) (r : side),
    1 <= r6 ->
    AllPos ch ->
    cfgB (L6_1 *> const S0)
      ((R6 ^^ (a + 1) ++ encChain ch ++ RSep p ++ R6 ^^ r6 ++ R9 ^^ n) *> r) -->*
    cfgB (L6_1 *> const S0)
      ((R6 ^^ (a + n + 1) ++ encChain ch ++ RSep p ++ R6 ^^ (r6 + n)) *> r).
Proof.
  induction n as [|n IH]; intros a r6 ch p r hr6 hpos.
  - apply refl_eq; tape_eq.
  - rewrite (lpow_S_l R9 n).
    eapply etrans.
    + eapply evstep_eq;
      [apply (roundTrip a (r6 - 1) 0 2 ch p R9 [] (R9 ^^ n *> r) hpos
        (fun l => local_C_R9 l (R9 ^^ n *> r))) | tape_eq | reflexivity].
    + eapply evstep_eq;
      [apply (IH (a + 1) (r6 + 1) ch p r); [lia | exact hpos] | tape_eq | tape_eq].
Qed.

Lemma bounce2_pow (q : nat) :
  forall (a b : nat) (ch : RevBs) (p : bool) (r : side),
    1 <= a -> 1 <= b -> AllPos ch ->
    cfgB (L6_1 *> const S0)
      ((R6 ^^ a ++ encChain ch ++ RSep p ++ R6 ^^ (b + 2 * q) ++ SEP) *> r) -->*
    cfgB (L6_1 *> const S0)
      ((R6 ^^ (a + q) ++ encChain ch ++ RSep p ++ R6 ^^ b ++ SEP ++ R9 ^^ q) *> r).
Proof.
  induction q as [|q IH]; intros a b ch p r ha hb hpos.
  - replace (b + 2 * 0) with b by lia. replace (a + 0) with a by lia.
    apply refl_eq; tape_eq.
  - eapply etrans.
    + eapply evstep_eq;
      [apply (roundTrip (a - 1) (b + 2 * q - 1) 2 1 ch p SEP (SEP ++ R9) r hpos
        (fun l => local_B2_step l r)) | tape_eq | reflexivity].
    + rewrite (lpow_S_r R9 q).
      eapply evstep_eq;
      [apply (IH (a + 1) b ch p (R9 *> r)); [lia | lia | exact hpos] | tape_eq | tape_eq].
Qed.

Lemma rule_B3_one (k : nat) (r : side) :
  cfgB (L6_1 *> const S0) ((R6 ^^ (k + 2) ++ SEP) *> r) -->*
  cfgB (L6_1 *> const S0) ((R6 ^^ (k + 1) ++ SEP ++ R9) *> r).
Proof.
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_base (k + 1) (SEP *> r)) | tape_eq | reflexivity].
  - eapply etrans.
    + assert (H : L6 ^^ (k + 1 + 1) = L6 ^^ 2 ++ L6 ^^ k)
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (local_B2_step (L6 ^^ k *> (L6_1 *> const S0)) r) | rewrite H; tape_eq | reflexivity].
    + eapply evstep_eq;
      [apply (rule_B_L6_pow k (L6_1 *> const S0) ((R6 ^^ 1 ++ (SEP ++ R9)) *> r)) | tape_eq | tape_eq].
Qed.

Lemma rule_B3_pow_exit_aux (k : nat) :
  forall (r : side),
    cfgB (L6_1 *> const S0) ((R6 ^^ (k + 1) ++ SEP) *> r) -->*
    cfgC (L11 *> const S0) (([S0; S0; S0; S0; S0] ++ R9 ^^ (k + 1)) *> r).
Proof.
  induction k as [|k IH]; intro r.
  - eapply evstep_eq; [apply rule_hub_exit | tape_eq | tape_eq].
  - eapply etrans.
    + eapply evstep_eq;
      [apply (rule_B3_one k r) | tape_eq | reflexivity].
    + assert (H : R9 ^^ (S k + 1) = R9 ^^ (k + 1) ++ R9 ^^ 1)
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (IH (R9 *> r)) | tape_eq | rewrite H; tape_eq].
Qed.

Lemma rule_B3_pow_exit (a : nat) (r : side) :
  1 <= a ->
  cfgB (L6_1 *> const S0) ((R6 ^^ a ++ SEP) *> r) -->*
  cfgC (L11 *> const S0) (([S0; S0; S0; S0; S0] ++ R9 ^^ a) *> r).
Proof.
  intro ha.
  eapply evstep_eq;
  [apply (rule_B3_pow_exit_aux (a - 1) r) | tape_eq | tape_eq].
Qed.

Lemma b2_exit_mid_rem0 (a : nat) (prevB : BigUint) (more2 : RevBs)
  (prevP isP3 : bool) (r : side) :
  1 <= a -> 3 <= BigUint.to_nat prevB -> AllPos more2 ->
  cfgB (L6_1 *> const S0)
    ((R6 ^^ a ++ encChain ((prevP, prevB) :: more2) ++ RSep isP3 ++ R6 ^^ 1 ++ SEP) *> r) -->*
  cfgB (L6_1 *> const S0)
    ((R6 ^^ (a + 1) ++ encChain more2 ++ RSep prevP ++ R6 ^^ (BigUint.to_nat prevB - 2) ++
      SEP ++ bitsDelim (if isP3 then P3 else P2) ++ R9) *> r).
Proof.
  intros ha hpb hpos.
  assert (hpos_m : AllPos ((prevP, prevB) :: more2)) by (split; [lia | exact hpos]).
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_chain (a - 1) 0 ((prevP, prevB) :: more2) isP3 (SEP *> r) hpos_m) | tape_eq | reflexivity].
  - eapply etrans.
    + cbn [encLChain].
      assert (H : L6 ^^ (BigUint.to_nat prevB - 1) = L6 ^^ 2 ++ L6 ^^ (BigUint.to_nat prevB - 3))
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (local_B2_rem0 isP3
        (L6 ^^ (BigUint.to_nat prevB - 3) *>
          (LSep prevP *> (encLChain more2 *> (L6 ^^ a *> (L6_1 *> const S0))))) r) | rewrite H; tape_eq | reflexivity].
    + eapply evstep_eq;
      [apply (sweepBack_chain (a - 1) (BigUint.to_nat prevB - 3) more2 prevP
        ((R6 ++ SEP ++ bitsDelim (if isP3 then P3 else P2) ++ R9) *> r) hpos) | tape_eq | tape_eq].
Qed.

Lemma b2_exit_mid_rem1 (a : nat) (prevB : BigUint) (more2 : RevBs)
  (prevP isP3 : bool) (r : side) :
  1 <= a -> 3 <= BigUint.to_nat prevB -> AllPos more2 ->
  cfgB (L6_1 *> const S0)
    ((R6 ^^ a ++ encChain ((prevP, prevB) :: more2) ++ RSep isP3 ++ R6 ^^ 2 ++ SEP) *> r) -->*
  cfgB (L6_1 *> const S0)
    ((R6 ^^ (a + 2) ++ encChain more2 ++ RSep prevP ++ R6 ^^ (BigUint.to_nat prevB - 1) ++
      SEP ++ bitsDelim (if isP3 then W1 else W2) ++ R9) *> r).
Proof.
  intros ha hpb hpos.
  assert (hpos_m : AllPos ((prevP, prevB) :: more2)) by (split; [lia | exact hpos]).
  assert (Hsplit : L6 ^^ (BigUint.to_nat prevB - 1) = L6 ^^ 2 ++ L6 ^^ (BigUint.to_nat prevB - 3))
    by (rewrite <- lpow_add; f_equal; lia).
  destruct isP3.
  - eapply etrans.
    + eapply evstep_eq;
      [apply (sweepOut_chain (a - 1) 1 ((prevP, prevB) :: more2) true (SEP *> r) hpos_m) | tape_eq | reflexivity].
    + eapply etrans.
      * cbn [encLChain].
        eapply evstep_eq;
        [apply (local_B2_rem1_S3_h1
          (L6 ^^ (BigUint.to_nat prevB - 3) *>
            (LSep prevP *> (encLChain more2 *> (L6 ^^ a *> (L6_1 *> const S0))))) r) | rewrite Hsplit; tape_eq | reflexivity].
      * eapply etrans.
        { eapply evstep_eq;
          [apply (sweepBack_chain (a - 1) (BigUint.to_nat prevB - 3) more2 prevP
            ((R6 ^^ 3 ++ [S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0] ++ R9) *> r) hpos) | tape_eq | reflexivity]. }
        { eapply evstep_eq;
          [apply (roundTrip a (BigUint.to_nat prevB - 3) 2 2 more2 prevP
            ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) (SEP ++ bitsDelim W1)
            (R9 *> r) hpos (fun l => local_B2_rem1_S3_h2 l (R9 *> r))) | tape_eq | tape_eq]. }
  - eapply etrans.
    + eapply evstep_eq;
      [apply (sweepOut_chain (a - 1) 1 ((prevP, prevB) :: more2) false (SEP *> r) hpos_m) | tape_eq | reflexivity].
    + eapply etrans.
      * cbn [encLChain].
        eapply evstep_eq;
        [apply (local_B2_rem1_S1_h1
          (L6 ^^ (BigUint.to_nat prevB - 3) *>
            (LSep prevP *> (encLChain more2 *> (L6 ^^ a *> (L6_1 *> const S0))))) r) | rewrite Hsplit; tape_eq | reflexivity].
      * eapply etrans.
        { eapply evstep_eq;
          [apply (sweepBack_chain (a - 1) (BigUint.to_nat prevB - 3) more2 prevP
            ((R6 ^^ 4 ++ [S0; S0; S1; S0; S0; S0] ++ R9) *> r) hpos) | tape_eq | reflexivity]. }
        { eapply evstep_eq;
          [apply (roundTrip a (BigUint.to_nat prevB - 2) 2 1 more2 prevP
            [S0; S0; S1; S0; S0; S0] (SEP ++ bitsDelim W2)
            (R9 *> r) hpos (fun l => local_B2_rem1_S1_h2 l (R9 *> r))) | tape_eq | tape_eq]. }
Qed.

Lemma b2_exit_top_rem0 (a : nat) (r : side) :
  2 <= a ->
  cfgB (L6_1 *> const S0) ((R6 ^^ a ++ RSep true ++ R6 ^^ 1 ++ SEP) *> r) -->*
  cfgB (L6_1 *> const S0) ((R6 ^^ (a - 1) ++ SEP ++ bitsDelim P3 ++ R9) *> r).
Proof.
  intro ha.
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_chain (a - 1) 0 [] true (SEP *> r) I) | cbn [encChain]; tape_eq | reflexivity].
  - eapply etrans.
    + cbn [encLChain].
      assert (H : L6 ^^ (a - 1 + 1) = L6 ^^ 2 ++ L6 ^^ (a - 2))
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (local_B2_rem0 true (L6 ^^ (a - 2) *> (L6_1 *> const S0)) r) | rewrite H; tape_eq | reflexivity].
    + eapply evstep_eq;
      [apply (rule_B_L6_pow (a - 2) (L6_1 *> const S0) ((R6 ++ SEP ++ bitsDelim P3 ++ R9) *> r)) | tape_eq | tape_eq].
Qed.

Lemma b2_exit_top_rem1 (a : nat) (r : side) :
  2 <= a ->
  cfgB (L6_1 *> const S0) ((R6 ^^ a ++ RSep true ++ R6 ^^ 2 ++ SEP) *> r) -->*
  cfgB (L6_1 *> const S0) ((R6 ^^ (a + 1) ++ SEP ++ bitsDelim W1 ++ R9) *> r).
Proof.
  intro ha.
  eapply etrans.
  - eapply evstep_eq;
    [apply (sweepOut_chain (a - 1) 1 [] true (SEP *> r) I) | cbn [encChain]; tape_eq | reflexivity].
  - eapply etrans.
    + cbn [encLChain].
      assert (H : L6 ^^ (a - 1 + 1) = L6 ^^ 2 ++ L6 ^^ (a - 2))
        by (rewrite <- lpow_add; f_equal; lia).
      eapply evstep_eq;
      [apply (local_B2_rem1_S3_h1 (L6 ^^ (a - 2) *> (L6_1 *> const S0)) r) | rewrite H; tape_eq | reflexivity].
    + eapply etrans.
      * eapply evstep_eq;
        [apply (rule_B_L6_pow (a - 2) (L6_1 *> const S0)
          ((R6 ^^ 3 ++ [S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0] ++ R9) *> r)) | tape_eq | reflexivity].
      * eapply etrans.
        { eapply evstep_eq;
          [apply (sweepOut_base a
            (([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) *> (R9 *> r))) | tape_eq | reflexivity]. }
        { eapply etrans.
          - assert (H2 : L6 ^^ (a + 1) = L6 ^^ 2 ++ L6 ^^ (a - 1))
              by (rewrite <- lpow_add; f_equal; lia).
            eapply evstep_eq;
            [apply (local_B2_rem1_S3_h2 (L6 ^^ (a - 1) *> (L6_1 *> const S0)) (R9 *> r)) | rewrite H2; tape_eq | reflexivity].
          - eapply evstep_eq;
            [apply (rule_B_L6_pow (a - 1) (L6_1 *> const S0)
              ((R6 ^^ 2 ++ (SEP ++ bitsDelim W1)) *> (R9 *> r))) | tape_eq | tape_eq]. }
Qed.

(* ========================================================================== *)
(* Layer 2: BigUint Stack Evaluator & Soundness                               *)
(* ========================================================================== *)

Fixpoint peel_n (k : nat) (x : BigUint) : option BigUint :=
  match k with
  | 0 => Some x
  | S k' =>
    match BigUint.pred x with
    | None => None
    | Some x1 => peel_n k' x1
    end
  end.

Lemma peel_n_some (k : nat) :
  forall (x y : BigUint),
    peel_n k x = Some y ->
    BigUint.to_nat x = k + BigUint.to_nat y.
Proof.
  induction k as [|k IH]; intros x y H; cbn [peel_n] in H.
  - inversion H; subst; reflexivity.
  - pose proof (inj_pred x) as Hp.
    destruct (BigUint.pred x) as [x1|]; [|discriminate].
    apply IH in H. lia.
Qed.

Fixpoint add_small (k : nat) (x : BigUint) : BigUint :=
  match k with
  | 0 => x
  | S k' => BigUint.succ (add_small k' x)
  end.

Lemma add_small_spec (k : nat) (x : BigUint) :
  BigUint.to_nat (add_small k x) = BigUint.to_nat x + k.
Proof.
  induction k as [|k IH]; cbn [add_small]; [lia | rewrite inj_succ, IH; lia].
Qed.

Definition bu2 : BigUint := Eval compute in (BigUint.of_nat 2).

Definition div2 (b : BigUint) : BigUint * bool :=
  let '(q, rem) := divmodc b (Uint63.of_Z 2%Z) in
  (q, is0 (Cons_simpl rem BigUintNil)).

Lemma div2_spec (b q : BigUint) (even : bool) :
  div2 b = (q, even) ->
  if even
  then BigUint.to_nat b = 2 * BigUint.to_nat q
  else BigUint.to_nat b = 2 * BigUint.to_nat q + 1.
Proof.
  unfold div2.
  destruct (divmodc b (Uint63.of_Z 2%Z)) as [q0 rem] eqn:E.
  intro H; inversion H; clear H; subst q0 even.
  assert (K : divmod_small b bu2 = Some (q, Cons_simpl rem BigUintNil)).
  { change ((let '(q', r') := divmodc b (Uint63.of_Z 2%Z) in
             Some (q', Cons_simpl r' BigUintNil)) =
            Some (q, Cons_simpl rem BigUintNil)).
    rewrite E. reflexivity. }
  apply inj_divmod_small in K.
  change (BigUint.to_nat bu2) with 2 in K.
  destruct K as [Heq Hlt].
  fold (Cons_simpl rem BigUintNil).
  destruct (inj_is0 (Cons_simpl rem BigUintNil)); lia.
Qed.

Inductive StepRes :=
  | Cont (st : Stack)
  | Halted
  | Stuck.

Fixpoint backStep (revBs : RevBs) (a : BigUint) (sub : nat)
  (nextD : Delim) (acc : Stack) : StepRes :=
  match revBs with
  | [] => Stuck
  | (isP3, bj) :: more =>
    match more with
    | [] =>
      if negb isP3 then Stuck else
      match peel_n (S sub) bj with
      | None => Stuck
      | Some bm1 =>
        let b' := BigUint.succ bm1 in
        let '(q, even) := div2 b' in
        let aq := BigUint.add a q in
        if even then
          match peel_n 3 aq with
          | None => Stuck
          | Some _ => Cont ((aq, W1) :: (q, nextD) :: acc)
          end
        else
          match peel_n 2 aq with
          | None => Stuck
          | Some aqm2 => Cont ((BigUint.succ aqm2, P3) :: (BigUint.succ q, nextD) :: acc)
          end
      end
    | (_, prevB) :: _ =>
      match peel_n (S sub) bj, peel_n 3 prevB with
      | Some bm1, Some _ =>
        let b' := BigUint.succ bm1 in
        let '(q, even) := div2 b' in
        let a' := BigUint.succ (BigUint.add a q) in
        if even then
          backStep more a' 1 (if isP3 then W1 else W2) ((q, nextD) :: acc)
        else
          backStep more a' 2 (if isP3 then P3 else P2) ((BigUint.succ q, nextD) :: acc)
      | _, _ => Stuck
      end
    end
  end.

Fixpoint scanStep (st : Stack) (aAcc : BigUint) (addNext : nat)
  (revBs : RevBs) (prevSep : bool) : StepRes :=
  match st with
  | [] => Stuck
  | (nk, d) :: rest =>
    let bk := add_small addNext nk in
    match d with
    | P1 =>
      match rest with
      | [] => Stuck
      | (na, _) :: _ =>
        match peel_n 2 bk, peel_n 1 na with
        | Some _, Some _ => scanStep rest (BigUint.add aAcc nk) 1 ((prevSep, bk) :: revBs) false
        | _, _ => Stuck
        end
      end
    | P2 =>
      match rest with
      | [] => Stuck
      | (na, _) :: _ =>
        match peel_n 2 bk, peel_n 1 na with
        | Some _, Some _ =>
          scanStep rest (BigUint.add aAcc nk) 0 ((prevSep, BigUint.succ bk) :: revBs) false
        | _, _ => Stuck
        end
      end
    | P3 =>
      match rest with
      | [] => Stuck
      | (na, _) :: _ =>
        match peel_n 2 bk, peel_n 1 na with
        | Some _, Some _ =>
          scanStep rest (BigUint.add aAcc nk) 0 ((prevSep, BigUint.succ bk) :: revBs) true
        | _, _ => Stuck
        end
      end
    | W1 =>
      match rest with
      | [] => Stuck
      | (na, da) :: tail =>
        match peel_n 2 bk, peel_n 1 na with
        | Some bkm2, Some na' =>
          let bk' := BigUint.succ bkm2 in
          let a' := add_small 3 (BigUint.add aAcc nk) in
          backStep ((prevSep, bk') :: revBs) a' 0 P1 ((na', da) :: tail)
        | _, _ => Stuck
        end
      end
    | W2 =>
      match rest with
      | [] => Stuck
      | (na, da) :: tail =>
        match peel_n 4 bk, peel_n 1 na with
        | Some bkm4, Some na' =>
          let bk' := BigUint.succ bkm4 in
          let a' := add_small 4 (BigUint.add aAcc nk) in
          backStep ((prevSep, bk') :: revBs) a' 0 W3 ((na', da) :: tail)
        | _, _ => Stuck
        end
      end
    | W3 =>
      match peel_n 2 bk with
      | Some bkm2 =>
        let bk' := BigUint.succ bkm2 in
        let a' := add_small 3 (BigUint.add aAcc nk) in
        backStep ((prevSep, bk') :: revBs) a' 0 W4 rest
      | None => Stuck
      end
    | W4 =>
      match rest with
      | [] => Stuck
      | (na, _) :: _ =>
        match peel_n 1 bk, peel_n 2 na with
        | Some _, Some _ => Halted
        | _, _ => Stuck
        end
      end
    end
  end.

Definition stackStep (st : Stack) : StepRes :=
  scanStep st BigUintNil 1 [] true.

Fixpoint run_steps (n : nat) (st : Stack) : StepRes :=
  match n with
  | 0 => Cont st
  | S n' =>
    match stackStep st with
    | Cont st' => run_steps n' st'
    | Halted => Halted
    | Stuck => Stuck
    end
  end.

Fixpoint run_blocks (blocks : nat) (st : Stack) : StepRes :=
  match blocks with
  | 0 => run_steps 63 st
  | S b' =>
    match run_steps 64 st with
    | Cont st' => run_blocks b' (firstn 24 st')
    | Halted => Halted
    | Stuck => Stuck
    end
  end.

Lemma backStep_sound (revBs : RevBs) :
  forall (isP3 : bool) (bj : BigUint) (more : RevBs),
    revBs = (isP3, bj) :: more ->
    forall (a : BigUint) (sub : nat) (nextD : Delim) (acc : Stack) (tail : side),
      AllPos more -> 1 <= BigUint.to_nat a ->
      match backStep revBs a sub nextD acc with
      | Cont out =>
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (BigUint.to_nat a) ++ encChain more ++ RSep isP3 ++
            R6 ^^ (BigUint.to_nat bj - sub) ++
            SEP ++ bitsDelim nextD ++ encStack acc) *> tail) -->*
        hubCfg out tail
      | Halted => False
      | Stuck => True
      end.
Proof.
  induction revBs as [|[isP30 bj0] more IH]; intros isP3 bj more' Heq a sub nextD acc tail hpos ha.
  - discriminate.
  - inversion Heq; subst isP30 bj0 more'; clear Heq.
    cbn [backStep].
    destruct more as [|[prevP prevB] more2].
    + (* Top of chain *)
      destruct isP3; cbn [negb]; [|exact I].
      destruct (peel_n (S sub) bj) as [bm1|] eqn:Ebj; [|exact I].
      apply peel_n_some in Ebj.
      destruct (div2 (BigUint.succ bm1)) as [q even] eqn:Ediv.
      pose proof (div2_spec _ _ _ Ediv) as Hdiv.
      rewrite inj_succ in Hdiv.
      destruct even.
      * destruct (peel_n 3 (BigUint.add a q)) as [aqm3|] eqn:Eaq; [|exact I].
        apply peel_n_some in Eaq. rewrite inj_add in Eaq.
        assert (Hq1 : 1 <= BigUint.to_nat q) by lia.
        eapply etrans.
        { cbn [encChain].
          eapply evstep_eq;
          [apply (bounce2_pow (BigUint.to_nat q - 1) (BigUint.to_nat a) 2 [] true
            ((bitsDelim nextD ++ encStack acc) *> tail) ha ltac:(lia) I) | tape_eq | reflexivity]. }
        { eapply etrans.
          - cbn [encChain].
            eapply evstep_eq;
            [apply (b2_exit_top_rem1 (BigUint.to_nat a + (BigUint.to_nat q - 1))
              ((R9 ^^ (BigUint.to_nat q - 1) ++ bitsDelim nextD ++ encStack acc) *> tail)
              ltac:(lia)) | tape_eq | reflexivity].
          - unfold hubCfg. cbn [encStack]. rewrite inj_add.
            eapply evstep_eq;
            [apply (rule_B3_pow_exit (BigUint.to_nat a + BigUint.to_nat q)
              ((bitsDelim W1 ++ R9 ++ R9 ^^ (BigUint.to_nat q - 1) ++
                bitsDelim nextD ++ encStack acc) *> tail) ltac:(lia)) | tape_eq | tape_eq]. }
      * destruct (peel_n 2 (BigUint.add a q)) as [aqm2|] eqn:Eaq; [|exact I].
        apply peel_n_some in Eaq. rewrite inj_add in Eaq.
        eapply etrans.
        { cbn [encChain].
          eapply evstep_eq;
          [apply (bounce2_pow (BigUint.to_nat q) (BigUint.to_nat a) 1 [] true
            ((bitsDelim nextD ++ encStack acc) *> tail) ha ltac:(lia) I) | tape_eq | reflexivity]. }
        { eapply etrans.
          - cbn [encChain].
            eapply evstep_eq;
            [apply (b2_exit_top_rem0 (BigUint.to_nat a + BigUint.to_nat q)
              ((R9 ^^ (BigUint.to_nat q) ++ bitsDelim nextD ++ encStack acc) *> tail)
              ltac:(lia)) | tape_eq | reflexivity].
          - unfold hubCfg. cbn [encStack]. rewrite !inj_succ.
            eapply evstep_eq;
            [apply (rule_B3_pow_exit (BigUint.to_nat a + BigUint.to_nat q - 1)
              ((bitsDelim P3 ++ R9 ++ R9 ^^ (BigUint.to_nat q) ++
                bitsDelim nextD ++ encStack acc) *> tail) ltac:(lia)) | tape_eq | tape_eq]. }
    + (* Middle of chain *)
      destruct hpos as [hprevB_pos hpos2].
      destruct (peel_n (S sub) bj) as [bm1|] eqn:Ebj; [|exact I].
      destruct (peel_n 3 prevB) as [pbm3|] eqn:Epb; [|exact I].
      apply peel_n_some in Ebj.
      apply peel_n_some in Epb.
      destruct (div2 (BigUint.succ bm1)) as [q even] eqn:Ediv.
      pose proof (div2_spec _ _ _ Ediv) as Hdiv.
      rewrite inj_succ in Hdiv.
      set (a' := BigUint.succ (BigUint.add a q)).
      assert (Ha' : BigUint.to_nat a' = BigUint.to_nat a + BigUint.to_nat q + 1).
      { unfold a'. rewrite inj_succ, inj_add. lia. }
      destruct even.
      * assert (Hq1 : 1 <= BigUint.to_nat q) by lia.
        assert (Hstep :
          cfgB (L6_1 *> const S0)
            ((R6 ^^ (BigUint.to_nat a) ++ encChain ((prevP, prevB) :: more2) ++ RSep isP3 ++
              R6 ^^ (BigUint.to_nat bj - sub) ++
              SEP ++ bitsDelim nextD ++ encStack acc) *> tail) -->*
          cfgB (L6_1 *> const S0)
            ((R6 ^^ (BigUint.to_nat a') ++ encChain more2 ++ RSep prevP ++
              R6 ^^ (BigUint.to_nat prevB - 1) ++
              SEP ++ bitsDelim (if isP3 then W1 else W2) ++
              encStack ((q, nextD) :: acc)) *> tail)).
        { eapply etrans.
          - eapply evstep_eq;
            [apply (bounce2_pow (BigUint.to_nat q - 1) (BigUint.to_nat a) 2
              ((prevP, prevB) :: more2) isP3 ((bitsDelim nextD ++ encStack acc) *> tail)
              ha ltac:(lia) (conj hprevB_pos hpos2)) | tape_eq | reflexivity].
          - cbn [encStack].
            eapply evstep_eq;
            [apply (b2_exit_mid_rem1 (BigUint.to_nat a + (BigUint.to_nat q - 1)) prevB more2
              prevP isP3 ((R9 ^^ (BigUint.to_nat q - 1) ++ bitsDelim nextD ++ encStack acc) *> tail)
              ltac:(lia) ltac:(lia) hpos2) | tape_eq | tape_eq]. }
        pose proof (IH prevP prevB more2 eq_refl a' 1 (if isP3 then W1 else W2)
          ((q, nextD) :: acc) tail hpos2 ltac:(lia)) as Hih.
        destruct (backStep ((prevP, prevB) :: more2) a' 1 (if isP3 then W1 else W2)
          ((q, nextD) :: acc)) as [out | |]; [| exact Hih | exact I].
        exact (etrans Hstep Hih).
      * assert (Hstep :
          cfgB (L6_1 *> const S0)
            ((R6 ^^ (BigUint.to_nat a) ++ encChain ((prevP, prevB) :: more2) ++ RSep isP3 ++
              R6 ^^ (BigUint.to_nat bj - sub) ++
              SEP ++ bitsDelim nextD ++ encStack acc) *> tail) -->*
          cfgB (L6_1 *> const S0)
            ((R6 ^^ (BigUint.to_nat a') ++ encChain more2 ++ RSep prevP ++
              R6 ^^ (BigUint.to_nat prevB - 2) ++
              SEP ++ bitsDelim (if isP3 then P3 else P2) ++
              encStack ((BigUint.succ q, nextD) :: acc)) *> tail)).
        { eapply etrans.
          - eapply evstep_eq;
            [apply (bounce2_pow (BigUint.to_nat q) (BigUint.to_nat a) 1
              ((prevP, prevB) :: more2) isP3 ((bitsDelim nextD ++ encStack acc) *> tail)
              ha ltac:(lia) (conj hprevB_pos hpos2)) | tape_eq | reflexivity].
          - cbn [encStack]. rewrite inj_succ.
            eapply evstep_eq;
            [apply (b2_exit_mid_rem0 (BigUint.to_nat a + BigUint.to_nat q) prevB more2
              prevP isP3 ((R9 ^^ (BigUint.to_nat q) ++ bitsDelim nextD ++ encStack acc) *> tail)
              ltac:(lia) ltac:(lia) hpos2) | tape_eq | tape_eq]. }
        pose proof (IH prevP prevB more2 eq_refl a' 2 (if isP3 then P3 else P2)
          ((BigUint.succ q, nextD) :: acc) tail hpos2 ltac:(lia)) as Hih.
        destruct (backStep ((prevP, prevB) :: more2) a' 2 (if isP3 then P3 else P2)
          ((BigUint.succ q, nextD) :: acc)) as [out | |]; [| exact Hih | exact I].
        exact (etrans Hstep Hih).
Qed.

Lemma scanStep_sound (st : Stack) :
  forall (nk : BigUint) (d : Delim) (rest : Stack),
    st = (nk, d) :: rest ->
    forall (aAcc : BigUint) (addNext : nat) (revBs : RevBs) (prevSep : bool)
      (a_tape r6init r9rem : nat) (tail : side),
      AllPos revBs -> 1 <= r6init ->
      a_tape + r9rem = BigUint.to_nat aAcc + BigUint.to_nat nk ->
      r6init + r9rem = BigUint.to_nat nk + addNext ->
      match scanStep st aAcc addNext revBs prevSep with
      | Cont out =>
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_tape + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ r6init ++
            R9 ^^ r9rem ++ bitsDelim d ++ encStack rest) *> tail) -->*
        hubCfg out tail
      | Halted =>
        halts tm
          (cfgB (L6_1 *> const S0)
            ((R6 ^^ (a_tape + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ r6init ++
              R9 ^^ r9rem ++ bitsDelim d ++ encStack rest) *> tail))
      | Stuck => True
      end.
Proof.
  induction st as [|[nk0 d0] rest IH];
    intros nk d rest' Heq aAcc addNext revBs prevSep a_tape r6init r9rem tail
      hpos hr6 ha_sum hr6_sum.
  - discriminate.
  - inversion Heq; subst nk0 d0 rest'; clear Heq.
    set (a_mid := BigUint.to_nat aAcc + BigUint.to_nat nk).
    set (bk := add_small addNext nk).
    assert (Hbk : BigUint.to_nat bk = BigUint.to_nat nk + addNext) by apply add_small_spec.
    assert (Hb1 :
      cfgB (L6_1 *> const S0)
        ((R6 ^^ (a_tape + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ r6init ++
          R9 ^^ r9rem ++ bitsDelim d ++ encStack rest) *> tail) -->*
      cfgB (L6_1 *> const S0)
        ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
          bitsDelim d ++ encStack rest) *> tail)).
    { eapply evstep_eq;
      [apply (bounce1_pow r9rem a_tape r6init revBs prevSep
        ((bitsDelim d ++ encStack rest) *> tail) hr6 hpos) | tape_eq | unfold a_mid; tape_eq]. }
    destruct d; cbn [scanStep]; fold bk.
    + (* P1 *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 2 bk) as [bkm2|] eqn:Ebk; [|exact I].
      destruct (peel_n 1 na) as [nam1|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      assert (Hrt :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim P1 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ ((a_mid + 1) + 1) ++ encChain ((prevSep, bk) :: revBs) ++ RSep false ++
            R6 ^^ 2 ++ R9 ^^ (BigUint.to_nat nam1) ++ bitsDelim da ++ encStack tail_st) *> tail)).
      { cbn [encStack encChain].
        eapply evstep_eq;
        [apply (roundTrip a_mid (BigUint.to_nat bk - 2) 1 2 revBs prevSep
          (bitsDelim P1 ++ R9) (RSep false ++ R6 ^^ 2)
          ((R9 ^^ (BigUint.to_nat nam1) ++ bitsDelim da ++ encStack tail_st) *> tail)
          hpos (fun l => local_C_P1_R9 l _)) | tape_eq | tape_eq]. }
      pose proof (IH na da tail_st eq_refl (BigUint.add aAcc nk) 1 ((prevSep, bk) :: revBs) false
        (a_mid + 1) 2 (BigUint.to_nat nam1) tail
        ltac:(cbn [AllPos]; split; [lia | exact hpos]) ltac:(lia)
        ltac:(rewrite inj_add; unfold a_mid; lia) ltac:(lia)) as Hih.
      destruct (scanStep ((na, da) :: tail_st) (BigUint.add aAcc nk) 1
        ((prevSep, bk) :: revBs) false) as [out | |].
      * exact (etrans (etrans Hb1 Hrt) Hih).
      * exact (halts_evstep tm _ _ Hih (etrans Hb1 Hrt)).
      * exact I.
    + (* P2 *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 2 bk) as [bkm2|] eqn:Ebk; [|exact I].
      destruct (peel_n 1 na) as [nam1|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      assert (Hrt :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim P2 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ ((a_mid + 1) + 1) ++ encChain ((prevSep, BigUint.succ bk) :: revBs) ++
            RSep false ++ R6 ^^ 1 ++ R9 ^^ (BigUint.to_nat nam1) ++
            bitsDelim da ++ encStack tail_st) *> tail)).
      { cbn [encStack encChain]. rewrite inj_succ.
        eapply evstep_eq;
        [apply (roundTrip a_mid (BigUint.to_nat bk - 2) 1 3 revBs prevSep
          (bitsDelim P2 ++ R9) (RSep false ++ R6 ^^ 1)
          ((R9 ^^ (BigUint.to_nat nam1) ++ bitsDelim da ++ encStack tail_st) *> tail)
          hpos (fun l => local_C_P2_R9 l _)) | tape_eq | tape_eq]. }
      pose proof (IH na da tail_st eq_refl (BigUint.add aAcc nk) 0
        ((prevSep, BigUint.succ bk) :: revBs) false
        (a_mid + 1) 1 (BigUint.to_nat nam1) tail
        ltac:(cbn [AllPos]; split; [rewrite inj_succ; lia | exact hpos]) ltac:(lia)
        ltac:(rewrite inj_add; unfold a_mid; lia) ltac:(lia)) as Hih.
      destruct (scanStep ((na, da) :: tail_st) (BigUint.add aAcc nk) 0
        ((prevSep, BigUint.succ bk) :: revBs) false) as [out | |].
      * exact (etrans (etrans Hb1 Hrt) Hih).
      * exact (halts_evstep tm _ _ Hih (etrans Hb1 Hrt)).
      * exact I.
    + (* P3 *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 2 bk) as [bkm2|] eqn:Ebk; [|exact I].
      destruct (peel_n 1 na) as [nam1|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      assert (Hrt :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim P3 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ ((a_mid + 1) + 1) ++ encChain ((prevSep, BigUint.succ bk) :: revBs) ++
            RSep true ++ R6 ^^ 1 ++ R9 ^^ (BigUint.to_nat nam1) ++
            bitsDelim da ++ encStack tail_st) *> tail)).
      { cbn [encStack encChain]. rewrite inj_succ.
        eapply evstep_eq;
        [apply (roundTrip a_mid (BigUint.to_nat bk - 2) 1 3 revBs prevSep
          (bitsDelim P3 ++ R9) (RSep true ++ R6 ^^ 1)
          ((R9 ^^ (BigUint.to_nat nam1) ++ bitsDelim da ++ encStack tail_st) *> tail)
          hpos (fun l => local_C_P3_R9 l _)) | tape_eq | tape_eq]. }
      pose proof (IH na da tail_st eq_refl (BigUint.add aAcc nk) 0
        ((prevSep, BigUint.succ bk) :: revBs) true
        (a_mid + 1) 1 (BigUint.to_nat nam1) tail
        ltac:(cbn [AllPos]; split; [rewrite inj_succ; lia | exact hpos]) ltac:(lia)
        ltac:(rewrite inj_add; unfold a_mid; lia) ltac:(lia)) as Hih.
      destruct (scanStep ((na, da) :: tail_st) (BigUint.add aAcc nk) 0
        ((prevSep, BigUint.succ bk) :: revBs) true) as [out | |].
      * exact (etrans (etrans Hb1 Hrt) Hih).
      * exact (halts_evstep tm _ _ Hih (etrans Hb1 Hrt)).
      * exact I.
    + (* W1 *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 2 bk) as [bkm2|] eqn:Ebk; [|exact I].
      destruct (peel_n 1 na) as [na'|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      set (bk' := BigUint.succ bkm2).
      set (a' := add_small 3 (BigUint.add aAcc nk)).
      set (r_tail := (R9 ^^ (BigUint.to_nat na') ++ bitsDelim da ++ encStack tail_st) *> tail).
      assert (Ha' : BigUint.to_nat a' = a_mid + 3).
      { unfold a', a_mid. rewrite add_small_spec, inj_add. lia. }
      assert (Hbk' : BigUint.to_nat bk' = BigUint.to_nat bk - 1).
      { unfold bk'. rewrite inj_succ. lia. }
      assert (Hw :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim W1 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (BigUint.to_nat a') ++ encChain revBs ++ RSep prevSep ++
            R6 ^^ (BigUint.to_nat bk' - 0) ++
            SEP ++ bitsDelim P1 ++ encStack ((na', da) :: tail_st)) *> tail)).
      { eapply etrans.
        - cbn [encStack].
          eapply evstep_eq;
          [apply (roundTrip a_mid (BigUint.to_nat bk - 1) 0 1 revBs prevSep
            (bitsDelim W1 ++ R9) ([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0])
            r_tail hpos (fun l => local_W1_h1 l r_tail)) | unfold r_tail; tape_eq | reflexivity].
        - cbn [encStack].
          eapply evstep_eq;
          [apply (roundTrip (a_mid + 1) (BigUint.to_nat bk - 2) 1 1 revBs prevSep
            ([S1; S0; S1; S0] ++ R6 ++ [S0; S1; S0; S0; S0]) (SEP ++ bitsDelim P1)
            r_tail hpos (fun l => local_W1_h2 l r_tail)) | unfold r_tail; tape_eq | unfold r_tail; tape_eq]. }
      pose proof (backStep_sound ((prevSep, bk') :: revBs) prevSep bk' revBs eq_refl
        a' 0 P1 ((na', da) :: tail_st) tail hpos ltac:(lia)) as Hback.
      destruct (backStep ((prevSep, bk') :: revBs) a' 0 P1 ((na', da) :: tail_st)) as [out | |];
        [| destruct Hback | exact I].
      exact (etrans (etrans Hb1 Hw) Hback).
    + (* W2 *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 4 bk) as [bkm4|] eqn:Ebk; [|exact I].
      destruct (peel_n 1 na) as [na'|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      set (bk' := BigUint.succ bkm4).
      set (a' := add_small 4 (BigUint.add aAcc nk)).
      set (r_tail := (R9 ^^ (BigUint.to_nat na') ++ bitsDelim da ++ encStack tail_st) *> tail).
      assert (Ha' : BigUint.to_nat a' = a_mid + 4).
      { unfold a', a_mid. rewrite add_small_spec, inj_add. lia. }
      assert (Hbk' : BigUint.to_nat bk' = BigUint.to_nat bk - 3).
      { unfold bk'. rewrite inj_succ. lia. }
      assert (Hw :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim W2 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (BigUint.to_nat a') ++ encChain revBs ++ RSep prevSep ++
            R6 ^^ (BigUint.to_nat bk' - 0) ++
            SEP ++ bitsDelim W3 ++ encStack ((na', da) :: tail_st)) *> tail)).
      { eapply etrans.
        - cbn [encStack].
          eapply evstep_eq;
          [apply (roundTrip a_mid (BigUint.to_nat bk - 1) 0 2 revBs prevSep
            (bitsDelim W2 ++ R9) [S0; S1; S0; S0; S0]
            r_tail hpos (fun l => local_W2_h1 l r_tail)) | unfold r_tail; tape_eq | reflexivity].
        - eapply etrans.
          + eapply evstep_eq;
            [apply (roundTrip (a_mid + 1) (BigUint.to_nat bk - 2) 2 1 revBs prevSep
              [S0; S1; S0; S0; S0] ([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0])
              r_tail hpos (fun l => local_W2_h2 l r_tail)) | unfold r_tail; tape_eq | reflexivity].
          + cbn [encStack].
            eapply evstep_eq;
            [apply (roundTrip (a_mid + 2) (BigUint.to_nat bk - 4) 2 1 revBs prevSep
              ([S0; S0; S0; S0; S0; S0] ++ R6 ++ [S0; S0]) (SEP ++ bitsDelim W3)
              r_tail hpos (fun l => local_W2_h3 l r_tail)) | unfold r_tail; tape_eq | unfold r_tail; tape_eq]. }
      pose proof (backStep_sound ((prevSep, bk') :: revBs) prevSep bk' revBs eq_refl
        a' 0 W3 ((na', da) :: tail_st) tail hpos ltac:(lia)) as Hback.
      destruct (backStep ((prevSep, bk') :: revBs) a' 0 W3 ((na', da) :: tail_st)) as [out | |];
        [| destruct Hback | exact I].
      exact (etrans (etrans Hb1 Hw) Hback).
    + (* W3 *)
      destruct (peel_n 2 bk) as [bkm2|] eqn:Ebk; [|exact I].
      apply peel_n_some in Ebk.
      set (bk' := BigUint.succ bkm2).
      set (a' := add_small 3 (BigUint.add aAcc nk)).
      set (r_tail := encStack rest *> tail).
      assert (Ha' : BigUint.to_nat a' = a_mid + 3).
      { unfold a', a_mid. rewrite add_small_spec, inj_add. lia. }
      assert (Hbk' : BigUint.to_nat bk' = BigUint.to_nat bk - 1).
      { unfold bk'. rewrite inj_succ. lia. }
      assert (Hw :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim W3 ++ encStack rest) *> tail) -->*
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (BigUint.to_nat a') ++ encChain revBs ++ RSep prevSep ++
            R6 ^^ (BigUint.to_nat bk' - 0) ++
            SEP ++ bitsDelim W4 ++ encStack rest) *> tail)).
      { eapply etrans.
        - eapply evstep_eq;
          [apply (roundTrip a_mid (BigUint.to_nat bk - 1) 0 2 revBs prevSep
            (bitsDelim W3) [S0; S0; S0; S0]
            r_tail hpos (fun l => local_W3_h1 l r_tail)) | unfold r_tail; tape_eq | reflexivity].
        - eapply evstep_eq;
          [apply (roundTrip (a_mid + 1) (BigUint.to_nat bk - 2) 2 1 revBs prevSep
            [S0; S0; S0; S0] (SEP ++ bitsDelim W4)
            r_tail hpos (fun l => local_W3_h2 l r_tail)) | unfold r_tail; tape_eq | unfold r_tail; tape_eq]. }
      pose proof (backStep_sound ((prevSep, bk') :: revBs) prevSep bk' revBs eq_refl
        a' 0 W4 rest tail hpos ltac:(lia)) as Hback.
      destruct (backStep ((prevSep, bk') :: revBs) a' 0 W4 rest) as [out | |];
        [| destruct Hback | exact I].
      exact (etrans (etrans Hb1 Hw) Hback).
    + (* W4 -> Halted *)
      destruct rest as [|[na da] tail_st]; [exact I|].
      destruct (peel_n 1 bk) as [bkm1|] eqn:Ebk; [|exact I].
      destruct (peel_n 2 na) as [nam2|] eqn:Ena; [|exact I].
      apply peel_n_some in Ebk. apply peel_n_some in Ena.
      assert (Hsw :
        cfgB (L6_1 *> const S0)
          ((R6 ^^ (a_mid + 1) ++ encChain revBs ++ RSep prevSep ++ R6 ^^ (BigUint.to_nat bk) ++
            bitsDelim W4 ++ encStack ((na, da) :: tail_st)) *> tail) -->*
        cfgC ([S1; S1; S0] *>
          (L6 ^^ (BigUint.to_nat bk - 1) *>
            (LSep prevSep *> (encLChain revBs *> (L6 ^^ (a_mid + 1) *> (L6_1 *> const S0))))))
          ((bitsDelim W4 ++ R9 ++ [S1]) *>
            (([S0; S0; S0; S0; S1; S0; S0; S0] ++ R9 ^^ (BigUint.to_nat nam2) ++
              bitsDelim da ++ encStack tail_st) *> tail))).
      { assert (Hna : R9 ^^ (BigUint.to_nat na) =
          R9 ++ [S1] ++ [S0; S0; S0; S0; S1; S0; S0; S0] ++ R9 ^^ (BigUint.to_nat nam2)).
        { rewrite Ena, lpow_add, R9_2_split, !app_assoc. reflexivity. }
        eapply evstep_eq;
        [apply (sweepOut_chain a_mid (BigUint.to_nat bk - 1) revBs prevSep
          ((bitsDelim W4 ++ encStack ((na, da) :: tail_st)) *> tail) hpos) | tape_eq | cbn [encStack]; rewrite Hna; tape_eq]. }
      eapply halts_evstep; [| exact (etrans Hb1 Hsw)].
      apply local_W4_halt.
Qed.

Lemma stackStep_spec (st : Stack) (tail : side) :
  match stackStep st with
  | Cont out => hubCfg st tail -->* hubCfg out tail
  | Halted => halts tm (hubCfg st tail)
  | Stuck => True
  end.
Proof.
  destruct st as [|[n0 d0] rest]; [exact I|].
  assert (Hentry :
    hubCfg ((n0, d0) :: rest) tail -->*
    cfgB (L6_1 *> const S0)
      ((R6 ^^ (0 + 1) ++ encChain [] ++ RSep true ++ R6 ^^ 1 ++
        R9 ^^ (BigUint.to_nat n0) ++ bitsDelim d0 ++ encStack rest) *> tail)).
  { unfold hubCfg. cbn [encStack encChain].
    eapply evstep_eq;
    [apply (rule_hub_entry ((R9 ^^ (BigUint.to_nat n0) ++ bitsDelim d0 ++ encStack rest) *> tail)) | tape_eq | tape_eq]. }
  pose proof (scanStep_sound ((n0, d0) :: rest) n0 d0 rest eq_refl BigUintNil 1 [] true
    0 1 (BigUint.to_nat n0) tail I ltac:(lia)
    ltac:(change (BigUint.to_nat BigUintNil) with 0; lia) ltac:(lia)) as Hscan.
  unfold stackStep.
  destruct (scanStep ((n0, d0) :: rest) BigUintNil 1 [] true) as [out | |].
  - exact (etrans Hentry Hscan).
  - exact (halts_evstep tm _ _ Hscan Hentry).
  - exact I.
Qed.

Lemma run_steps_spec (n : nat) :
  forall (st : Stack) (tail : side),
    match run_steps n st with
    | Cont out => hubCfg st tail -->* hubCfg out tail
    | Halted => halts tm (hubCfg st tail)
    | Stuck => True
    end.
Proof.
  induction n as [|n IH]; intros st tail; cbn [run_steps].
  - apply evstep_refl.
  - pose proof (stackStep_spec st tail) as Hs.
    destruct (stackStep st) as [st' | |]; [| exact Hs | exact I].
    pose proof (IH st' tail) as Hih.
    destruct (run_steps n st') as [out | |].
    + exact (etrans Hs Hih).
    + exact (halts_evstep tm _ _ Hih Hs).
    + exact I.
Qed.

Lemma run_steps_halts (n : nat) (st : Stack) :
  match run_steps n st with
  | Cont out => hub_halts out -> hub_halts st
  | Halted => hub_halts st
  | Stuck => True
  end.
Proof.
  destruct (run_steps n st) as [out | |] eqn:E.
  - intros Hout tail.
    pose proof (run_steps_spec n st tail) as Hs; rewrite E in Hs.
    exact (halts_evstep tm _ _ (Hout tail) Hs).
  - intro tail.
    pose proof (run_steps_spec n st tail) as Hs; rewrite E in Hs; exact Hs.
  - exact I.
Qed.

Lemma run_blocks_sound (blocks : nat) :
  forall (st : Stack),
    run_blocks blocks st = Halted -> hub_halts st.
Proof.
  induction blocks as [|b IH]; intros st H; cbn [run_blocks] in H.
  - pose proof (run_steps_halts 63 st) as Hs.
    rewrite H in Hs. exact Hs.
  - pose proof (run_steps_halts 64 st) as Hs.
    destruct (run_steps 64 st) as [st' | |]; [| exact Hs | discriminate].
    apply Hs. apply (truncate_sound 24). apply IH. exact H.
Qed.

(* ========================================================================== *)
(* Layer 3: Blank-Tape Bootstrap (c0 -> hit4 -> hit7 -> hit8 -> cp0) & Halt   *)
(* ========================================================================== *)

Definition n2 : BigUint := Eval compute in (BigUint.of_nat 2).
Definition n3 : BigUint := Eval compute in (BigUint.of_nat 3).
Definition n4 : BigUint := Eval compute in (BigUint.of_nat 4).
Definition n5 : BigUint := Eval compute in (BigUint.of_nat 5).
Definition n6 : BigUint := Eval compute in (BigUint.of_nat 6).
Definition n7 : BigUint := Eval compute in (BigUint.of_nat 7).
Definition n10 : BigUint := Eval compute in (BigUint.of_nat 10).
Definition n11 : BigUint := Eval compute in (BigUint.of_nat 11).
Definition n12 : BigUint := Eval compute in (BigUint.of_nat 12).
Definition n14 : BigUint := Eval compute in (BigUint.of_nat 14).
Definition n20 : BigUint := Eval compute in (BigUint.of_nat 20).
Definition n30 : BigUint := Eval compute in (BigUint.of_nat 30).
Definition n60 : BigUint := Eval compute in (BigUint.of_nat 60).
Definition n62 : BigUint := Eval compute in (BigUint.of_nat 62).
Definition n103 : BigUint := Eval compute in (BigUint.of_nat 103).
Definition n154 : BigUint := Eval compute in (BigUint.of_nat 154).

Definition hit4Stack : Stack := [(n14, W1); (n3, P3)].
Definition hit7Stack : Stack := [(n60, P3); (n20, P1); (n11, P1); (n6, P1); (n2, P3)].
Definition hit8Stack : Stack :=
  [(n154, W1); (n30, P3); (n10, W2); (n5, P2); (n3, P2); (n2, W1)].
Definition cp0 : Stack := [(n154, W1); (n30, P3); (n10, W2); (n5, P2)].

Lemma hit7_to_hit8 :
  hubCfg hit7Stack ((R9 ++ [S1; S0; S1; S0; S1]) *> const S0) -->*
  hubCfg hit8Stack ([S1; S0; S1; S0; S1] *> const S0).
Proof.
  set (tail7 := (R9 ++ [S1; S0; S1; S0; S1]) *> const S0).
  set (ch0 := ([] : RevBs)).
  set (ch1 := (true, n62) :: ch0).
  set (ch2 := (true, n20) :: ch1).
  set (ch3 := (false, n12) :: ch2).
  set (ch4 := (false, n7) :: ch3).
  set (ch5 := (false, n4) :: ch4).
  assert (hpos1 : AllPos ch1) by (unfold ch1, ch0; cbn [AllPos]; split; [change (BigUint.to_nat n62) with 62; lia | exact I]).
  assert (hpos2 : AllPos ch2) by (unfold ch2; cbn [AllPos]; split; [change (BigUint.to_nat n20) with 20; lia | exact hpos1]).
  assert (hpos3 : AllPos ch3) by (unfold ch3; cbn [AllPos]; split; [change (BigUint.to_nat n12) with 12; lia | exact hpos2]).
  assert (hpos4 : AllPos ch4) by (unfold ch4; cbn [AllPos]; split; [change (BigUint.to_nat n7) with 7; lia | exact hpos3]).
  assert (hpos5 : AllPos ch5) by (unfold ch5; cbn [AllPos]; split; [change (BigUint.to_nat n4) with 4; lia | exact hpos4]).
  let htape :=
    unfold hubCfg, tail7, ch5, ch4, ch3, ch2, ch1, ch0, hit7Stack, hit8Stack;
    cbn [encStack encChain encLChain];
    change (BigUint.to_nat n2) with 2;
    change (BigUint.to_nat n3) with 3;
    change (BigUint.to_nat n4) with 4;
    change (BigUint.to_nat n5) with 5;
    change (BigUint.to_nat n6) with 6;
    change (BigUint.to_nat n7) with 7;
    change (BigUint.to_nat n10) with 10;
    change (BigUint.to_nat n11) with 11;
    change (BigUint.to_nat n12) with 12;
    change (BigUint.to_nat n20) with 20;
    change (BigUint.to_nat n30) with 30;
    change (BigUint.to_nat n60) with 60;
    change (BigUint.to_nat n62) with 62;
    change (BigUint.to_nat n103) with 103;
    change (BigUint.to_nat n154) with 154;
    tape_eq
  in
  (* Hub entry *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (rule_hub_entry ((R9 ^^ 60 ++ bitsDelim P3 ++
     encStack [(n20, P1); (n11, P1); (n6, P1); (n2, P3)]) *> tail7)) | htape | reflexivity] |];
  (* Element 0: (60, P3) *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (bounce1_pow 60 0 1 ch0 true
     ((bitsDelim P3 ++ encStack [(n20, P1); (n11, P1); (n6, P1); (n2, P3)]) *> tail7)
     ltac:(lia) I) | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 60 59 1 3 ch0 true (bitsDelim P3 ++ R9) (RSep true ++ R6 ^^ 1)
     ((R9 ^^ 19 ++ bitsDelim P1 ++ encStack [(n11, P1); (n6, P1); (n2, P3)]) *> tail7)
     I (fun l => local_C_P3_R9 l _)) | htape | reflexivity] |];
  (* Element 1: (20, P1) *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (bounce1_pow 19 61 1 ch1 true
     ((bitsDelim P1 ++ encStack [(n11, P1); (n6, P1); (n2, P3)]) *> tail7)
     ltac:(lia) hpos1) | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 80 18 1 2 ch1 true (bitsDelim P1 ++ R9) (RSep false ++ R6 ^^ 2)
     ((R9 ^^ 10 ++ bitsDelim P1 ++ encStack [(n6, P1); (n2, P3)]) *> tail7)
     hpos1 (fun l => local_C_P1_R9 l _)) | htape | reflexivity] |];
  (* Element 2: (11, P1) *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (bounce1_pow 10 81 2 ch2 false
     ((bitsDelim P1 ++ encStack [(n6, P1); (n2, P3)]) *> tail7)
     ltac:(lia) hpos2) | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 91 10 1 2 ch2 false (bitsDelim P1 ++ R9) (RSep false ++ R6 ^^ 2)
     ((R9 ^^ 5 ++ bitsDelim P1 ++ encStack [(n2, P3)]) *> tail7)
     hpos2 (fun l => local_C_P1_R9 l _)) | htape | reflexivity] |];
  (* Element 3: (6, P1) *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (bounce1_pow 5 92 2 ch3 false
     ((bitsDelim P1 ++ encStack [(n2, P3)]) *> tail7)
     ltac:(lia) hpos3) | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 97 5 1 2 ch3 false (bitsDelim P1 ++ R9) (RSep false ++ R6 ^^ 2)
     ((R9 ^^ 1 ++ bitsDelim P3) *> tail7)
     hpos3 (fun l => local_C_P1_R9 l _)) | htape | reflexivity] |];
  (* Element 4: (2, P3) consuming R9 from tail7 *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (bounce1_pow 1 98 2 ch4 false (bitsDelim P3 *> tail7) ltac:(lia) hpos4)
    | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 99 1 1 3 ch4 false (bitsDelim P3 ++ R9) (RSep true ++ R6 ^^ 1)
     ([S1; S0; S1; S0; S1] *> const S0) hpos4 (fun l => local_C_P3_R9 l _)) | htape | reflexivity] |];
  (* Hop 1 at right boundary [S1; S0; S1; S0; S1] *> const S0 *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (sweepOut_chain 100 0 ch5 true ([S1; S0; S1; S0; S1] *> const S0) hpos5)
    | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (local_hit7_h1
     (L6 ^^ 1 *> (LSep false *> (encLChain ch4 *> (L6 ^^ 101 *> (L6_1 *> const S0))))))
    | htape | reflexivity] |];
  eapply etrans;
  [eapply evstep_eq;
   [apply (sweepBack_chain 100 1 ch4 false
     ((R6 ^^ 3 ++ ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) ++ [S1; S0; S1; S0; S1]) *> const S0)
     hpos4) | htape | reflexivity] |];
  (* Hop 2 + backStep *)
  eapply etrans;
  [eapply evstep_eq;
   [apply (roundTrip 101 1 2 2 ch4 false
     ([S1; S0; S1; S0] ++ R6 ++ [S0; S0; S1; S0; S0; S0]) (SEP ++ bitsDelim W1)
     ([S1; S0; S1; S0; S1] *> const S0) hpos4 (fun l => local_B2_rem1_S3_h2 l _)) | htape | reflexivity] |];
  assert (Hbeval : backStep ((false, n3) :: ch4) n103 0 W1 [] = Cont hit8Stack)
    by vm_cast_no_check (eq_refl (Cont hit8Stack));
  pose proof (backStep_sound ((false, n3) :: ch4) false n3 ch4 eq_refl n103 0 W1 []
    ([S1; S0; S1; S0; S1] *> const S0) hpos4
    ltac:(change (BigUint.to_nat n103) with 103; lia)) as Hback;
  rewrite Hbeval in Hback;
  eapply evstep_eq; [exact Hback | htape | reflexivity].
Qed.

Local Transparent cfgB cfgC lpow L6 L6_1 L11 LSep R6 R9 SEP RSep bitsDelim.

Lemma init_to_hit4 :
  c0 -->* hubCfg hit4Stack ((R9 ++ [S1; S0; S1; S0; S1]) *> const S0).
Proof.
  change c0 with (evalLocal (mkLocal A R [] []) (const S0) (const S0)).
  unfold hubCfg, cfgC.
  rewrite <- Str_app_assoc.
  apply (runLocal_tt (11 * 1000 + 243) A R [] [] C R L11
    (([S0; S0; S0; S0; S0] ++ encStack hit4Stack) ++ R9 ++ [S1; S0; S1; S0; S1])).
  vm_refl.
Qed.

Lemma hit4_to_hit7 (tail : side) :
  hubCfg hit4Stack tail -->* hubCfg hit7Stack tail.
Proof.
  assert (H : run_steps 3 hit4Stack = Cont hit7Stack).
  { vm_cast_no_check (eq_refl (Cont hit7Stack)). }
  pose proof (run_steps_spec 3 hit4Stack tail) as Hs.
  rewrite H in Hs. exact Hs.
Qed.

Lemma init_to_hit8 :
  c0 -->* hubCfg hit8Stack ([S1; S0; S1; S0; S1] *> const S0).
Proof.
  eapply etrans; [apply init_to_hit4 |].
  eapply etrans; [apply hit4_to_hit7 |].
  exact hit7_to_hit8.
Qed.

Lemma cp0_halts : hub_halts cp0.
Proof.
  apply (run_blocks_sound 3008 cp0).
  vm_cast_no_check (eq_refl Halted).
Qed.

Lemma halt_c0 : halts tm c0.
Proof.
  assert (H8 : hub_halts hit8Stack).
  { apply (truncate_sound 4 hit8Stack). exact cp0_halts. }
  exact (halts_evstep tm c0
    (hubCfg hit8Stack ([S1; S0; S1; S0; S1] *> const S0))
    (H8 ([S1; S0; S1; S0; S1] *> const S0))
    init_to_hit8).
Qed.

End M566.

Theorem halt : halts tm c0.
Proof. exact M566.halt_c0. Qed.
