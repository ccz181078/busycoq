(* 1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB--- halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.List NArith.BinNat NArith.Nnat Lia String.
Import ListNotations.
Set Default Goal Selector "!".

Open Scope sym.
Open Scope list.

Definition tm := Eval compute in
  (TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

(* ========================================================================== *)
(* Section 1: Basic List Power (N-indexed) & Stream Helpers                   *)
(* ========================================================================== *)

Definition npow {A} (l : list A) (n : N) : list A :=
  l ^^ (N.to_nat n).

Lemma npow_0 {A} (l : list A) : npow l 0%N = [].
Proof. reflexivity. Qed.

Lemma npow_1 {A} (l : list A) : npow l 1%N = l.
Proof. unfold npow. cbn. apply app_nil_r. Qed.

Lemma npow_add {A} (l : list A) (n m : N) : npow l (n + m)%N = npow l n ++ npow l m.
Proof. unfold npow. rewrite N2Nat.inj_add, lpow_add. reflexivity. Qed.

Lemma npow_succ_l {A} (l : list A) (n : N) : npow l (n + 1)%N = l ++ npow l n.
Proof. replace (n + 1)%N with (1 + n)%N by lia. rewrite npow_add, npow_1. reflexivity. Qed.

Lemma npow_succ_r {A} (l : list A) (n : N) : npow l (n + 1)%N = npow l n ++ l.
Proof. rewrite npow_add, npow_1. reflexivity. Qed.

Lemma npow_nil {A} (n : N) : npow ([] : list A) n = [].
Proof.
  unfold npow. induction (N.to_nat n) as [|m IHm]; [reflexivity | exact IHm].
Qed.

Lemma N_succ_eq_add_1 (n : N) : N.succ n = (n + 1)%N.
Proof. lia. Qed.

(* ========================================================================== *)
(* Section 2: Four Sound Concrete Steppers (wstep, cstep, rcstep, bstep)      *)
(* ========================================================================== *)

Record CCfg := mkCCfg {
  ccfg_q : Q;
  ccfg_cur : Sym;
  ccfg_l : list Sym;
  ccfg_r : list Sym
}.

Definition is_empty_sym (xs : list Sym) : bool :=
  match xs with [] => true | _ => false end.

Definition evalWindow (l_tail r_tail : side) (c : CCfg) : Q * tape :=
  (ccfg_q c, (ccfg_l c *> l_tail, ccfg_cur c, ccfg_r c *> r_tail)).

Definition wstep (c : CCfg) : option CCfg :=
  match tm (ccfg_q c, ccfg_cur c) with
  | None => None
  | Some (w, L, q') =>
    match ccfg_l c with
    | [] => None
    | b :: ls => Some (mkCCfg q' b ls (w :: ccfg_r c))
    end
  | Some (w, R, q') =>
    match ccfg_r c with
    | [] => None
    | b :: rs => Some (mkCCfg q' b (w :: ccfg_l c) rs)
    end
  end.

Lemma wstep_sound (c c' : CCfg) (l_tail r_tail : side) :
  wstep c = Some c' ->
  evalWindow l_tail r_tail c --> evalWindow l_tail r_tail c'.
Proof.
  destruct c as [q cur l r]. unfold wstep; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r].
  destruct (tm (q, cur)) as [[[w d] q']|] eqn:E; [|discriminate].
  destruct d; [destruct l as [|b ls]; [discriminate|] | destruct r as [|b rs]; [discriminate|]];
    intro H; injection H as <-; apply step_c_spec;
    unfold step_c, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r]; rewrite E; cbn; reflexivity.
Qed.

Fixpoint wmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match wstep c with
    | Some c1 => wmultiStep n' c1
    | None => None
    end
  end.

Lemma wmultiStep_sound (n : nat) (c c' : CCfg) (l_tail r_tail : side) :
  wmultiStep n c = Some c' ->
  evalWindow l_tail r_tail c -->* evalWindow l_tail r_tail c'.
Proof.
  revert c. induction n as [|n IH]; intros c H.
  - injection H as <-. apply evstep_refl.
  - cbn [wmultiStep] in H.
    destruct (wstep c) as [c1|] eqn:E; [|discriminate].
    eapply evstep_step; [exact (wstep_sound c c1 l_tail r_tail E) | exact (IH c1 H)].
Qed.

Definition evalCCfg (r_tail : side) (c : CCfg) : Q * tape :=
  evalWindow 0inf r_tail c.

Definition cstep (c : CCfg) : option CCfg :=
  match tm (ccfg_q c, ccfg_cur c) with
  | None => None
  | Some (w, L, q') =>
    match ccfg_l c with
    | [] => Some (mkCCfg q' 0%sym [] (w :: ccfg_r c))
    | b :: ls => Some (mkCCfg q' b ls (w :: ccfg_r c))
    end
  | Some (w, R, q') =>
    match ccfg_r c with
    | [] => None
    | b :: rs =>
      let l' := if is_empty_sym (ccfg_l c) && sym_eqb w 0%sym then [] else w :: ccfg_l c in
      Some (mkCCfg q' b l' rs)
    end
  end.

Lemma cstep_sound (c c' : CCfg) (r_tail : side) :
  cstep c = Some c' ->
  evalCCfg r_tail c --> evalCCfg r_tail c'.
Proof.
  destruct c as [q cur l r]. unfold cstep; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r].
  destruct (tm (q, cur)) as [[[w d] q']|] eqn:E; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; intro H; injection H as <-;
      apply step_c_spec; unfold step_c, evalCCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r];
      rewrite E; cbn; reflexivity.
  - destruct r as [|b rs]; [discriminate|].
    intro H; injection H as <-; apply step_c_spec;
      unfold step_c, evalCCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r]; rewrite E; cbn.
    destruct l as [|b' ls']; cbn.
    + destruct (sym_eqb_spec w 0%sym) as [->|Hne]; cbn; [rewrite <- const_unfold|]; reflexivity.
    + reflexivity.
Qed.

Fixpoint cmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match cstep c with
    | Some c1 => cmultiStep n' c1
    | None => None
    end
  end.

Lemma cmultiStep_sound (n : nat) (c c' : CCfg) (r_tail : side) :
  cmultiStep n c = Some c' ->
  evalCCfg r_tail c -->* evalCCfg r_tail c'.
Proof.
  revert c. induction n as [|n IH]; intros c H.
  - injection H as <-. apply evstep_refl.
  - cbn [cmultiStep] in H.
    destruct (cstep c) as [c1|] eqn:E; [|discriminate].
    eapply evstep_step; [exact (cstep_sound c c1 r_tail E) | exact (IH c1 H)].
Qed.

Definition evalRCCfg (l_tail : side) (c : CCfg) : Q * tape :=
  evalWindow l_tail 0inf c.

Definition rcstep (c : CCfg) : option CCfg :=
  match tm (ccfg_q c, ccfg_cur c) with
  | None => None
  | Some (w, L, q') =>
    match ccfg_l c with
    | [] => None
    | b :: ls =>
      let r' := if is_empty_sym (ccfg_r c) && sym_eqb w 0%sym then [] else w :: ccfg_r c in
      Some (mkCCfg q' b ls r')
    end
  | Some (w, R, q') =>
    match ccfg_r c with
    | [] => Some (mkCCfg q' 0%sym (w :: ccfg_l c) [])
    | b :: rs => Some (mkCCfg q' b (w :: ccfg_l c) rs)
    end
  end.

Lemma rcstep_sound (c c' : CCfg) (l_tail : side) :
  rcstep c = Some c' ->
  evalRCCfg l_tail c --> evalRCCfg l_tail c'.
Proof.
  destruct c as [q cur l r]. unfold rcstep; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r].
  destruct (tm (q, cur)) as [[[w d] q']|] eqn:E; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; [discriminate|].
    intro H; injection H as <-; apply step_c_spec;
      unfold step_c, evalRCCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r]; rewrite E; cbn.
    destruct r as [|b' rs']; cbn.
    + destruct (sym_eqb_spec w 0%sym) as [->|Hne]; cbn; [rewrite <- const_unfold|]; reflexivity.
    + reflexivity.
  - destruct r as [|b rs]; intro H; injection H as <-;
      apply step_c_spec; unfold step_c, evalRCCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r];
      rewrite E; cbn; reflexivity.
Qed.

Fixpoint rcmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match rcstep c with
    | Some c1 => rcmultiStep n' c1
    | None => None
    end
  end.

Lemma rcmultiStep_sound (n : nat) (c c' : CCfg) (l_tail : side) :
  rcmultiStep n c = Some c' ->
  evalRCCfg l_tail c -->* evalRCCfg l_tail c'.
Proof.
  revert c. induction n as [|n IH]; intros c H.
  - injection H as <-. apply evstep_refl.
  - cbn [rcmultiStep] in H.
    destruct (rcstep c) as [c1|] eqn:E; [|discriminate].
    eapply evstep_step; [exact (rcstep_sound c c1 l_tail E) | exact (IH c1 H)].
Qed.

Definition evalBCfg (c : CCfg) : Q * tape :=
  evalWindow 0inf 0inf c.

Definition bstep (c : CCfg) : option CCfg :=
  match tm (ccfg_q c, ccfg_cur c) with
  | None => None
  | Some (w, L, q') =>
    let r' := if is_empty_sym (ccfg_r c) && sym_eqb w 0%sym then [] else w :: ccfg_r c in
    match ccfg_l c with
    | [] => Some (mkCCfg q' 0%sym [] r')
    | b :: ls => Some (mkCCfg q' b ls r')
    end
  | Some (w, R, q') =>
    let l' := if is_empty_sym (ccfg_l c) && sym_eqb w 0%sym then [] else w :: ccfg_l c in
    match ccfg_r c with
    | [] => Some (mkCCfg q' 0%sym l' [])
    | b :: rs => Some (mkCCfg q' b l' rs)
    end
  end.

Lemma bstep_sound (c c' : CCfg) :
  bstep c = Some c' ->
  evalBCfg c --> evalBCfg c'.
Proof.
  destruct c as [q cur l r]. unfold bstep; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r].
  destruct (tm (q, cur)) as [[[w d] q']|] eqn:E; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; intro H; injection H as <-;
      apply step_c_spec; unfold step_c, evalBCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r];
      rewrite E; cbn; destruct r as [|b' rs']; cbn;
      try (destruct (sym_eqb_spec w 0%sym) as [->|Hne]; cbn; [rewrite <- const_unfold|]);
      reflexivity.
  - destruct r as [|b rs]; intro H; injection H as <-;
      apply step_c_spec; unfold step_c, evalBCfg, evalWindow; cbn [ccfg_q ccfg_cur ccfg_l ccfg_r];
      rewrite E; cbn; destruct l as [|b' ls']; cbn;
      try (destruct (sym_eqb_spec w 0%sym) as [->|Hne]; cbn; [rewrite <- const_unfold|]);
      reflexivity.
Qed.

Fixpoint bmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match bstep c with
    | Some c1 => bmultiStep n' c1
    | None => None
    end
  end.

Lemma bmultiStep_sound (n : nat) (c c' : CCfg) :
  bmultiStep n c = Some c' ->
  evalBCfg c -->* evalBCfg c'.
Proof.
  revert c. induction n as [|n IH]; intros c H.
  - injection H as <-. apply evstep_refl.
  - cbn [bmultiStep] in H.
    destruct (bstep c) as [c1|] eqn:E; [|discriminate].
    eapply evstep_step; [exact (bstep_sound c c1 E) | exact (IH c1 H)].
Qed.

(* ========================================================================== *)
(* Section 3: Token & RLE Encoding (Tok, Mode, Rle, evalRle, evalRStack)      *)
(* ========================================================================== *)

Inductive Tok := U | M | W | Z | T | P | PTTTM_TAIL.
Inductive Mode := R0 | R1 | R1_ODD.

Definition tok_eqb (a b : Tok) : bool :=
  match a, b with
  | U, U | M, M | W, W | Z, Z | T, T | P, P | PTTTM_TAIL, PTTTM_TAIL => true
  | _, _ => false
  end.

Lemma tok_eqb_spec (a b : Tok) : Bool.reflect (a = b) (tok_eqb a b).
Proof. destruct a, b; cbn; constructor; congruence. Qed.

Definition mode_eqb (a b : Mode) : bool :=
  match a, b with
  | R0, R0 | R1, R1 | R1_ODD, R1_ODD => true
  | _, _ => false
  end.

Lemma mode_eqb_spec (a b : Mode) : Bool.reflect (a = b) (mode_eqb a b).
Proof. destruct a, b; cbn; constructor; congruence. Qed.

Fixpoint word_eqb (w1 w2 : list Tok) : bool :=
  match w1, w2 with
  | [], [] => true
  | t1 :: ts1, t2 :: ts2 => tok_eqb t1 t2 && word_eqb ts1 ts2
  | _, _ => false
  end.

Lemma word_eqb_spec (w1 w2 : list Tok) : Bool.reflect (w1 = w2) (word_eqb w1 w2).
Proof.
  revert w2. induction w1 as [|t1 ts1 IH]; intros [|t2 ts2]; cbn;
    try (constructor; congruence).
  destruct (tok_eqb_spec t1 t2) as [->|Hne]; cbn.
  - destruct (IH ts2) as [->|Hne2]; constructor; congruence.
  - constructor; congruence.
Qed.

Fixpoint isZpWord (w : list Tok) : bool :=
  match w with
  | [] => true
  | Z :: ts => isZpWord ts
  | P :: ts => isZpWord ts
  | _ :: _ => false
  end.

Fixpoint revWord (w : list Tok) : list Tok :=
  match w with
  | [] => []
  | t :: ts => revWord ts ++ [t]
  end.

Lemma revWord_append (w1 w2 : list Tok) :
  revWord (w1 ++ w2) = revWord w2 ++ revWord w1.
Proof.
  induction w1 as [|t ts IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma revWord_revWord (w : list Tok) : revWord (revWord w) = w.
Proof.
  induction w as [|t ts IH]; cbn; [reflexivity|].
  rewrite revWord_append; cbn. rewrite IH. reflexivity.
Qed.

Lemma isZpWord_append (w1 w2 : list Tok) :
  isZpWord (w1 ++ w2) = (isZpWord w1 && isZpWord w2).
Proof.
  induction w1 as [|t ts IH]; cbn; [reflexivity|].
  destruct t; cbn; try reflexivity; exact IH.
Qed.

Lemma isZpWord_revWord (w : list Tok) : isZpWord (revWord w) = isZpWord w.
Proof.
  induction w as [|t ts IH]; cbn; [reflexivity|].
  rewrite isZpWord_append, IH.
  destruct t; cbn; apply andb_true_r || apply andb_false_r.
Qed.

Definition tokL (t : Tok) : list Sym :=
  match t with
  | U => [0; 1]%sym
  | M => [0; 1; 1]%sym
  | W => [0; 0; 1; 1]%sym
  | Z => [0; 0; 0; 0; 1; 1]%sym
  | T => [0; 1; 1; 1]%sym
  | P => [0; 1; 0; 0; 1; 1]%sym
  | PTTTM_TAIL => []
  end.

Definition tokR (t : Tok) : list Sym :=
  match t with
  | Z => [1; 0; 1; 1; 0; 1]%sym
  | P => [0; 0; 1; 1; 0; 1]%sym
  | PTTTM_TAIL => [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym
  | _ => []
  end.

Fixpoint wordL (w : list Tok) : list Sym :=
  match w with
  | [] => []
  | t :: ts => tokL t ++ wordL ts
  end.

Fixpoint wordR (w : list Tok) : list Sym :=
  match w with
  | [] => []
  | t :: ts => tokR t ++ wordR ts
  end.

Lemma wordL_append (w1 w2 : list Tok) :
  wordL (w1 ++ w2) = wordL w1 ++ wordL w2.
Proof.
  induction w1 as [|t ts IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma wordR_append (w1 w2 : list Tok) :
  wordR (w1 ++ w2) = wordR w1 ++ wordR w2.
Proof.
  induction w1 as [|t ts IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Definition Rle := list (list Tok * N).

Fixpoint rle_eqb (r1 r2 : Rle) : bool :=
  match r1, r2 with
  | [], [] => true
  | (w1, c1) :: rest1, (w2, c2) :: rest2 =>
    word_eqb w1 w2 && (c1 =? c2)%N && rle_eqb rest1 rest2
  | _, _ => false
  end.

Lemma rle_eqb_spec (r1 r2 : Rle) : Bool.reflect (r1 = r2) (rle_eqb r1 r2).
Proof.
  revert r2. induction r1 as [|[w1 c1] rest1 IH]; intros [|[w2 c2] rest2]; cbn;
    try (constructor; congruence).
  destruct (word_eqb_spec w1 w2) as [->|Hne1]; cbn; [|constructor; congruence].
  destruct (N.eqb_spec c1 c2) as [->|Hne2]; cbn; [|constructor; congruence].
  destruct (IH rest2) as [->|Hne3]; constructor; congruence.
Qed.

Fixpoint evalRle (rle : Rle) : side :=
  match rle with
  | [] => 0inf
  | (w, c) :: rest => npow (wordL w) c *> evalRle rest
  end.

Fixpoint evalRStack (rs : Rle) (r_end : side) : side :=
  match rs with
  | [] => r_end
  | (w, c) :: rest => npow (wordR w) c *> evalRStack rest r_end
  end.

Definition is_empty_word (w : list Tok) : bool :=
  match w with [] => true | _ => false end.

Definition pushRle (w : list Tok) (c : N) (rle : Rle) : Rle :=
  if (c =? 0)%N || is_empty_word w then rle
  else match rle with
  | (w', c') :: rest =>
    if word_eqb w w' then (w, (c + c')%N) :: rest
    else (w, c) :: rle
  | [] => [(w, c)]
  end.

Lemma evalRle_pushRle (w : list Tok) (c : N) (rle : Rle) :
  evalRle (pushRle w c rle) = npow (wordL w) c *> evalRle rle.
Proof.
  unfold pushRle.
  destruct (N.eqb_spec c 0%N) as [->|Hc]; cbn [orb].
  - rewrite npow_0. reflexivity.
  - destruct w as [|t ts]; cbn [is_empty_word orb].
    + cbn [wordL]. rewrite npow_nil. reflexivity.
    + destruct rle as [|[w' c'] rest]; cbn [evalRle].
      * reflexivity.
      * destruct (word_eqb_spec (t :: ts) w') as [<-|Hne]; cbn [evalRle].
        -- rewrite npow_add, Str_app_assoc. reflexivity.
        -- reflexivity.
Qed.

Lemma evalRStack_pushRle (w : list Tok) (c : N) (rs : Rle) (r_end : side) :
  evalRStack (pushRle w c rs) r_end = npow (wordR w) c *> evalRStack rs r_end.
Proof.
  unfold pushRle.
  destruct (N.eqb_spec c 0%N) as [->|Hc]; cbn [orb].
  - rewrite npow_0. reflexivity.
  - destruct w as [|t ts]; cbn [is_empty_word orb].
    + cbn [wordR]. rewrite npow_nil. reflexivity.
    + destruct rs as [|[w' c'] rest]; cbn [evalRStack].
      * reflexivity.
      * destruct (word_eqb_spec (t :: ts) w') as [<-|Hne]; cbn [evalRStack].
        -- rewrite npow_add, Str_app_assoc. reflexivity.
        -- reflexivity.
Qed.

Lemma evalRle_pushRle_one (w : list Tok) (rle : Rle) :
  evalRle (pushRle w 1%N rle) = wordL w *> evalRle rle.
Proof.
  rewrite evalRle_pushRle, npow_1. reflexivity.
Qed.

Fixpoint pushToksLtr (ts : list Tok) (rle : Rle) : Rle :=
  match ts with
  | [] => rle
  | t :: ts' => pushToksLtr ts' (pushRle [t] 1%N rle)
  end.

Fixpoint popLastTok (rle : Rle) : option (Tok * Rle) :=
  match rle with
  | [] => None
  | ([], _) :: rest => popLastTok rest
  | (t :: ts, c) :: rest =>
    if (c =? 0)%N then popLastTok rest
    else
      let rest' := if (c =? 1)%N then rest else (t :: ts, (c - 1)%N) :: rest in
      Some (t, pushRle ts 1%N rest')
  end.

Lemma popLastTok_sound (rle : Rle) (t : Tok) (rle' : Rle) :
  popLastTok rle = Some (t, rle') ->
  evalRle rle = tokL t *> evalRle rle'.
Proof.
  induction rle as [|[[|t0 ts] c] rest IH]; intro H.
  - discriminate.
  - cbn [popLastTok] in H. cbn [evalRle wordL]. rewrite npow_nil. cbn [Str_app].
    exact (IH H).
  - cbn [popLastTok] in H.
    destruct (N.eqb_spec c 0%N) as [->|Hc0].
    + cbn [evalRle]. rewrite npow_0. cbn [Str_app]. exact (IH H).
    + injection H as <- <-.
      destruct (N.eqb_spec c 1%N) as [->|Hc1].
      * cbn [evalRle]. rewrite evalRle_pushRle, !npow_1. cbn [wordL].
        rewrite Str_app_assoc. reflexivity.
      * cbn [evalRle]. rewrite evalRle_pushRle, npow_1.
        replace c with (1 + (c - 1))%N at 1 by lia.
        rewrite npow_add, npow_1. cbn [evalRle wordL].
        rewrite !Str_app_assoc. reflexivity.
Qed.

(* ========================================================================== *)
(* Section 4: Named Configurations & 59 Verified Micro-Step Lemmas            *)
(* ========================================================================== *)

Definition evalWK (k1 : N) : side :=
  [1; 0; 1; 1]%sym *> (npow [0; 0; 1; 1]%sym k1 *> 0inf).

Definition cfgR (l : side) : Q * tape :=
  (B, ([1; 1]%sym *> l, 0%sym, 0inf)).

Definition carryCfg (l r : side) : Q * tape :=
  (B, (l, 1%sym, [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).

Definition r0Cfg (l r : side) : Q * tape :=
  (E, ([0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym *> l, 0%sym, r)).

Definition r1Cfg (l r : side) : Q * tape :=
  (E, ([0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym *> l, 0%sym, r)).

Definition r1OddShortCfg (l r : side) : Q * tape :=
  (B, ([1; 1; 0; 0; 0; 0; 1; 1]%sym *> l, 1%sym, r)).

Definition r1OddCfg (l r : side) : Q * tape :=
  r1OddShortCfg (tokL Z *> l) r.

Definition wSweepCfg (l r : side) : Q * tape :=
  (D, (l, 1%sym, [1]%sym *> r)).

Definition dSweepCfg (l r : side) : Q * tape :=
  (E, ([0; 1; 1]%sym *> l, 1%sym, r)).

Definition tSweepCfg (l r : side) : Q * tape :=
  (E, ([0; 0; 0; 0; 1; 1]%sym *> l, 0%sym, r)).

Definition t3Cfg (l r : side) : Q * tape :=
  (B, (l, 1%sym, [0; 1; 0; 0; 1]%sym *> r)).

Definition pmuCfg (l r : side) : Q * tape :=
  (D, (l, 1%sym, [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).

Lemma init_to_carry0 :
  c0 -->* carryCfg (tokL M *> (tokL U *> 0inf)) (evalWK 1%N).
Proof.
  apply (bmultiStep_sound 307
    (mkCCfg A 0%sym [] [])
    (mkCCfg B 1%sym [0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym)).
  vm_compute. reflexivity.
Qed.

Lemma carry_Z (l r : side) :
  carryCfg (tokL Z *> l) r -->* carryCfg l (tokR Z *> r).
Proof.
  apply (wmultiStep_sound 48
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_P (l r : side) :
  carryCfg (tokL P *> l) r -->* carryCfg l (tokR P *> r).
Proof.
  apply (wmultiStep_sound 16
    (mkCCfg B 1%sym [0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_PMUTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL U *> (tokL M *> (tokL P *> l))))) r -->*
  carryCfg l (npow (tokR Z) 2%N *> (tokR P *> r)).
Proof.
  apply (wmultiStep_sound 68
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_PTTW (l r : side) :
  carryCfg (tokL W *> (npow (tokL T) 2%N *> (tokL P *> l))) r -->*
  carryCfg l (npow (tokR Z) 3%N *> r).
Proof.
  apply (wmultiStep_sound 104
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_PTTT (l r : side) :
  carryCfg (npow (tokL T) 3%N *> (tokL P *> l)) r -->*
  carryCfg l (npow (tokR Z) 2%N *> (tokR P *> r)).
Proof.
  apply (wmultiStep_sound 72
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_PTTTM (l r : side) :
  carryCfg (tokL M *> (npow (tokL T) 3%N *> (tokL P *> l))) r -->*
  carryCfg l (npow (tokR Z) 2%N *> (tokR PTTTM_TAIL *> r)).
Proof.
  apply (wmultiStep_sound 85
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_UM (r : side) :
  carryCfg (tokL M *> (tokL U *> 0inf)) r -->*
  r1Cfg (tokL M *> (tokL U *> 0inf)) r.
Proof.
  apply (cmultiStep_sound 57
    (mkCCfg B 1%sym [0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym []) r).
  vm_compute. reflexivity.
Qed.

Lemma turn_UMT (r : side) :
  carryCfg (tokL T *> (tokL M *> (tokL U *> 0inf))) r -->*
  r1Cfg (tokL Z *> (tokL U *> 0inf)) r.
Proof.
  apply (cmultiStep_sound 89
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1]%sym []) r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZT (l r : side) :
  carryCfg (tokL T *> (tokL Z *> l)) r -->* r1Cfg (tokL M *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 57
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_WM (l r : side) :
  carryCfg (tokL M *> (tokL W *> l)) r -->* r1Cfg (tokL T *> l) r.
Proof.
  apply (wmultiStep_sound 51
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PT (l r : side) :
  carryCfg (tokL T *> (tokL P *> l)) r -->* r0Cfg (tokL P *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 105
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZM (l r : side) :
  carryCfg (tokL M *> (tokL Z *> l)) r -->* r1Cfg (tokL P *> l) r.
Proof.
  apply (wmultiStep_sound 51
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PTW (l r : side) :
  carryCfg (tokL W *> (tokL T *> (tokL P *> l))) r -->*
  r1OddCfg (tokL Z *> (tokL U *> (tokL M *> l))) r.
Proof.
  apply (wmultiStep_sound 127
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL P *> l))) r -->*
  r1Cfg (tokL Z *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 89
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PTT (l r : side) :
  carryCfg (tokL T *> (tokL T *> (tokL P *> l))) r -->*
  r1Cfg (tokL Z *> (tokL U *> (tokL M *> l))) r.
Proof.
  apply (wmultiStep_sound 93
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZMU (l r : side) :
  carryCfg (tokL U *> (tokL M *> (tokL Z *> l))) r -->*
  r1OddCfg (tokL T *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 101
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL Z *> l))) r -->*
  r0Cfg (tokL P *> (tokL M *> (tokL T *> l))) r.
Proof.
  apply (wmultiStep_sound 111
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZTT (l r : side) :
  carryCfg (tokL T *> (tokL T *> (tokL Z *> l))) r -->*
  r0Cfg (tokL P *> (tokL W *> (tokL T *> l))) r.
Proof.
  apply (wmultiStep_sound 115
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZTW (l r : side) :
  carryCfg (tokL W *> (tokL T *> (tokL Z *> l))) r -->*
  r0Cfg (tokL Z *> (tokL W *> (tokL T *> l))) r.
Proof.
  apply (wmultiStep_sound 115
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_MUTW (l r : side) :
  carryCfg (tokL W *> (tokL T *> (tokL U *> (tokL M *> l)))) r -->*
  r1OddCfg (tokL Z *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 127
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PTTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL T *> (tokL P *> l)))) r -->*
  r0Cfg (tokL P *> (tokL Z *> (tokL U *> (tokL M *> l)))) r.
Proof.
  apply (wmultiStep_sound 147
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZTTW (l r : side) :
  carryCfg (tokL W *> (tokL T *> (tokL T *> (tokL Z *> l)))) r -->*
  r0Cfg (tokL Z *> (tokL Z *> (tokL P *> l))) r.
Proof.
  apply (wmultiStep_sound 147
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZTTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL T *> (tokL Z *> l)))) r -->*
  r1Cfg (tokL Z *> (tokL W *> (tokL T *> l))) r.
Proof.
  apply (wmultiStep_sound 99
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZPMU (l r : side) :
  carryCfg (tokL U *> (tokL M *> (tokL P *> (tokL Z *> l)))) r -->*
  r0Cfg (tokL P *> (tokL M *> (tokL W *> (tokL T *> l)))) r.
Proof.
  apply (wmultiStep_sound 147
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_ZMUTM (l r : side) :
  carryCfg (tokL M *> (tokL T *> (tokL U *> (tokL M *> (tokL Z *> l))))) r -->*
  r0Cfg (tokL P *> (tokL Z *> (tokL P *> l))) r.
Proof.
  apply (wmultiStep_sound 143
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma turn_PTTTW (l r : side) :
  carryCfg (tokL W *> (tokL T *> (tokL T *> (tokL T *> (tokL P *> l))))) r -->*
  r0Cfg (tokL Z *> (tokL Z *> (tokL Z *> (tokL T *> l)))) r.
Proof.
  apply (wmultiStep_sound 185
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma carry_MU_to_pmuCfg (l r : side) :
  carryCfg (tokL U *> (tokL M *> l)) r -->* pmuCfg l (tokR P *> r).
Proof.
  apply (wmultiStep_sound 15
    (mkCCfg B 1%sym [0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [] [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma pmu_step (l r : side) :
  pmuCfg (tokL P *> l) r -->* pmuCfg l (tokR Z *> r).
Proof.
  apply (wmultiStep_sound 52
    (mkCCfg D 1%sym [0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [] [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma pmuCfg_Z_turn (l r : side) :
  pmuCfg (tokL Z *> l) (tokR Z *> r) -->* r0Cfg (tokL M *> (tokL W *> (tokL T *> l))) r.
Proof.
  apply (wmultiStep_sound 36
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma pmuCfg_TM_halt (l r : side) :
  pmuCfg (tokL M *> (tokL T *> l)) r -->*
  (F, (l, 1%sym, [1; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).
Proof.
  apply (wmultiStep_sound 21
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg F 1%sym [] [1; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma r0_Z (l r : side) :
  r0Cfg l (tokR Z *> r) -->* r0Cfg (tokL Z *> l) r.
Proof.
  apply (wmultiStep_sound 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r0_P (l r : side) :
  r0Cfg l (tokR P *> r) -->* r0Cfg (tokL P *> l) r.
Proof.
  apply (wmultiStep_sound 44
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r0_PTTTM_TAIL (l r : side) :
  r0Cfg l (tokR PTTTM_TAIL *> r) -->* r1Cfg (tokL Z *> l) r.
Proof.
  apply (wmultiStep_sound 15
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1_Z (l r : side) :
  r1Cfg l (tokR Z *> r) -->* r0Cfg (tokL M *> (tokL Z *> l)) r.
Proof.
  apply (wmultiStep_sound 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1_P (l r : side) :
  r1Cfg l (tokR P *> r) -->* r1OddCfg (tokL P *> l) r.
Proof.
  apply (wmultiStep_sound 62
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1OddShort_Z (l r : side) :
  r1OddShortCfg l (tokR Z *> r) -->* r1OddShortCfg (tokL Z *> l) r.
Proof.
  apply (wmultiStep_sound 12
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1Odd_P (l r : side) :
  r1OddCfg l (tokR P *> r) -->* r1Cfg (tokL Z *> l) r.
Proof.
  apply (wmultiStep_sound 10
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_start (l : side) :
  cfgR l -->* wSweepCfg l 0inf.
Proof.
  apply (rcmultiStep_sound 2
    (mkCCfg B 0%sym [1; 1]%sym [])
    (mkCCfg D 1%sym [] [1]%sym) l).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_step (l r : side) :
  wSweepCfg (tokL W *> l) r -->* wSweepCfg l ([0; 0; 1; 1]%sym *> r).
Proof.
  apply (wmultiStep_sound 4
    (mkCCfg D 1%sym [0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg D 1%sym [] [1; 0; 0; 1; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma dSweep_step (l r : side) :
  dSweepCfg l ([0; 0; 1; 1]%sym *> r) -->* dSweepCfg (tokL W *> l) r.
Proof.
  apply (wmultiStep_sound 6
    (mkCCfg E 1%sym [0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma dSweep_end (l : side) :
  dSweepCfg l 0inf -->* cfgR (tokL W *> l).
Proof.
  apply (rcmultiStep_sound 5
    (mkCCfg E 1%sym [0; 1; 1]%sym [])
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1]%sym []) l).
  vm_compute. reflexivity.
Qed.

Lemma tSweep_step (l r : side) :
  tSweepCfg l ([0; 0; 1; 1]%sym *> r) -->* tSweepCfg (tokL T *> l) r.
Proof.
  apply (wmultiStep_sound 22
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma tSweep_end (l : side) :
  tSweepCfg l 0inf -->* cfgR (tokL Z *> l).
Proof.
  apply (rcmultiStep_sound 2
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym [])
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []) l).
  vm_compute. reflexivity.
Qed.

Lemma r0_to_dSweep (l r : side) :
  r0Cfg l ([1; 0; 1; 1]%sym *> r) -->* dSweepCfg (tokL Z *> (tokL Z *> l)) r.
Proof.
  apply (wmultiStep_sound 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1_to_dSweep (l r : side) :
  r1Cfg l ([1; 0; 1; 1]%sym *> r) -->* dSweepCfg (tokL Z *> (tokL M *> (tokL Z *> l))) r.
Proof.
  apply (wmultiStep_sound 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1Odd_to_tSweep (l r : side) :
  r1OddCfg l ([1; 0; 1; 1]%sym *> r) -->* tSweepCfg (tokL Z *> (tokL Z *> l)) r.
Proof.
  apply (wmultiStep_sound 10
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_Z_to_dSweep (l r : side) :
  wSweepCfg (tokL Z *> l) r -->* dSweepCfg (tokL T *> l) r.
Proof.
  apply (wmultiStep_sound 9
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_ZT_to_dSweep (l r : side) :
  wSweepCfg (tokL T *> (tokL Z *> l)) ([0; 0; 1; 1]%sym *> r) -->*
  dSweepCfg (tokL Z *> (tokL P *> l)) r.
Proof.
  apply (wmultiStep_sound 47
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_PT_to_carry (l r : side) :
  wSweepCfg (tokL T *> (tokL P *> l)) ([0; 0; 1; 1]%sym *> r) -->*
  carryCfg l ([1; 0; 1; 1]%sym *> r).
Proof.
  apply (wmultiStep_sound 34
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma wSweep_ZMT_to_tSweep (l r : side) :
  wSweepCfg (tokL T *> (tokL M *> (tokL Z *> l))) ([0; 0; 1; 1]%sym *> r) -->*
  tSweepCfg (tokL Z *> (tokL P *> l)) r.
Proof.
  apply (wmultiStep_sound 69
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma cfgR_Z_to_TW (l : side) :
  cfgR (tokL Z *> l) -->* cfgR (tokL W *> (tokL T *> l)).
Proof.
  apply (rcmultiStep_sound 16
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [])
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l).
  vm_compute. reflexivity.
Qed.

Lemma cfgR_TW_to_t3Cfg (l : side) :
  cfgR (tokL W *> (tokL T *> l)) -->* t3Cfg l (evalWK 0%N).
Proof.
  apply (rcmultiStep_sound 24
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym [])
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym) l).
  vm_compute. reflexivity.
Qed.

Lemma t3_step (l r : side) :
  t3Cfg (npow (tokL T) 3%N *> l) r -->* t3Cfg l (npow (tokR Z) 2%N *> r).
Proof.
  apply (wmultiStep_sound 56
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r).
  vm_compute. reflexivity.
Qed.

Lemma t3Cfg_Z_zero_to_carry (l : side) :
  t3Cfg (tokL Z *> l) (evalWK 0%N) -->* carryCfg l (evalWK 1%N).
Proof.
  apply (rcmultiStep_sound 104
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l).
  vm_compute. reflexivity.
Qed.

Lemma t3Cfg_Z_succ_to_r0 (l r : side) :
  t3Cfg (tokL Z *> l) (tokR Z *> r) -->* r0Cfg (tokL P *> l) r.
Proof.
  apply (wmultiStep_sound 35
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma t3Cfg_TZ_to_r1OddShort (l r : side) :
  t3Cfg (tokL T *> (tokL Z *> l)) r -->* r1OddShortCfg (tokL M *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 47
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1OddShortCfg_evalWK0_to_carry (l : side) :
  r1OddShortCfg l (evalWK 0%N) -->* carryCfg l (evalWK 1%N).
Proof.
  apply (rcmultiStep_sound 156
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym [] [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l).
  vm_compute. reflexivity.
Qed.

Lemma t3Cfg_TTZ_to_r0 (l r : side) :
  t3Cfg (npow (tokL T) 2%N *> (tokL Z *> l)) r -->* r0Cfg (tokL W *> (tokL T *> l)) r.
Proof.
  apply (wmultiStep_sound 71
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []) l r).
  vm_compute. reflexivity.
Qed.

Lemma r1Odd_Z (l r : side) :
  r1OddCfg l (tokR Z *> r) -->* r1OddCfg (tokL Z *> l) r.
Proof.
  exact (r1OddShort_Z (tokL Z *> l) r).
Qed.

(* ========================================================================== *)
(* Section 5: Loop & Suffix Transition Lemmas                                 *)
(* ========================================================================== *)

Lemma wSweep_loop (n : N) : forall (l r : side),
  wSweepCfg (npow (tokL W) n *> l) r -->*
  wSweepCfg l (npow [0; 0; 1; 1]%sym n *> r).
Proof.
  induction n as [|n IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply wSweep_step |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma dSweep_loop (n : N) : forall (l r : side),
  dSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -->*
  dSweepCfg (npow (tokL W) n *> l) r.
Proof.
  induction n as [|n IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply dSweep_step |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma tSweep_loop (n : N) : forall (l r : side),
  tSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -->*
  tSweepCfg (npow (tokL T) n *> l) r.
Proof.
  induction n as [|n IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply tSweep_step |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma t3_loop (q : N) : forall (l r : side),
  t3Cfg (npow (tokL T) (3 * q)%N *> l) r -->*
  t3Cfg l (npow (tokR Z) (2 * q)%N *> r).
Proof.
  induction q as [|q IH] using N.peano_ind; intros l r.
  - cbn [N.mul]; rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - replace (3 * N.succ q)%N with (3 + 3 * q)%N by lia.
    replace (2 * N.succ q)%N with (2 * q + 2)%N by lia.
    rewrite npow_add, Str_app_assoc.
    eapply evstep_trans; [apply t3_step |].
    rewrite npow_add, Str_app_assoc.
    apply IH.
Qed.

Lemma pmu_loop (m : N) : forall (l r : side),
  pmuCfg (npow (tokL P) m *> l) r -->*
  pmuCfg l (npow (tokR Z) m *> r).
Proof.
  induction m as [|m IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply pmu_step |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma r0_Z_loop (m : N) : forall (l r : side),
  r0Cfg l (npow (tokR Z) m *> r) -->*
  r0Cfg (npow (tokL Z) m *> l) r.
Proof.
  induction m as [|m IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_Z |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma r0_P_loop (m : N) : forall (l r : side),
  r0Cfg l (npow (tokR P) m *> r) -->*
  r0Cfg (npow (tokL P) m *> l) r.
Proof.
  induction m as [|m IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_P |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma r1OddShort_Z_loop (m : N) : forall (l r : side),
  r1OddShortCfg l (npow (tokR Z) m *> r) -->*
  r1OddShortCfg (npow (tokL Z) m *> l) r.
Proof.
  induction m as [|m IH] using N.peano_ind; intros l r.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r1OddShort_Z |].
    rewrite npow_succ_r, Str_app_assoc.
    apply IH.
Qed.

Lemma cfgR_ZW_to_TW (n : N) (l : side) :
  cfgR (npow (tokL W) n *> (tokL Z *> l)) -->*
  cfgR (npow (tokL W) (n + 1)%N *> (tokL T *> l)).
Proof.
  eapply evstep_trans; [apply wSweep_start |].
  eapply evstep_trans; [apply wSweep_loop |].
  eapply evstep_trans; [apply wSweep_Z_to_dSweep |].
  eapply evstep_trans; [apply dSweep_loop |].
  rewrite npow_succ_l, Str_app_assoc.
  apply dSweep_end.
Qed.

Lemma npow_add_1_l (l : list Sym) (n : N) (r : side) :
  npow l (n + 1)%N *> r = l *> (npow l n *> r).
Proof.
  rewrite npow_succ_l, Str_app_assoc. reflexivity.
Qed.

Lemma r0_end (k1 : N) (l : side) :
  r0Cfg l (evalWK k1) -->* carryCfg l (evalWK (k1 + 2)%N).
Proof.
  unfold evalWK.
  eapply evstep_trans; [apply r0_to_dSweep |].
  eapply evstep_trans; [apply dSweep_loop |].
  eapply evstep_trans; [apply dSweep_end |].
  rewrite <- (npow_add_1_l (tokL W) k1).
  eapply evstep_trans; [apply cfgR_ZW_to_TW |].
  eapply evstep_trans; [apply wSweep_start |].
  eapply evstep_trans; [apply wSweep_loop |].
  rewrite (npow_add_1_l [0; 0; 1; 1]%sym (k1 + 1)%N).
  eapply evstep_trans; [apply wSweep_ZT_to_dSweep |].
  eapply evstep_trans; [apply dSweep_loop |].
  eapply evstep_trans; [apply dSweep_end |].
  rewrite <- (npow_add_1_l (tokL W) (k1 + 1)%N).
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply cfgR_ZW_to_TW |].
  eapply evstep_trans; [apply wSweep_start |].
  eapply evstep_trans; [apply wSweep_loop |].
  rewrite (npow_add_1_l [0; 0; 1; 1]%sym (k1 + 2)%N).
  apply wSweep_PT_to_carry.
Qed.

Lemma r1_end (kf1 : N) (l : side) :
  r1Cfg l (evalWK kf1) -->*
  t3Cfg (npow (tokL T) (kf1 + 1)%N *> (tokL Z *> (tokL P *> l))) (evalWK 0%N).
Proof.
  unfold evalWK.
  eapply evstep_trans; [apply r1_to_dSweep |].
  eapply evstep_trans; [apply dSweep_loop |].
  eapply evstep_trans; [apply dSweep_end |].
  rewrite <- (npow_add_1_l (tokL W) kf1).
  eapply evstep_trans; [apply cfgR_ZW_to_TW |].
  eapply evstep_trans; [apply wSweep_start |].
  eapply evstep_trans; [apply wSweep_loop |].
  rewrite (npow_add_1_l [0; 0; 1; 1]%sym (kf1 + 1)%N).
  eapply evstep_trans; [apply wSweep_ZMT_to_tSweep |].
  eapply evstep_trans; [apply tSweep_loop |].
  eapply evstep_trans; [apply tSweep_end |].
  eapply evstep_trans; [apply cfgR_Z_to_TW |].
  apply cfgR_TW_to_t3Cfg.
Qed.

Lemma r1Odd_end (kf1 : N) (l : side) :
  r1OddCfg l (evalWK kf1) -->*
  t3Cfg (npow (tokL T) kf1 *> (tokL Z *> (tokL Z *> l))) (evalWK 0%N).
Proof.
  unfold evalWK.
  eapply evstep_trans; [apply r1Odd_to_tSweep |].
  eapply evstep_trans; [apply tSweep_loop |].
  eapply evstep_trans; [apply tSweep_end |].
  eapply evstep_trans; [apply cfgR_Z_to_TW |].
  apply cfgR_TW_to_t3Cfg.
Qed.

Definition stepZtToCarry (rle2 : Rle) (n : N) : Rle * N :=
  let q := (n / 3)%N in
  let rem := (n mod 3)%N in
  if (rem =? 0)%N then
    if (q =? 0)%N then (rle2, 1%N)
    else (pushRle [Z] (2 * q - 1)%N (pushRle [P] 1%N rle2), 2%N)
  else if (rem =? 1)%N then
    (pushRle [Z] (2 * q)%N (pushToksLtr [T; M] rle2), 1%N)
  else
    (pushRle [Z] (2 * q)%N (pushToksLtr [T; W] rle2), 2%N).

Lemma stepZtToCarry_sound (rle2 : Rle) (n : N) :
  t3Cfg (npow (tokL T) n *> (tokL Z *> evalRle rle2)) (evalWK 0%N) -->*
  carryCfg (evalRle (fst (stepZtToCarry rle2 n))) (evalWK (snd (stepZtToCarry rle2 n))).
Proof.
  unfold stepZtToCarry; cbv zeta.
  remember (n / 3)%N as q eqn:Eq.
  remember (n mod 3)%N as rem eqn:Erem.
  assert (Hdiv : n = (3 * q + rem)%N) by lia.
  assert (Hrem : (rem = 0 \/ rem = 1 \/ rem = 2)%N) by lia.
  clear Eq Erem.
  rewrite Hdiv, npow_add, Str_app_assoc.
  eapply evstep_trans; [apply t3_loop |].
  destruct (N.eqb_spec rem 0%N) as [->|Hne0]; cbn [fst snd].
  - rewrite npow_0; cbn [Str_app].
    destruct (N.eqb_spec q 0%N) as [->|Hq0]; cbn [fst snd].
    + cbn [N.mul]; rewrite npow_0; cbn [Str_app]. apply t3Cfg_Z_zero_to_carry.
    + rewrite !evalRle_pushRle, npow_1; cbn [wordL]; rewrite !app_nil_r.
      replace (2 * q)%N with (1 + (2 * q - 1))%N at 1 by lia.
      rewrite npow_add, npow_1, Str_app_assoc.
      eapply evstep_trans; [apply t3Cfg_Z_succ_to_r0 |].
      eapply evstep_trans; [apply r0_Z_loop |].
      apply (r0_end 0%N).
  - destruct (N.eqb_spec rem 1%N) as [->|Hne1]; cbn [fst snd].
    + rewrite npow_1.
      cbn [pushToksLtr]; rewrite !evalRle_pushRle, !npow_1; cbn [wordL]; rewrite !app_nil_r.
      eapply evstep_trans; [apply t3Cfg_TZ_to_r1OddShort |].
      eapply evstep_trans; [apply r1OddShort_Z_loop |].
      apply r1OddShortCfg_evalWK0_to_carry.
    + assert (rem = 2%N) as -> by lia.
      cbn [pushToksLtr]; rewrite !evalRle_pushRle, !npow_1; cbn [wordL]; rewrite !app_nil_r.
      eapply evstep_trans; [apply t3Cfg_TTZ_to_r0 |].
      eapply evstep_trans; [apply r0_Z_loop |].
      apply (r0_end 0%N).
Qed.


(* ========================================================================== *)
(* Section 6: RLE Combinators & Sweep Soundness Lemmas                        *)
(* ========================================================================== *)

Definition popTok (t_exp : Tok) (rle : Rle) : option Rle :=
  match popLastTok rle with
  | Some (t, rle') => if tok_eqb t t_exp then Some rle' else None
  | None => None
  end.

Lemma popTok_sound (t_exp : Tok) (rle rle' : Rle) :
  popTok t_exp rle = Some rle' ->
  evalRle rle = tokL t_exp *> evalRle rle'.
Proof.
  unfold popTok.
  destruct (popLastTok rle) as [[t r]|] eqn:Hp; [|discriminate].
  destruct (tok_eqb_spec t t_exp) as [->|]; [|discriminate].
  intro H; injection H as <-.
  exact (popLastTok_sound rle t_exp r Hp).
Qed.

Fixpoint popToks (ts : list Tok) (rle : Rle) : option Rle :=
  match ts with
  | [] => Some rle
  | t :: ts' =>
    match popTok t rle with
    | Some rle' => popToks ts' rle'
    | None => None
    end
  end.

Lemma popToks_sound (ts : list Tok) : forall (rle rle' : Rle),
  popToks ts rle = Some rle' ->
  evalRle rle = wordL ts *> evalRle rle'.
Proof.
  induction ts as [|t ts' IH]; intros rle rle' H; cbn [popToks] in H.
  - injection H as <-. reflexivity.
  - destruct (popTok t rle) as [r1|] eqn:H1; [|discriminate].
    rewrite (popTok_sound t rle r1 H1), (IH r1 rle' H).
    cbn [wordL]. rewrite Str_app_assoc. reflexivity.
Qed.

Definition matchHeadAnyCount (w_exp : list Tok) (rle : Rle) : option (N * Rle) :=
  match rle with
  | (w, c) :: rest => if word_eqb w w_exp && (0 <? c)%N then Some (c, rest) else None
  | [] => None
  end.

Lemma matchHeadAnyCount_sound (w_exp : list Tok) (rle rest : Rle) (c : N) :
  matchHeadAnyCount w_exp rle = Some (c, rest) ->
  (0 < c)%N /\ evalRle rle = npow (wordL w_exp) c *> evalRle rest.
Proof.
  destruct rle as [|[w c0] tl]; [discriminate|].
  unfold matchHeadAnyCount.
  destruct (word_eqb_spec w w_exp) as [->|]; cbn [andb]; [|discriminate].
  destruct (N.ltb_spec 0%N c0) as [Hc0|]; [|discriminate].
  intro H; injection H as <- <-.
  split; [exact Hc0 | reflexivity].
Qed.

Definition popPrefixCount (pref w_exp : list Tok) (rle : Rle) : option (N * Rle) :=
  match popToks pref rle with
  | Some r1 => matchHeadAnyCount w_exp r1
  | None => None
  end.

Lemma popPrefixCount_sound (pref w_exp : list Tok) (rle r3 : Rle) (b : N) :
  popPrefixCount pref w_exp rle = Some (b, r3) ->
  (0 < b)%N /\ evalRle rle = wordL pref *> (npow (wordL w_exp) b *> evalRle r3).
Proof.
  unfold popPrefixCount.
  destruct (popToks pref rle) as [r1|] eqn:H1; [|discriminate].
  intro H.
  destruct (matchHeadAnyCount_sound w_exp r1 r3 b H) as [Hb Hr1].
  rewrite (popToks_sound pref rle r1 H1), Hr1.
  split; [exact Hb | reflexivity].
Qed.

Lemma carry_word (w : list Tok) : forall (l r : side),
  isZpWord w = true ->
  carryCfg (wordL w *> l) r -->* carryCfg l (wordR (revWord w) *> r).
Proof.
  induction w as [|t ts IH]; intros l r H; cbn [isZpWord] in H.
  - cbn [wordL revWord wordR Str_app]. apply evstep_refl.
  - destruct t; try discriminate;
      cbn [wordL revWord]; rewrite Str_app_assoc, wordR_append, Str_app_assoc.
    + eapply evstep_trans; [apply carry_Z |]. apply (IH l (tokR Z *> r) H).
    + eapply evstep_trans; [apply carry_P |]. apply (IH l (tokR P *> r) H).
Qed.

Lemma carry_pow (c : N) (w : list Tok) : forall (l r : side),
  isZpWord w = true ->
  carryCfg (npow (wordL w) c *> l) r -->*
  carryCfg l (npow (wordR (revWord w)) c *> r).
Proof.
  induction c as [|c IH] using N.peano_ind; intros l r Hw.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply (carry_word w _ _ Hw) |].
    rewrite npow_succ_r, Str_app_assoc.
    apply (IH l _ Hw).
Qed.

Definition popCarrySpecial (rle rs : Rle) : option (Rle * Rle) :=
  match popToks [M; T; U; M; P] rle with
  | Some r' => Some (r', pushRle [Z] 2%N (pushRle [P] 1%N rs))
  | None => match popToks [M; T; T; T; P] rle with
  | Some r' => Some (r', pushRle [Z] 2%N (pushRle [PTTTM_TAIL] 1%N rs))
  | None => match popToks [W; T; T; P] rle with
  | Some r' => Some (r', pushRle [Z] 3%N rs)
  | None => match popToks [T; T; T; P] rle with
  | Some r' => Some (r', pushRle [Z] 2%N (pushRle [P] 1%N rs))
  | None => None
  end end end end.

Lemma popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : side) :
  popCarrySpecial rle rs = Some (rle', rs') ->
  carryCfg (evalRle rle) (evalRStack rs r_end) -->*
  carryCfg (evalRle rle') (evalRStack rs' r_end).
Proof.
  unfold popCarrySpecial.
  destruct (popToks [M; T; U; M; P] rle) as [r1|] eqn:H1.
  - intro H; injection H as <- <-.
    rewrite (popToks_sound _ _ _ H1), !evalRStack_pushRle, npow_1.
    cbn [wordL wordR]; rewrite !app_nil_r, !Str_app_assoc.
    apply carry_PMUTM.
  - destruct (popToks [M; T; T; T; P] rle) as [r2|] eqn:H2.
    + intro H; injection H as <- <-.
      rewrite (popToks_sound _ _ _ H2), !evalRStack_pushRle, npow_1.
      cbn [wordL wordR]; rewrite !app_nil_r, !Str_app_assoc.
      exact (carry_PTTTM (evalRle r2) (evalRStack rs r_end)).
    + destruct (popToks [W; T; T; P] rle) as [r3|] eqn:H3.
      * intro H; injection H as <- <-.
        rewrite (popToks_sound _ _ _ H3), !evalRStack_pushRle.
        cbn [wordL wordR]; rewrite !app_nil_r, !Str_app_assoc.
        exact (carry_PTTW (evalRle r3) (evalRStack rs r_end)).
      * destruct (popToks [T; T; T; P] rle) as [r4|] eqn:H4; [|discriminate].
        intro H; injection H as <- <-.
        rewrite (popToks_sound _ _ _ H4), !evalRStack_pushRle, npow_1.
        cbn [wordL wordR]; rewrite !app_nil_r, !Str_app_assoc.
        exact (carry_PTTT (evalRle r4) (evalRStack rs r_end)).
Qed.

Fixpoint popCarryLoop (fuel : nat) (rle rs : Rle) : Rle * Rle :=
  match fuel with
  | O => (rle, rs)
  | S fuel' =>
    match rle with
    | (w, c) :: rest =>
      if isZpWord w then
        popCarryLoop fuel' rest (pushRle (revWord w) c rs)
      else match popCarrySpecial rle rs with
      | Some (rle', rs') => popCarryLoop fuel' rle' rs'
      | None => (rle, rs)
      end
    | [] => ([], rs)
    end
  end.

Lemma popCarryLoop_sound (fuel : nat) : forall (rle rs : Rle) (r_end : side),
  carryCfg (evalRle rle) (evalRStack rs r_end) -->*
  carryCfg (evalRle (fst (popCarryLoop fuel rle rs)))
           (evalRStack (snd (popCarryLoop fuel rle rs)) r_end).
Proof.
  induction fuel as [|fuel IH]; intros rle rs r_end; cbn [popCarryLoop].
  - apply evstep_refl.
  - destruct rle as [|[w c] rest]; [apply evstep_refl|].
    destruct (isZpWord w) eqn:Hw.
    + cbn [evalRle].
      eapply evstep_trans; [apply (carry_pow c w _ _ Hw) |].
      rewrite <- evalRStack_pushRle.
      apply IH.
    + destruct (popCarrySpecial ((w, c) :: rest) rs) as [[rle' rs']|] eqn:Hp.
      * eapply evstep_trans; [exact (popCarrySpecial_sound _ _ _ _ r_end Hp) |].
        apply IH.
      * apply evstep_refl.
Qed.

Lemma r0_word (w : list Tok) : forall (l r : side),
  isZpWord w = true ->
  r0Cfg l (wordR w *> r) -->* r0Cfg (wordL (revWord w) *> l) r.
Proof.
  induction w as [|t ts IH]; intros l r H; cbn [isZpWord] in H.
  - cbn [wordR revWord wordL Str_app]. apply evstep_refl.
  - destruct t; try discriminate;
      cbn [wordR revWord]; rewrite Str_app_assoc, wordL_append, Str_app_assoc.
    + eapply evstep_trans; [apply r0_Z |]. apply (IH (tokL Z *> l) r H).
    + eapply evstep_trans; [apply r0_P |]. apply (IH (tokL P *> l) r H).
Qed.

Lemma r0_pow (c : N) (w : list Tok) : forall (l r : side),
  isZpWord w = true ->
  r0Cfg l (npow (wordR w) c *> r) -->*
  r0Cfg (npow (wordL (revWord w)) c *> l) r.
Proof.
  induction c as [|c IH] using N.peano_ind; intros l r Hw.
  - rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply (r0_word w _ _ Hw) |].
    rewrite npow_succ_r, Str_app_assoc.
    apply (IH _ r Hw).
Qed.

Fixpoint allZpStack (rs : Rle) : bool :=
  match rs with
  | [] => true
  | (it, _) :: rest => isZpWord it && allZpStack rest
  end.

Fixpoint copyRStack (rle : Rle) (rs : Rle) : option Rle :=
  match rs with
  | [] => Some rle
  | (item, count) :: rest =>
    if isZpWord item then copyRStack (pushRle (revWord item) count rle) rest
    else None
  end.

Lemma copyRStack_sound (rs : Rle) : forall (rle rle' : Rle) (r_end : side),
  copyRStack rle rs = Some rle' ->
  allZpStack rs = true /\
  (r0Cfg (evalRle rle) (evalRStack rs r_end) -->* r0Cfg (evalRle rle') r_end).
Proof.
  induction rs as [|[w c] rest IH]; intros rle rle' r_end H; cbn [copyRStack] in H.
  - injection H as <-. split; [reflexivity | apply evstep_refl].
  - destruct (isZpWord w) eqn:Hw; [|discriminate].
    destruct (IH (pushRle (revWord w) c rle) rle' r_end H) as [Hrest Hstep].
    cbn [allZpStack evalRStack]. rewrite Hw, Hrest.
    split; [reflexivity|].
    eapply evstep_trans; [apply (r0_pow c w (evalRle rle) _ Hw) |].
    rewrite <- evalRle_pushRle. exact Hstep.
Qed.

Definition HasRoundtrip (R : N -> side) : Prop :=
  forall (l : side) (k1 : N),
    r0Cfg l (R k1) -->* carryCfg l (R (k1 + 2)%N).

Lemma hasRoundtrip_evalWK : HasRoundtrip evalWK.
Proof. intros l k1. apply r0_end. Qed.

Lemma hasRoundtrip_Z {R : N -> side} (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR Z *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_Z |].
  eapply evstep_trans; [apply (hR (tokL Z *> l) k1) |].
  apply carry_Z.
Qed.

Lemma hasRoundtrip_P {R : N -> side} (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR P *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_P |].
  eapply evstep_trans; [apply (hR (tokL P *> l) k1) |].
  apply carry_P.
Qed.

Lemma hasRoundtrip_word (w : list Tok) : forall {R : N -> side},
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => wordR w *> R k1).
Proof.
  induction w as [|t ts IH]; intros R Hw hR; cbn [isZpWord] in Hw.
  - exact hR.
  - destruct t; try discriminate; intros l k1; cbn [wordR]; rewrite Str_app_assoc.
    + exact (hasRoundtrip_Z (IH R Hw hR) l k1).
    + exact (hasRoundtrip_P (IH R Hw hR) l k1).
Qed.

Lemma hasRoundtrip_pow (c : N) (w : list Tok) : forall {R : N -> side},
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => npow (wordR w) c *> R k1).
Proof.
  induction c as [|c IH] using N.peano_ind; intros R Hw hR.
  - intros l k1. rewrite npow_0; cbn [Str_app]. exact (hR l k1).
  - intros l k1. rewrite !N_succ_eq_add_1, !npow_succ_l, !Str_app_assoc.
    exact (hasRoundtrip_word w Hw (IH R Hw hR) l k1).
Qed.

Lemma hasRoundtrip_stack (rs : Rle) : forall {R : N -> side},
  allZpStack rs = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => evalRStack rs (R k1)).
Proof.
  induction rs as [|[w c] rest IH]; intros R Hrs hR.
  - exact hR.
  - cbn [allZpStack] in Hrs. apply andb_prop in Hrs. destruct Hrs as [Hw Hrest].
    intros l k1. cbn [evalRStack].
    exact (hasRoundtrip_pow c w Hw (IH R Hrest hR) l k1).
Qed.

Definition r1PhaseCfg (phase : bool) (l r : side) : Q * tape :=
  if phase then r1OddCfg l r else r1Cfg l r.

Definition sr1_out (p : list Tok * N * bool) : list Tok := fst (fst p).
Definition sr1_res (p : list Tok * N * bool) : N := snd (fst p).
Definition sr1_phase (p : list Tok * N * bool) : bool := snd p.

Fixpoint stepR1StarWord (w : list Tok) (phase : bool) : list Tok * N * bool :=
  match w with
  | [] => ([], 0%N, phase)
  | t :: ts =>
    if phase then
      let sub := stepR1StarWord ts (negb (tok_eqb t P)) in
      (sr1_out sub ++ [Z], sr1_res sub, sr1_phase sub)
    else
      let sub := stepR1StarWord ts (negb (tok_eqb t Z)) in
      (sr1_out sub ++ [P], (sr1_res sub + (if tok_eqb t Z then 1 else 0))%N, sr1_phase sub)
  end.

Lemma stepR1StarWord_phase_inv (w : list Tok) : forall (phase : bool),
  isZpWord w = true ->
  sr1_phase (stepR1StarWord w (negb phase)) = negb (sr1_phase (stepR1StarWord w phase)).
Proof.
  induction w as [|t ts IH]; intros phase Hw; cbn [isZpWord] in Hw.
  - reflexivity.
  - destruct t; try discriminate; destruct phase; cbn [stepR1StarWord tok_eqb negb sr1_phase snd].
    + exact (IH true Hw).
    + exact (IH false Hw).
    + exact (IH false Hw).
    + exact (IH true Hw).
Qed.

Lemma stepR1StarWord_sound (w : list Tok) : forall (phase : bool) (l : side) {R : N -> side},
  isZpWord w = true -> HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (wordR w *> R k1) -->*
    r1PhaseCfg (sr1_phase (stepR1StarWord w phase))
      (wordL (sr1_out (stepR1StarWord w phase)) *> l)
      (R (k1 + 2 * sr1_res (stepR1StarWord w phase))%N).
Proof.
  induction w as [|t ts IH]; intros phase l R Hw hR k1; cbn [isZpWord] in Hw.
  - cbn [stepR1StarWord sr1_out sr1_res sr1_phase fst snd wordR wordL Str_app N.mul].
    replace (k1 + 0)%N with k1 by lia. apply evstep_refl.
  - destruct t; try discriminate; destruct phase;
      cbn [stepR1StarWord tok_eqb negb sr1_out sr1_res sr1_phase fst snd wordR r1PhaseCfg];
      rewrite Str_app_assoc, wordL_append, Str_app_assoc; cbn [wordL]; rewrite app_nil_r.
    + (* Z, true *)
      eapply evstep_trans; [apply r1Odd_Z |].
      exact (IH true (tokL Z *> l) R Hw hR k1).
    + (* Z, false *)
      pose proof (hasRoundtrip_word ts Hw hR) as hR'.
      eapply evstep_trans; [apply r1_Z |].
      eapply evstep_trans; [exact (hR' (tokL M *> (tokL Z *> l)) k1) |].
      eapply evstep_trans; [apply turn_ZM |].
      pose proof (IH false (tokL P *> l) R Hw hR (k1 + 2)%N) as Hsub.
      replace (k1 + 2 * (sr1_res (stepR1StarWord ts false) + 1))%N
        with (k1 + 2 + 2 * sr1_res (stepR1StarWord ts false))%N by lia.
      exact Hsub.
    + (* P, true *)
      eapply evstep_trans; [apply r1Odd_P |].
      exact (IH false (tokL Z *> l) R Hw hR k1).
    + (* P, false *)
      replace (sr1_res (stepR1StarWord ts true) + 0)%N
        with (sr1_res (stepR1StarWord ts true)) by lia.
      eapply evstep_trans; [apply r1_P |].
      exact (IH true (tokL P *> l) R Hw hR k1).
Qed.

Lemma stepR1Star_same_pow (c : N) (w : list Tok) (phase : bool) :
  forall (l : side) {R : N -> side},
  isZpWord w = true ->
  sr1_phase (stepR1StarWord w phase) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (npow (wordR w) c *> R k1) -->*
    r1PhaseCfg phase (npow (wordL (sr1_out (stepR1StarWord w phase))) c *> l)
      (R (k1 + 2 * (c * sr1_res (stepR1StarWord w phase)))%N).
Proof.
  induction c as [|c IH] using N.peano_ind; intros l R Hw Hsame hR k1.
  - cbn [N.mul]; rewrite !npow_0; cbn [Str_app].
    replace (k1 + 0)%N with k1 by lia. apply evstep_refl.
  - rewrite !N_succ_eq_add_1, npow_succ_l, Str_app_assoc.
    pose proof (hasRoundtrip_pow c w Hw hR) as hR'.
    pose proof (stepR1StarWord_sound w phase l Hw hR' k1) as H1.
    rewrite Hsame in H1.
    eapply evstep_trans; [exact H1 |].
    pose proof (IH (wordL (sr1_out (stepR1StarWord w phase)) *> l) R Hw Hsame hR
      (k1 + 2 * sr1_res (stepR1StarWord w phase))%N) as H2.
    replace (k1 + 2 * ((c + 1) * sr1_res (stepR1StarWord w phase)))%N
      with (k1 + 2 * sr1_res (stepR1StarWord w phase) +
            2 * (c * sr1_res (stepR1StarWord w phase)))%N by lia.
    rewrite npow_succ_r, Str_app_assoc.
    exact H2.
Qed.

Lemma stepR1Star_alt_pow (q : N) (w : list Tok) (phase : bool) :
  forall (l : side) {R : N -> side},
  isZpWord w = true ->
  sr1_phase (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    let s1 := stepR1StarWord w phase in
    let s2 := stepR1StarWord w (sr1_phase s1) in
    r1PhaseCfg phase l (npow (wordR w) (2 * q)%N *> R k1) -->*
    r1PhaseCfg phase (npow (wordL (sr1_out s2 ++ sr1_out s1)) q *> l)
      (R (k1 + 2 * (q * (sr1_res s1 + sr1_res s2)))%N).
Proof.
  induction q as [|q IH] using N.peano_ind; intros l R Hw Halt hR k1; cbv zeta.
  - cbn [N.mul]; rewrite !npow_0; cbn [Str_app].
    replace (k1 + 0)%N with k1 by lia. apply evstep_refl.
  - replace (2 * N.succ q)%N with (1 + (1 + 2 * q))%N by lia.
    rewrite !npow_add, !npow_1, !Str_app_assoc.
    pose proof (hasRoundtrip_pow (2 * q)%N w Hw hR) as hR2.
    pose proof (hasRoundtrip_word w Hw hR2) as hR1.
    eapply evstep_trans; [exact (stepR1StarWord_sound w phase l Hw hR1 k1) |].
    eapply evstep_trans;
      [exact (stepR1StarWord_sound w (sr1_phase (stepR1StarWord w phase))
                (wordL (sr1_out (stepR1StarWord w phase)) *> l) Hw hR2
                (k1 + 2 * sr1_res (stepR1StarWord w phase))%N) |].
    rewrite Halt.
    pose proof (IH (wordL (sr1_out (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))) ++
                           sr1_out (stepR1StarWord w phase)) *> l) R Hw Halt hR
      (k1 + 2 * sr1_res (stepR1StarWord w phase) +
       2 * sr1_res (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))))%N) as Hsub.
    cbv zeta in Hsub.
    rewrite !N_succ_eq_add_1, npow_succ_r, Str_app_assoc.
    rewrite <- Str_app_assoc, <- wordL_append.
    replace (k1 + 2 * ((q + 1) * (sr1_res (stepR1StarWord w phase) +
              sr1_res (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))))))%N
      with (k1 + 2 * sr1_res (stepR1StarWord w phase) +
            2 * sr1_res (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))) +
            2 * (q * (sr1_res (stepR1StarWord w phase) +
              sr1_res (stepR1StarWord w (sr1_phase (stepR1StarWord w phase))))))%N by lia.
    exact Hsub.
Qed.

Definition sw_rle (p : Rle * bool * N) : Rle := fst (fst p).
Definition sw_phase (p : Rle * bool * N) : bool := snd (fst p).
Definition sw_res (p : Rle * bool * N) : N := snd p.

Fixpoint sweepStarLoop (rle : Rle) (phase : bool) (totalRes : N) (rs : Rle) : Rle * bool * N :=
  match rs with
  | [] => (rle, phase, totalRes)
  | (item, count) :: rest =>
    let s1 := stepR1StarWord item phase in
    let out1 := sr1_out s1 in
    let res1 := sr1_res s1 in
    let nextPhase := sr1_phase s1 in
    if Bool.eqb nextPhase phase then
      sweepStarLoop (pushRle out1 count rle) phase (totalRes + count * res1)%N rest
    else
      let s2 := stepR1StarWord item nextPhase in
      let out2 := sr1_out s2 in
      let res2 := sr1_res s2 in
      let q := (count / 2)%N in
      let rem := (count mod 2)%N in
      let rle1 := pushRle (out2 ++ out1) q rle in
      let resAfterQ := (totalRes + q * (res1 + res2))%N in
      if (rem =? 1)%N then
        sweepStarLoop (pushRle out1 1%N rle1) nextPhase (resAfterQ + res1)%N rest
      else
        sweepStarLoop rle1 phase resAfterQ rest
  end.

Lemma sweepStarLoop_sound (rs : Rle) :
  forall (rle : Rle) (phase : bool) (totalRes : N) {R : N -> side},
  allZpStack rs = true -> HasRoundtrip R ->
  forall (k1 : N),
    let res := sweepStarLoop rle phase totalRes rs in
    r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)%N)) -->*
    r1PhaseCfg (sw_phase res) (evalRle (sw_rle res)) (R (k1 + 2 * sw_res res)%N).
Proof.
  induction rs as [|[item count] rest IH]; intros rle phase totalRes R Hrs hR k1; cbv zeta.
  - cbn [sweepStarLoop sw_rle sw_phase sw_res fst snd evalRStack]. apply evstep_refl.
  - cbn [allZpStack] in Hrs. apply andb_prop in Hrs. destruct Hrs as [Hitem Hrest].
    pose proof (hasRoundtrip_stack rest Hrest hR) as hR_rest.
    cbn [sweepStarLoop evalRStack]; cbv zeta.
    destruct (Bool.eqb_spec (sr1_phase (stepR1StarWord item phase)) phase) as [Hsame|Hdiff].
    + eapply evstep_trans;
        [exact (stepR1Star_same_pow count item phase (evalRle rle) Hitem Hsame hR_rest
                  (k1 + 2 * totalRes)%N) |].
      rewrite <- evalRle_pushRle.
      replace (k1 + 2 * totalRes + 2 * (count * sr1_res (stepR1StarWord item phase)))%N
        with (k1 + 2 * (totalRes + count * sr1_res (stepR1StarWord item phase)))%N by lia.
      exact (IH (pushRle (sr1_out (stepR1StarWord item phase)) count rle) phase
               (totalRes + count * sr1_res (stepR1StarWord item phase))%N R Hrest hR k1).
    + assert (Hnot : sr1_phase (stepR1StarWord item phase) = negb phase)
        by (destruct phase, (sr1_phase (stepR1StarWord item _)); congruence || reflexivity).
      assert (Halt : sr1_phase (stepR1StarWord item (sr1_phase (stepR1StarWord item phase))) = phase)
        by (rewrite Hnot, (stepR1StarWord_phase_inv item phase Hitem), Hnot, Bool.negb_involutive; reflexivity).
      remember (count / 2)%N as q eqn:Eq.
      remember (count mod 2)%N as rem eqn:Erem.
      assert (Hdiv : count = (2 * q + rem)%N) by lia.
      assert (Hrem : (rem = 0 \/ rem = 1)%N) by lia.
      clear Eq Erem.
      rewrite Hdiv, npow_add, Str_app_assoc.
      pose proof (hasRoundtrip_pow rem item Hitem hR_rest) as hR_rem.
      eapply evstep_trans;
        [exact (stepR1Star_alt_pow q item phase (evalRle rle) Hitem Halt hR_rem
                  (k1 + 2 * totalRes)%N) |].
      rewrite <- evalRle_pushRle.
      replace (k1 + 2 * totalRes +
               2 * (q * (sr1_res (stepR1StarWord item phase) +
                         sr1_res (stepR1StarWord item (sr1_phase (stepR1StarWord item phase))))))%N
        with (k1 + 2 * (totalRes +
               q * (sr1_res (stepR1StarWord item phase) +
                    sr1_res (stepR1StarWord item (sr1_phase (stepR1StarWord item phase))))))%N by lia.
      destruct (N.eqb_spec rem 1%N) as [->|Hne1].
      * rewrite npow_1.
        eapply evstep_trans;
          [apply (stepR1StarWord_sound item phase _ Hitem hR_rest) |].
        rewrite <- evalRle_pushRle_one.
        replace (k1 +
                 2 * (totalRes +
                      q * (sr1_res (stepR1StarWord item phase) +
                           sr1_res (stepR1StarWord item (sr1_phase (stepR1StarWord item phase))))) +
                 2 * sr1_res (stepR1StarWord item phase))%N
          with (k1 +
                2 * (totalRes +
                     q * (sr1_res (stepR1StarWord item phase) +
                          sr1_res (stepR1StarWord item (sr1_phase (stepR1StarWord item phase)))) +
                     sr1_res (stepR1StarWord item phase)))%N by lia.
        apply (IH _ _ _ R Hrest hR k1).
      * assert (rem = 0%N) as -> by lia.
        rewrite npow_0; cbn [Str_app].
        apply (IH _ phase _ R Hrest hR k1).
Qed.

(* ========================================================================== *)
(* Section 7: Turnaround, Special Loops, and Final Halting Theorem            *)
(* ========================================================================== *)

Definition modeCfg (m : Mode) (l r : side) : Q * tape :=
  match m with
  | R0 => r0Cfg l r
  | R1 => r1Cfg l r
  | R1_ODD => r1OddCfg l r
  end.

Definition stepOneTok (rle : Rle) (mode : Mode) (t : Tok) : option (Rle * Mode) :=
  match mode, t with
  | R0, PTTTM_TAIL => Some (pushRle [Z] 1%N rle, R1)
  | R0, Z => Some (pushRle [Z] 1%N rle, R0)
  | R0, P => Some (pushRle [P] 1%N rle, R0)
  | R1, Z => Some (pushToksLtr [Z; M] rle, R0)
  | R1, P => Some (pushRle [P] 1%N rle, R1_ODD)
  | R1_ODD, Z => Some (pushRle [Z] 1%N rle, R1_ODD)
  | R1_ODD, P => Some (pushRle [Z] 1%N rle, R1)
  | _, _ => None
  end.

Lemma stepOneTok_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : side) :
  stepOneTok rle mode t = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (tokR t *> r) -->*
  modeCfg mode' (evalRle rle') r.
Proof.
  destruct mode, t; cbn [stepOneTok]; intros H; try discriminate;
    inversion H; subst rle' mode'; clear H;
    cbn [modeCfg pushToksLtr]; rewrite !evalRle_pushRle_one; cbn [wordL]; rewrite !app_nil_r.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Fixpoint stepOneWord (rle : Rle) (mode : Mode) (w : list Tok) : option (Rle * Mode) :=
  match w with
  | [] => Some (rle, mode)
  | t :: ts =>
    match stepOneTok rle mode t with
    | Some (rle1, mode1) => stepOneWord rle1 mode1 ts
    | None => None
    end
  end.

Lemma stepOneWord_sound (w : list Tok) :
  forall (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneWord rle mode w = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (wordR w *> r) -->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction w as [|t ts IH]; intros rle rle' mode mode' r H; cbn [stepOneWord] in H.
  - inversion H; subst. cbn [wordR Str_app]. apply evstep_refl.
  - destruct (stepOneTok rle mode t) as [[rle1 mode1]|] eqn:Ht; [|discriminate].
    cbn [wordR]; rewrite Str_app_assoc.
    eapply evstep_trans; [exact (stepOneTok_sound rle rle1 mode mode1 t _ Ht) |].
    exact (IH rle1 rle' mode1 mode' r H).
Qed.

Lemma r1_PP_pow (q : N) : forall (l r : side),
  r1Cfg l (npow (wordR [P]) (2 * q)%N *> r) -->*
  r1Cfg (npow (wordL [Z; P]) q *> l) r.
Proof.
  induction q as [|q IH] using N.peano_ind; intros l r.
  - cbn [N.mul]; rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - replace (2 * N.succ q)%N with (1 + (1 + 2 * q))%N by lia.
    rewrite !npow_add, !npow_1; cbn [wordR]; rewrite !app_nil_r, !Str_app_assoc.
    eapply evstep_trans; [apply r1_P |].
    eapply evstep_trans; [apply r1Odd_P |].
    rewrite !N_succ_eq_add_1, npow_succ_r, Str_app_assoc.
    cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
    apply IH.
Qed.

Lemma r1Odd_PP_pow (q : N) : forall (l r : side),
  r1OddCfg l (npow (wordR [P]) (2 * q)%N *> r) -->*
  r1OddCfg (npow (wordL [P; Z]) q *> l) r.
Proof.
  induction q as [|q IH] using N.peano_ind; intros l r.
  - cbn [N.mul]; rewrite !npow_0; cbn [Str_app]. apply evstep_refl.
  - replace (2 * N.succ q)%N with (1 + (1 + 2 * q))%N by lia.
    rewrite !npow_add, !npow_1; cbn [wordR]; rewrite !app_nil_r, !Str_app_assoc.
    eapply evstep_trans; [apply r1Odd_P |].
    eapply evstep_trans; [apply r1_P |].
    rewrite !N_succ_eq_add_1, npow_succ_r, Str_app_assoc.
    cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
    apply IH.
Qed.

Fixpoint stepOneBounceFuel (fuel : nat) (item : list Tok) (count : N) (rle : Rle) (mode : Mode) : option (Rle * Mode) :=
  if (count =? 0)%N then Some (rle, mode)
  else match fuel with
  | O => None
  | S fuel' =>
    if mode_eqb mode R0 && isZpWord item then
      Some (pushRle (revWord item) count rle, R0)
    else if word_eqb item [P] && mode_eqb mode R1 && (2 <=? count)%N then
      let q := (count / 2)%N in
      let rem := (count mod 2)%N in
      stepOneBounceFuel fuel' [P] rem (pushRle [Z; P] q rle) R1
    else if word_eqb item [P] && mode_eqb mode R1_ODD && (2 <=? count)%N then
      let q := (count / 2)%N in
      let rem := (count mod 2)%N in
      stepOneBounceFuel fuel' [P] rem (pushRle [P; Z] q rle) R1_ODD
    else
      match stepOneWord rle mode item with
      | Some (rle1, mode1) => stepOneBounceFuel fuel' item (count - 1)%N rle1 mode1
      | None => None
      end
  end.

Lemma stepOneBounceFuel_sound (fuel : nat) :
  forall (item : list Tok) (count : N) (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneBounceFuel fuel item count rle mode = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (npow (wordR item) count *> r) -->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction fuel as [|fuel IH]; intros item count rle rle' mode mode' r H;
    cbn [stepOneBounceFuel] in H.
  - destruct (N.eqb_spec count 0%N) as [->|]; [|discriminate].
    inversion H; subst. rewrite npow_0; cbn [Str_app]. apply evstep_refl.
  - destruct (N.eqb_spec count 0%N) as [->|Hc0].
    + inversion H; subst. rewrite npow_0; cbn [Str_app]. apply evstep_refl.
    + destruct (mode_eqb mode R0 && isZpWord item) eqn:E1.
      * apply andb_prop in E1. destruct E1 as [Hm Hitem].
        destruct (mode_eqb_spec mode R0) as [->|]; [|discriminate].
        inversion H; subst. cbn [modeCfg]; rewrite evalRle_pushRle.
        exact (r0_pow count item (evalRle rle) r Hitem).
      * destruct (word_eqb item [P] && mode_eqb mode R1 && (2 <=? count)%N) eqn:E2.
        { apply andb_prop in E2. destruct E2 as [E2a Hle].
          apply andb_prop in E2a. destruct E2a as [Hit Hm].
          destruct (word_eqb_spec item [P]) as [->|]; [|discriminate].
          destruct (mode_eqb_spec mode R1) as [->|]; [|discriminate].
          cbv zeta in H.
          remember (count / 2)%N as q eqn:Eq.
          remember (count mod 2)%N as rem eqn:Erem.
          assert (Hdiv : count = (2 * q + rem)%N) by lia.
          clear Eq Erem.
          rewrite Hdiv, npow_add, Str_app_assoc; cbn [modeCfg].
          eapply evstep_trans; [apply r1_PP_pow |].
          rewrite <- evalRle_pushRle.
          exact (IH [P] rem (pushRle [Z; P] q rle) rle' R1 mode' r H). }
        { destruct (word_eqb item [P] && mode_eqb mode R1_ODD && (2 <=? count)%N) eqn:E3.
          - apply andb_prop in E3. destruct E3 as [E3a Hle].
            apply andb_prop in E3a. destruct E3a as [Hit Hm].
            destruct (word_eqb_spec item [P]) as [->|]; [|discriminate].
            destruct (mode_eqb_spec mode R1_ODD) as [->|]; [|discriminate].
            cbv zeta in H.
            remember (count / 2)%N as q eqn:Eq.
            remember (count mod 2)%N as rem eqn:Erem.
            assert (Hdiv : count = (2 * q + rem)%N) by lia.
            clear Eq Erem.
            rewrite Hdiv, npow_add, Str_app_assoc; cbn [modeCfg].
            eapply evstep_trans; [apply r1Odd_PP_pow |].
            rewrite <- evalRle_pushRle.
            exact (IH [P] rem (pushRle [P; Z] q rle) rle' R1_ODD mode' r H).
          - destruct (stepOneWord rle mode item) as [[rle1 mode1]|] eqn:Hw; [|discriminate].
            replace count with ((count - 1) + 1)%N at 1 by lia.
            rewrite npow_succ_l, Str_app_assoc.
            eapply evstep_trans; [exact (stepOneWord_sound item rle rle1 mode mode1 _ Hw) |].
            exact (IH item (count - 1)%N rle1 rle' mode1 mode' r H). }
Qed.

Fixpoint simpleOneBounceCarry (rle : Rle) (mode : Mode) (rs : Rle) (k1 : N) : option (Rle * N) :=
  match rs with
  | [] => if mode_eqb mode R0 then Some (rle, (k1 + 2)%N) else None
  | (item, count) :: rest =>
    match stepOneBounceFuel 3 item count rle mode with
    | Some (rle', mode') => simpleOneBounceCarry rle' mode' rest k1
    | None => None
    end
  end.

Lemma simpleOneBounceCarry_sound (rs : Rle) :
  forall (rle rle' : Rle) (mode : Mode) (k1 kOut : N),
  simpleOneBounceCarry rle mode rs k1 = Some (rle', kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1)) -->*
  carryCfg (evalRle rle') (evalWK kOut).
Proof.
  induction rs as [|[item count] rest IH]; intros rle rle' mode k1 kOut H;
    cbn [simpleOneBounceCarry] in H.
  - destruct (mode_eqb_spec mode R0) as [->|]; [|discriminate].
    inversion H; subst. cbn [modeCfg evalRStack]. apply r0_end.
  - destruct (stepOneBounceFuel 3 item count rle mode) as [[rle1 mode1]|] eqn:Hb; [|discriminate].
    cbn [evalRStack].
    eapply evstep_trans; [exact (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ Hb) |].
    exact (IH rle1 rle' mode1 k1 kOut H).
Qed.

Fixpoint hasSpecial (rs : Rle) : bool :=
  match rs with
  | [] => false
  | (it, _) :: rest => word_eqb it [PTTTM_TAIL] || hasSpecial rest
  end.

Definition runRightSweepStarCarry (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : option (Rle * N) :=
  if mode_eqb mode R0 then
    match copyRStack rle rStack with
    | Some rle' => Some (rle', (k1 + 2)%N)
    | None => None
    end
  else if hasSpecial rStack then
    simpleOneBounceCarry rle mode rStack k1
  else if allZpStack rStack then
    let initPhase := negb (mode_eqb mode R1) in
    let sw := sweepStarLoop rle initPhase 0%N rStack in
    let rle1 := sw_rle sw in
    let finalPhase := sw_phase sw in
    let totalRes := sw_res sw in
    let kFinal1 := (k1 + 2 * totalRes)%N in
    if negb finalPhase then
      Some (stepZtToCarry (pushRle [P] 1%N rle1) (kFinal1 + 1)%N)
    else
      Some (stepZtToCarry (pushRle [Z] 1%N rle1) kFinal1)
  else None.

Lemma runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : N) :
  runRightSweepStarCarry rle mode rStack k1 = Some (rOut, kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) -->*
  carryCfg (evalRle rOut) (evalWK kOut).
Proof.
  unfold runRightSweepStarCarry; cbv zeta.
  destruct (mode_eqb_spec mode R0) as [->|Hm0].
  - destruct (copyRStack rle rStack) as [rle'|] eqn:Hc; [|discriminate].
    intro H; injection H as <- <-. cbn [modeCfg].
    destruct (copyRStack_sound rStack rle rle' (evalWK k1) Hc) as [_ Hstep].
    eapply evstep_trans; [exact Hstep | apply r0_end].
  - destruct (hasSpecial rStack) eqn:Hspec.
    + exact (simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut).
    + destruct (allZpStack rStack) eqn:Hall; [|discriminate].
      intro H.
      assert (Hmode : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
                      r1PhaseCfg (negb (mode_eqb mode R1)) (evalRle rle)
                        (evalRStack rStack (evalWK (k1 + 2 * 0)%N))).
      { replace (k1 + 2 * 0)%N with k1 by lia.
        destruct mode; [congruence | reflexivity | reflexivity]. }
      rewrite Hmode.
      eapply evstep_trans;
        [exact (sweepStarLoop_sound rStack rle (negb (mode_eqb mode R1)) 0%N
                  Hall hasRoundtrip_evalWK k1) |].
      remember (sweepStarLoop rle (negb (mode_eqb mode R1)) 0%N rStack) as sw eqn:Esw.
      destruct (sw_phase sw) eqn:Ephase; cbn [negb] in H;
        injection H as H;
        pose proof (f_equal fst H) as H1;
        pose proof (f_equal snd H) as H2;
        cbn [fst snd] in H1, H2; subst rOut kOut.
      * cbn [r1PhaseCfg].
        eapply evstep_trans; [apply r1Odd_end |].
        pose proof (stepZtToCarry_sound (pushRle [Z] 1%N (sw_rle sw)) (k1 + 2 * sw_res sw)%N) as Hzt.
        rewrite evalRle_pushRle_one in Hzt; cbn [wordL] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
      * cbn [r1PhaseCfg].
        eapply evstep_trans; [apply r1_end |].
        pose proof (stepZtToCarry_sound (pushRle [P] 1%N (sw_rle sw)) (k1 + 2 * sw_res sw + 1)%N) as Hzt.
        rewrite evalRle_pushRle_one in Hzt; cbn [wordL] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
Qed.

Inductive StepCarryRes :=
  | SCR_halt
  | SCR_next (rle : Rle) (k1 : N)
  | SCR_err.

Lemma halts_of_evstep (c1 c2 : Q * tape) :
  c1 -->* c2 -> halts tm c2 -> halts tm c1.
Proof.
  intros Hstep Hhalt.
  destruct (with_counter Hstep) as [n Hmulti].
  exact (halts_multistep tm c1 c2 n Hhalt Hmulti).
Qed.

Definition StepCarryValid (cfg : Q * tape) (res : StepCarryRes) : Prop :=
  match res with
  | SCR_halt => halts tm cfg
  | SCR_next rOut kOut => cfg -->* carryCfg (evalRle rOut) (evalWK kOut)
  | SCR_err => False
  end.

Lemma stepCarryValid_of_evstep {cfg1 cfg2 : Q * tape} {res : StepCarryRes} :
  cfg1 -->* cfg2 -> StepCarryValid cfg2 res -> StepCarryValid cfg1 res.
Proof.
  intros Hstep Hval.
  destruct res as [|rOut kOut|]; cbn [StepCarryValid] in *.
  - exact (halts_of_evstep cfg1 cfg2 Hstep Hval).
  - eapply evstep_trans; [exact Hstep | exact Hval].
  - exact Hval.
Qed.

Definition finishTurn (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : StepCarryRes :=
  match runRightSweepStarCarry rle mode rStack k1 with
  | Some (rOut, kOut) => SCR_next rOut kOut
  | None => SCR_err
  end.

Lemma finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) :
  finishTurn rle mode rStack k1 <> SCR_err ->
  StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
    (finishTurn rle mode rStack k1).
Proof.
  unfold finishTurn.
  destruct (runRightSweepStarCarry rle mode rStack k1) as [[rOut kOut]|] eqn:Hr.
  - intros _. cbn [StepCarryValid].
    exact (runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut Hr).
  - intro Hne; exfalso; exact (Hne eq_refl).
Qed.

Definition stepTurnaround (r2 rStack : Rle) (k1 : N) : StepCarryRes :=
  if rle_eqb r2 [([M], 1%N); ([U], 1%N)] then
    finishTurn [([M], 1%N); ([U], 1%N)] R1 rStack k1
  else if rle_eqb r2 [([T], 1%N); ([M], 1%N); ([U], 1%N)] then
    finishTurn [([Z], 1%N); ([U], 1%N)] R1 rStack k1
  else match popToks [T; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; M] r') R1 rStack k1
  | None => match popToks [M; W] r2 with
  | Some r' => finishTurn (pushToksLtr [T] r') R1 rStack k1
  | None => match popToks [T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [T; P] r') R0 rStack k1
  | None => match popToks [M; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [P] r') R1 rStack k1
  | None => match popToks [W; T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [M; U; Z] r') R1_ODD rStack k1
  | None => match popToks [M; T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [T; Z] r') R1 rStack k1
  | None => match popToks [T; T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [M; U; Z] r') R1 rStack k1
  | None => match popToks [U; M; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; T] r') R1_ODD rStack k1
  | None => match popToks [M; T; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; M; P] r') R0 rStack k1
  | None => match popToks [T; T; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; W; P] r') R0 rStack k1
  | None => match popToks [W; T; U; M] r2 with
  | Some r' => finishTurn (pushToksLtr [T; Z] r') R1_ODD rStack k1
  | None => match popToks [M; T; T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [M; U; Z; P] r') R0 rStack k1
  | None => match popToks [W; T; T; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [P; Z; Z] r') R0 rStack k1
  | None => match popToks [M; T; T; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; W; Z] r') R1 rStack k1
  | None => match popToks [U; M; P; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [T; W; M; P] r') R0 rStack k1
  | None => match popToks [M; T; U; M; Z] r2 with
  | Some r' => finishTurn (pushToksLtr [P; Z; P] r') R0 rStack k1
  | None => match popToks [W; T; T; T; P] r2 with
  | Some r' => finishTurn (pushToksLtr [T; Z; Z; Z] r') R0 rStack k1
  | None => SCR_err
  end end end end end end end end end end end end end end end end end.

Lemma turnBranch_sound (pat out : list Tok) (mode : Mode) (r2 r' rStack : Rle) (k1 : N) :
  popToks pat r2 = Some r' ->
  carryCfg (wordL pat *> evalRle r') (evalRStack rStack (evalWK k1)) -->*
    modeCfg mode (evalRle (pushToksLtr out r')) (evalRStack rStack (evalWK k1)) ->
  finishTurn (pushToksLtr out r') mode rStack k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (finishTurn (pushToksLtr out r') mode rStack k1).
Proof.
  intros Hp Hturn Hne.
  rewrite (popToks_sound pat r2 r' Hp).
  exact (stepCarryValid_of_evstep Hturn (finishTurn_sound (pushToksLtr out r') mode rStack k1 Hne)).
Qed.

Ltac solve_turn_step thm :=
  cbn [wordL pushToksLtr modeCfg];
  rewrite !evalRle_pushRle_one;
  cbn [wordL];
  rewrite ?app_nil_r, ?Str_app_assoc;
  apply thm.

Ltac step_turn_case pat out mode thm :=
  lazymatch goal with
  | |- _ -> StepCarryValid (carryCfg (evalRle ?r2) _) _ =>
    let Hp := fresh "Hp" in
    destruct (popToks pat r2) as [r'|] eqn:Hp;
    [ intro; eapply (turnBranch_sound pat out mode r2 r' _ _ Hp);
      [ solve_turn_step thm | assumption ]
    | clear Hp ]
  end.

Lemma stepTurnaround_sound (r2 rStack : Rle) (k1 : N) :
  stepTurnaround r2 rStack k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (stepTurnaround r2 rStack k1).
Proof.
  unfold stepTurnaround.
  destruct (rle_eqb_spec r2 [([M], 1%N); ([U], 1%N)]) as [->|_].
  - intro Hne.
    eapply stepCarryValid_of_evstep; [| exact (finishTurn_sound _ R1 rStack k1 Hne)].
    cbn [evalRle modeCfg]; rewrite !npow_1; cbn [wordL]; rewrite !app_nil_r.
    apply turn_UM.
  - destruct (rle_eqb_spec r2 [([T], 1%N); ([M], 1%N); ([U], 1%N)]) as [->|_].
    + intro Hne.
      eapply stepCarryValid_of_evstep; [| exact (finishTurn_sound _ R1 rStack k1 Hne)].
      cbn [evalRle modeCfg]; rewrite !npow_1; cbn [wordL]; rewrite !app_nil_r.
      apply turn_UMT.
    + step_turn_case [T; Z] [T; M] R1 turn_ZT.
      step_turn_case [M; W] [T] R1 turn_WM.
      step_turn_case [T; P] [T; P] R0 turn_PT.
      step_turn_case [M; Z] [P] R1 turn_ZM.
      step_turn_case [W; T; P] [M; U; Z] R1_ODD turn_PTW.
      step_turn_case [M; T; P] [T; Z] R1 turn_PTM.
      step_turn_case [T; T; P] [M; U; Z] R1 turn_PTT.
      step_turn_case [U; M; Z] [T; T] R1_ODD turn_ZMU.
      step_turn_case [M; T; Z] [T; M; P] R0 turn_ZTM.
      step_turn_case [T; T; Z] [T; W; P] R0 turn_ZTT.
      step_turn_case [W; T; U; M] [T; Z] R1_ODD turn_MUTW.
      step_turn_case [M; T; T; P] [M; U; Z; P] R0 turn_PTTM.
      step_turn_case [W; T; T; Z] [P; Z; Z] R0 turn_ZTTW.
      step_turn_case [M; T; T; Z] [T; W; Z] R1 turn_ZTTM.
      step_turn_case [U; M; P; Z] [T; W; M; P] R0 turn_ZPMU.
      step_turn_case [M; T; U; M; Z] [P; Z; P] R0 turn_ZMUTM.
      step_turn_case [W; T; T; T; P] [T; Z; Z; Z] R0 turn_PTTTW.
      intro Hne; exfalso; exact (Hne eq_refl).
Qed.

Lemma wordL_Z_pow (n : N) : npow (wordL [Z]) n = npow (tokL Z) n.
Proof. cbn [wordL]; rewrite app_nil_r. reflexivity. Qed.

Lemma wordL_P_pow (n : N) : npow (wordL [P]) n = npow (tokL P) n.
Proof. cbn [wordL]; rewrite app_nil_r. reflexivity. Qed.

Lemma special_ZTM_loop (n : N) : forall (l : side) {R : N -> side},
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL M *> (tokL T *> (npow (tokL Z) (n + 1)%N *> l))) (R k1) -->*
  r0Cfg (npow (tokL P) (n + 1)%N *> (tokL M *> (tokL T *> l))) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n IH] using N.peano_ind; intros l R hR k1.
  - cbn [N.add N.mul]; rewrite !npow_1.
    replace (k1 + 0)%N with k1 by lia.
    apply turn_ZTM.
  - rewrite !N_succ_eq_add_1.
    rewrite (npow_succ_l (tokL Z) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTM |].
    eapply evstep_trans;
      [exact (hR (tokL P *> (tokL M *> (tokL T *> (npow (tokL Z) (n + 1)%N *> l)))) k1) |].
    eapply evstep_trans; [apply carry_P |].
    eapply evstep_trans; [exact (IH l _ (hasRoundtrip_P hR) (k1 + 2)%N) |].
    eapply evstep_trans; [apply r0_P |].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite (npow_succ_l (tokL P) (n + 1)%N), Str_app_assoc.
    apply evstep_refl.
Qed.

Lemma special_PT_loop (n : N) : forall (l : side) {R : N -> side},
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL T *> (npow (tokL P) (n + 1)%N *> l)) (R k1) -->*
  r0Cfg (npow (tokL P) (n + 1)%N *> (tokL T *> l)) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n IH] using N.peano_ind; intros l R hR k1.
  - cbn [N.add N.mul]; rewrite !npow_1.
    replace (k1 + 0)%N with k1 by lia.
    apply turn_PT.
  - rewrite !N_succ_eq_add_1.
    rewrite (npow_succ_l (tokL P) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_PT |].
    eapply evstep_trans;
      [exact (hR (tokL P *> (tokL T *> (npow (tokL P) (n + 1)%N *> l))) k1) |].
    eapply evstep_trans; [apply carry_P |].
    eapply evstep_trans; [exact (IH l _ (hasRoundtrip_P hR) (k1 + 2)%N) |].
    eapply evstep_trans; [apply r0_P |].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    apply evstep_refl.
Qed.

Lemma special_ZTW_loop (n : N) : forall (l : side) {R : N -> side},
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL W *> (tokL T *> (npow (tokL Z) (n + 1)%N *> l))) (R k1) -->*
  r0Cfg (npow (tokL Z) (n + 1)%N *> (tokL W *> (tokL T *> l))) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n IH] using N.peano_ind; intros l R hR k1.
  - cbn [N.add N.mul]; rewrite !npow_1.
    replace (k1 + 0)%N with k1 by lia.
    apply turn_ZTW.
  - rewrite !N_succ_eq_add_1.
    rewrite (npow_succ_l (tokL Z) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTW |].
    eapply evstep_trans;
      [exact (hR (tokL Z *> (tokL W *> (tokL T *> (npow (tokL Z) (n + 1)%N *> l)))) k1) |].
    eapply evstep_trans; [apply carry_Z |].
    eapply evstep_trans; [exact (IH l _ (hasRoundtrip_Z hR) (k1 + 2)%N) |].
    eapply evstep_trans; [apply r0_Z |].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    apply evstep_refl.
Qed.

Definition stepSpecialLoops (r2 rStack : Rle) (k1 : N) : option StepCarryRes :=
  match popPrefixCount [M; T] [Z] r2 with
  | Some (b, r3) =>
    match copyRStack (pushRle [P] b (pushToksLtr [T; M] r3)) rStack with
    | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
    | None => Some SCR_err
    end
  | None => match popPrefixCount [T] [P] r2 with
  | Some (b, r3) =>
    match copyRStack (pushRle [P] b (pushRle [T] 1%N r3)) rStack with
    | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
    | None => Some SCR_err
    end
  | None => match popPrefixCount [W; T] [Z] r2 with
  | Some (b, r3) =>
    match copyRStack (pushRle [Z] b (pushToksLtr [T; W] r3)) rStack with
    | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
    | None => Some SCR_err
    end
  | None => match popPrefixCount [U; M] [P] r2 with
  | Some (mVal, r3) =>
    match popTok Z r3 with
    | Some r4 =>
      let r5 := pushRle [P] 1%N (pushRle [Z] (mVal - 1)%N (pushToksLtr [T; W; M] r4)) in
      Some (finishTurn r5 R0 rStack k1)
    | None =>
      match popToks [M; T] r3 with
      | Some _ => Some SCR_halt
      | None => Some SCR_err
      end
    end
  | None => None
  end end end end.

Lemma stepSpecialLoops_sound (r2 rStack : Rle) (k1 : N) (res : StepCarryRes) :
  stepSpecialLoops r2 rStack k1 = Some res ->
  res <> SCR_err ->
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res.
Proof.
  unfold stepSpecialLoops.
  destruct (popPrefixCount [M; T] [Z] r2) as [[b r3]|] eqn:Hp1.
  - destruct (popPrefixCount_sound [M; T] [Z] r2 r3 b Hp1) as [Hb Hr2].
    destruct (copyRStack (pushRle [P] b (pushToksLtr [T; M] r3)) rStack) as [r4|] eqn:Hc1.
    + intros H Hne; injection H as <-; unfold StepCarryValid.
      destruct (copyRStack_sound rStack (pushRle [P] b (pushToksLtr [T; M] r3)) r4
                  (evalWK (k1 + 2 * (b - 1))%N) Hc1) as [Hrs Hcopy].
      pose proof (hasRoundtrip_stack rStack Hrs hasRoundtrip_evalWK) as hR.
      assert (Hb1 : b = (b - 1 + 1)%N) by lia.
      rewrite Hr2, wordL_Z_pow, Hb1; cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
      eapply evstep_trans; [exact (special_ZTM_loop (b - 1)%N (evalRle r3) hR k1) |].
      rewrite <- Hb1.
      cbn [pushToksLtr] in Hcopy; rewrite !evalRle_pushRle, !npow_1, wordL_P_pow in Hcopy;
        cbn [wordL] in Hcopy; rewrite !app_nil_r in Hcopy.
      eapply evstep_trans; [exact Hcopy |].
      eapply evstep_trans; [apply r0_end |].
      replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N by lia.
      apply evstep_refl.
    + intros H Hne; injection H as <-; exfalso; exact (Hne eq_refl).
  - destruct (popPrefixCount [T] [P] r2) as [[b r3]|] eqn:Hp2.
    + destruct (popPrefixCount_sound [T] [P] r2 r3 b Hp2) as [Hb Hr2].
      destruct (copyRStack (pushRle [P] b (pushRle [T] 1%N r3)) rStack) as [r4|] eqn:Hc2.
      * intros H Hne; injection H as <-; unfold StepCarryValid.
        destruct (copyRStack_sound rStack (pushRle [P] b (pushRle [T] 1%N r3)) r4
                    (evalWK (k1 + 2 * (b - 1))%N) Hc2) as [Hrs Hcopy].
        pose proof (hasRoundtrip_stack rStack Hrs hasRoundtrip_evalWK) as hR.
        assert (Hb1 : b = (b - 1 + 1)%N) by lia.
        rewrite Hr2, wordL_P_pow, Hb1; cbn [wordL]; rewrite app_nil_r.
        eapply evstep_trans; [exact (special_PT_loop (b - 1)%N (evalRle r3) hR k1) |].
        rewrite <- Hb1.
        rewrite !evalRle_pushRle, !npow_1, wordL_P_pow in Hcopy;
          cbn [wordL] in Hcopy; rewrite !app_nil_r in Hcopy.
        eapply evstep_trans; [exact Hcopy |].
        eapply evstep_trans; [apply r0_end |].
        replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N by lia.
        apply evstep_refl.
      * intros H Hne; injection H as <-; exfalso; exact (Hne eq_refl).
    + destruct (popPrefixCount [W; T] [Z] r2) as [[b r3]|] eqn:Hp3.
      * destruct (popPrefixCount_sound [W; T] [Z] r2 r3 b Hp3) as [Hb Hr2].
        destruct (copyRStack (pushRle [Z] b (pushToksLtr [T; W] r3)) rStack) as [r4|] eqn:Hc3.
        { intros H Hne; injection H as <-; unfold StepCarryValid.
          destruct (copyRStack_sound rStack (pushRle [Z] b (pushToksLtr [T; W] r3)) r4
                      (evalWK (k1 + 2 * (b - 1))%N) Hc3) as [Hrs Hcopy].
          pose proof (hasRoundtrip_stack rStack Hrs hasRoundtrip_evalWK) as hR.
          assert (Hb1 : b = (b - 1 + 1)%N) by lia.
          rewrite Hr2, wordL_Z_pow, Hb1; cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
          eapply evstep_trans; [exact (special_ZTW_loop (b - 1)%N (evalRle r3) hR k1) |].
          rewrite <- Hb1.
          cbn [pushToksLtr] in Hcopy; rewrite !evalRle_pushRle, !npow_1, wordL_Z_pow in Hcopy;
            cbn [wordL] in Hcopy; rewrite !app_nil_r in Hcopy.
          eapply evstep_trans; [exact Hcopy |].
          eapply evstep_trans; [apply r0_end |].
          replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N by lia.
          apply evstep_refl. }
        { intros H Hne; injection H as <-; exfalso; exact (Hne eq_refl). }
      * destruct (popPrefixCount [U; M] [P] r2) as [[mVal r3]|] eqn:Hp4; [|discriminate].
        destruct (popPrefixCount_sound [U; M] [P] r2 r3 mVal Hp4) as [Hm Hr2].
        rewrite Hr2, wordL_P_pow; cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
        destruct (popTok Z r3) as [r4|] eqn:Hz.
        { cbv zeta; intros H Hne; injection H as <-.
          eapply stepCarryValid_of_evstep; [apply carry_MU_to_pmuCfg |].
          eapply stepCarryValid_of_evstep; [apply pmu_loop |].
          rewrite (popTok_sound Z r3 r4 Hz).
          replace (npow (tokR Z) mVal) with (npow (tokR Z) (1 + (mVal - 1))%N) by (f_equal; lia).
          rewrite npow_add, npow_1, Str_app_assoc.
          eapply stepCarryValid_of_evstep; [apply pmuCfg_Z_turn |].
          eapply stepCarryValid_of_evstep; [apply r0_Z_loop |].
          eapply stepCarryValid_of_evstep; [apply r0_P |].
          assert (Hr5 : tokL P *> (npow (tokL Z) (mVal - 1)%N *> (tokL M *> (tokL W *> (tokL T *> evalRle r4)))) =
                        evalRle (pushRle [P] 1%N (pushRle [Z] (mVal - 1)%N (pushToksLtr [T; W; M] r4)))).
          { cbn [pushToksLtr]; rewrite !evalRle_pushRle, !npow_1;
              cbn [wordL]; rewrite !app_nil_r. reflexivity. }
          rewrite Hr5.
          exact (finishTurn_sound _ R0 rStack k1 Hne). }
        { destruct (popToks [M; T] r3) as [r4|] eqn:Hmt.
          - intros H Hne; injection H as <-.
            eapply stepCarryValid_of_evstep; [apply carry_MU_to_pmuCfg |].
            eapply stepCarryValid_of_evstep; [apply pmu_loop |].
            rewrite (popToks_sound [M; T] r3 r4 Hmt); cbn [wordL]; rewrite app_nil_r, Str_app_assoc.
            eapply stepCarryValid_of_evstep; [apply pmuCfg_TM_halt |].
            cbn [StepCarryValid]. apply halted_halts. reflexivity.
          - intros H Hne; injection H as <-; exfalso; exact (Hne eq_refl). }
Qed.

Definition stepCarryAux (fuel : nat) (rle : Rle) (k1 : N) : StepCarryRes :=
  let (r2, rStack) := popCarryLoop fuel rle [] in
  if negb (hasSpecial rStack) then
    match stepSpecialLoops r2 rStack k1 with
    | Some res => res
    | None => stepTurnaround r2 rStack k1
    end
  else
    stepTurnaround r2 rStack k1.

Lemma stepCarryAux_sound (fuel : nat) (rle : Rle) (k1 : N) :
  stepCarryAux fuel rle k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarryAux fuel rle k1).
Proof.
  pose proof (popCarryLoop_sound fuel rle [] (evalWK k1)) as Hp.
  unfold stepCarryAux.
  destruct (popCarryLoop fuel rle []) as [r2 rStack].
  cbn [fst snd evalRStack] in Hp.
  intro Hne.
  eapply stepCarryValid_of_evstep; [exact Hp |].
  destruct (negb (hasSpecial rStack)) eqn:Hns.
  - destruct (stepSpecialLoops r2 rStack k1) as [res|] eqn:Hsl.
    + exact (stepSpecialLoops_sound r2 rStack k1 res Hsl Hne).
    + exact (stepTurnaround_sound r2 rStack k1 Hne).
  - exact (stepTurnaround_sound r2 rStack k1 Hne).
Qed.

Fixpoint runCarryAux (fuel : nat) (n : nat) (rle : Rle) (k1 : N) : bool :=
  match n with
  | O => false
  | S n' =>
    match stepCarryAux fuel rle k1 with
    | SCR_halt => true
    | SCR_next rle' k1' => runCarryAux fuel n' rle' k1'
    | SCR_err => false
    end
  end.

Lemma runCarryAux_sound (fuel : nat) (n : nat) : forall (rle : Rle) (k1 : N),
  runCarryAux fuel n rle k1 = true ->
  halts tm (carryCfg (evalRle rle) (evalWK k1)).
Proof.
  induction n as [|n IH]; intros rle k1 H; cbn [runCarryAux] in H.
  - discriminate.
  - destruct (stepCarryAux fuel rle k1) as [|rle' k1'|] eqn:Hs; [| |discriminate].
    + assert (Hne : stepCarryAux fuel rle k1 <> SCR_err) by (rewrite Hs; discriminate).
      pose proof (stepCarryAux_sound fuel rle k1 Hne) as Hval.
      rewrite Hs in Hval; exact Hval.
    + assert (Hne : stepCarryAux fuel rle k1 <> SCR_err) by (rewrite Hs; discriminate).
      pose proof (stepCarryAux_sound fuel rle k1 Hne) as Hval.
      rewrite Hs in Hval; cbn [StepCarryValid] in Hval.
      exact (halts_of_evstep _ _ Hval (IH rle' k1' H)).
Qed.

Definition initRle : Rle := pushToksLtr [U; M] [].

Lemma init_to_initRle :
  c0 -->* carryCfg (evalRle initRle) (evalWK 1%N).
Proof.
  cbn [initRle pushToksLtr]; rewrite !evalRle_pushRle_one; cbn [evalRle wordL]; rewrite !app_nil_r.
  exact init_to_carry0.
Qed.

Lemma runCarry_2605 : runCarryAux (N.to_nat 80%N) (N.to_nat 2605%N) initRle 1%N = true.
Proof. vm_compute. reflexivity. Qed.

Lemma halt : halts tm c0.
Proof.
  exact (halts_of_evstep _ _ init_to_initRle
    (runCarryAux_sound (N.to_nat 80%N) (N.to_nat 2605%N) initRle 1%N runCarry_2605)).
Qed.

Print Assumptions halt.
