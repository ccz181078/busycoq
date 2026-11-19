(* Classification: chaotic bell class 4.
   Consolidated from busycoq PR #19, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.List Lists.Streams PeanoNat Lia NArith ZArith String.

Module TM1.
Import BusyCoq.Individual62.

Import Bool List Streams PeanoNat Lia NArith ZArith String.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC").

Open Scope list_scope.

Lemma N_peano_ind (P : N -> Prop)
  (H0 : P 0%N) (HS : forall n : N, P n -> P (n + 1)%N) :
  forall n : N, P n.
Proof.
  intro n. induction n using N.peano_ind.
  - exact H0.
  - rewrite <- N.add_1_r. exact (HS n IHn).
Qed.

Definition npow (xs : list Sym) (n : N) : list Sym :=
  xs ^^ (N.to_nat n).

Lemma npow_0 (xs : list Sym) : npow xs 0%N = [].
Proof. reflexivity. Qed.

Lemma npow_1 (xs : list Sym) : npow xs 1%N = xs.
Proof. unfold npow; cbn; apply app_nil_r. Qed.

Lemma npow_add (xs : list Sym) (a b : N) :
  npow xs (a + b)%N = npow xs a ++ npow xs b.
Proof.
  unfold npow. rewrite N2Nat.inj_add. apply lpow_add.
Qed.

Lemma npow_2 (xs : list Sym) : npow xs 2%N = xs ++ xs.
Proof. change 2%N with (1 + 1)%N; rewrite npow_add, !npow_1; reflexivity. Qed.

Lemma npow_3 (xs : list Sym) : npow xs 3%N = xs ++ xs ++ xs.
Proof. change 3%N with (1 + (1 + 1))%N; rewrite !npow_add, !npow_1; reflexivity. Qed.

Lemma npow_succ_l (xs : list Sym) (n : N) :
  npow xs (n + 1)%N = xs ++ npow xs n.
Proof.
  replace (n + 1)%N with (1 + n)%N by lia.
  rewrite npow_add, npow_1. reflexivity.
Qed.

Lemma npow_succ_r (xs : list Sym) (n : N) :
  npow xs (n + 1)%N = npow xs n ++ xs.
Proof.
  rewrite npow_add, npow_1. reflexivity.
Qed.

Lemma zero_cons_0inf : (0 >> 0inf)%sym = 0inf.
Proof. rewrite <- const_unfold. reflexivity. Qed.

Record CCfg := mkCCfg {
  cc_q : Q;
  cc_cur : Sym;
  cc_l : list Sym;
  cc_r : list Sym
}.

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with
  | 0, 0 => true | 1, 1 => true | _, _ => false
  end%sym.

Lemma sym_eqb_eq (a b : Sym) : sym_eqb a b = true <-> a = b.
Proof. destruct a, b; cbn; intuition congruence. Qed.

Definition is_nil_sym (xs : list Sym) : bool :=
  match xs with [] => true | _ => false end.

Definition evalWindow (l_tail r_tail : side) (c : CCfg) : Q * tape :=
  (cc_q c, (cc_l c *> l_tail, cc_cur c, cc_r c *> r_tail)).

Definition evalCCfg (r_tail : side) (c : CCfg) : Q * tape :=
  evalWindow 0inf r_tail c.

Definition evalRCCfg (l_tail : side) (c : CCfg) : Q * tape :=
  evalWindow l_tail 0inf c.

Definition evalBCfg (c : CCfg) : Q * tape :=
  evalWindow 0inf 0inf c.

Definition wstep (M : TM) (c : CCfg) : option CCfg :=
  match M (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    match cc_l c with
    | [] => None
    | b :: ls => Some (mkCCfg q' b ls (w :: cc_r c))
    end
  | Some (w, R, q') =>
    match cc_r c with
    | [] => None
    | b :: rs => Some (mkCCfg q' b (w :: cc_l c) rs)
    end
  end.

Lemma wstep_sound (M : TM) (c c' : CCfg) (l_tail r_tail : side)
  (h : wstep M c = Some c') :
  evalWindow l_tail r_tail c -[ M ]-> evalWindow l_tail r_tail c'.
Proof.
  destruct c as [q cur l r]; unfold wstep in h; cbn [cc_q cc_cur cc_l cc_r] in h.
  destruct (M (q, cur)) as [[[w d] q']|] eqn:Htr; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; [discriminate|].
    inverts h. unfold evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
    exact (step_left Htr).
  - destruct r as [|b rs]; [discriminate|].
    inverts h. unfold evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
    exact (step_right Htr).
Qed.

Fixpoint wmultiStep (M : TM) (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match wstep M c with
    | Some c1 => wmultiStep M n' c1
    | None => None
    end
  end.

Lemma wmultiStep_sound (M : TM) (n : nat) : forall (c c' : CCfg) (l_tail r_tail : side),
  wmultiStep M n c = Some c' ->
  evalWindow l_tail r_tail c -[ M ]->* evalWindow l_tail r_tail c'.
Proof.
  induction n as [|n ih]; intros c c' l_tail r_tail h.
  - cbn in h; inverts h; apply evstep_refl.
  - cbn [wmultiStep] in h.
    destruct (wstep M c) as [c1|] eqn:Hs; [|discriminate].
    exact (evstep_step _ _ _ _ (wstep_sound M c c1 l_tail r_tail Hs) (ih c1 c' l_tail r_tail h)).
Qed.

Definition cstep (M : TM) (c : CCfg) : option CCfg :=
  match M (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    match cc_l c with
    | [] => Some (mkCCfg q' 0%sym [] (w :: cc_r c))
    | b :: ls => Some (mkCCfg q' b ls (w :: cc_r c))
    end
  | Some (w, R, q') =>
    match cc_r c with
    | [] => None
    | b :: rs =>
      let l' := if is_nil_sym (cc_l c) && sym_eqb w 0%sym then [] else w :: cc_l c in
      Some (mkCCfg q' b l' rs)
    end
  end.

Lemma cstep_sound (M : TM) (c c' : CCfg) (r_tail : side)
  (h : cstep M c = Some c') :
  evalCCfg r_tail c -[ M ]-> evalCCfg r_tail c'.
Proof.
  destruct c as [q cur l r]; unfold cstep in h; cbn [cc_q cc_cur cc_l cc_r] in h.
  destruct (M (q, cur)) as [[[w d] q']|] eqn:Htr; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; inverts h; unfold evalCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
    + pose proof (step_left Htr (l := 0inf) (r := r *> r_tail)) as Hstep.
      cbn [move_left hd tl] in Hstep. exact Hstep.
    + exact (step_left Htr).
  - destruct r as [|b rs]; [discriminate|].
    destruct l as [|b' ls']; cbn [is_nil_sym andb] in h.
    + destruct (sym_eqb w 0%sym) eqn:Hw; inverts h;
      unfold evalCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_right Htr (l := 0inf) (r := b >> (rs *> r_tail))) as Hstep.
        cbn [move_right hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * exact (step_right Htr).
    + inverts h; unfold evalCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      exact (step_right Htr).
Qed.

Fixpoint cmultiStep (M : TM) (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match cstep M c with
    | Some c1 => cmultiStep M n' c1
    | None => None
    end
  end.

Lemma cmultiStep_sound (M : TM) (n : nat) : forall (c c' : CCfg) (r_tail : side),
  cmultiStep M n c = Some c' ->
  evalCCfg r_tail c -[ M ]->* evalCCfg r_tail c'.
Proof.
  induction n as [|n ih]; intros c c' r_tail h.
  - cbn in h; inverts h; apply evstep_refl.
  - cbn [cmultiStep] in h.
    destruct (cstep M c) as [c1|] eqn:Hs; [|discriminate].
    exact (evstep_step _ _ _ _ (cstep_sound M c c1 r_tail Hs) (ih c1 c' r_tail h)).
Qed.

Definition rcstep (M : TM) (c : CCfg) : option CCfg :=
  match M (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    match cc_l c with
    | [] => None
    | b :: ls =>
      let r' := if is_nil_sym (cc_r c) && sym_eqb w 0%sym then [] else w :: cc_r c in
      Some (mkCCfg q' b ls r')
    end
  | Some (w, R, q') =>
    match cc_r c with
    | [] => Some (mkCCfg q' 0%sym (w :: cc_l c) [])
    | b :: rs => Some (mkCCfg q' b (w :: cc_l c) rs)
    end
  end.

Lemma rcstep_sound (M : TM) (c c' : CCfg) (l_tail : side)
  (h : rcstep M c = Some c') :
  evalRCCfg l_tail c -[ M ]-> evalRCCfg l_tail c'.
Proof.
  destruct c as [q cur l r]; unfold rcstep in h; cbn [cc_q cc_cur cc_l cc_r] in h.
  destruct (M (q, cur)) as [[[w d] q']|] eqn:Htr; [|discriminate].
  destruct d.
  - destruct l as [|b ls]; [discriminate|].
    destruct r as [|b' rs']; cbn [is_nil_sym andb] in h.
    + destruct (sym_eqb w 0%sym) eqn:Hw; inverts h;
      unfold evalRCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_left Htr (l := b >> (ls *> l_tail)) (r := 0inf)) as Hstep.
        cbn [move_left hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * exact (step_left Htr).
    + inverts h; unfold evalRCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      exact (step_left Htr).
  - destruct r as [|b rs]; inverts h; unfold evalRCCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
    + pose proof (step_right Htr (l := l *> l_tail) (r := 0inf)) as Hstep.
      cbn [move_right hd tl] in Hstep. exact Hstep.
    + exact (step_right Htr).
Qed.

Fixpoint rcmultiStep (M : TM) (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match rcstep M c with
    | Some c1 => rcmultiStep M n' c1
    | None => None
    end
  end.

Lemma rcmultiStep_sound (M : TM) (n : nat) : forall (c c' : CCfg) (l_tail : side),
  rcmultiStep M n c = Some c' ->
  evalRCCfg l_tail c -[ M ]->* evalRCCfg l_tail c'.
Proof.
  induction n as [|n ih]; intros c c' l_tail h.
  - cbn in h; inverts h; apply evstep_refl.
  - cbn [rcmultiStep] in h.
    destruct (rcstep M c) as [c1|] eqn:Hs; [|discriminate].
    exact (evstep_step _ _ _ _ (rcstep_sound M c c1 l_tail Hs) (ih c1 c' l_tail h)).
Qed.

Definition bstep (M : TM) (c : CCfg) : option CCfg :=
  match M (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    let r' := if is_nil_sym (cc_r c) && sym_eqb w 0%sym then [] else w :: cc_r c in
    match cc_l c with
    | [] => Some (mkCCfg q' 0%sym [] r')
    | b :: ls => Some (mkCCfg q' b ls r')
    end
  | Some (w, R, q') =>
    let l' := if is_nil_sym (cc_l c) && sym_eqb w 0%sym then [] else w :: cc_l c in
    match cc_r c with
    | [] => Some (mkCCfg q' 0%sym l' [])
    | b :: rs => Some (mkCCfg q' b l' rs)
    end
  end.

Lemma bstep_sound (M : TM) (c c' : CCfg)
  (h : bstep M c = Some c') :
  evalBCfg c -[ M ]-> evalBCfg c'.
Proof.
  destruct c as [q cur l r]; unfold bstep in h; cbn [cc_q cc_cur cc_l cc_r] in h.
  destruct (M (q, cur)) as [[[w d] q']|] eqn:Htr; [|discriminate].
  destruct d.
  - destruct r as [|b' rs']; cbn [is_nil_sym andb] in h.
    + destruct (sym_eqb w 0%sym) eqn:Hw; destruct l as [|b ls]; inverts h;
      unfold evalBCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_left Htr (l := 0inf) (r := 0inf)) as Hstep.
        cbn [move_left hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_left Htr (l := b >> (ls *> 0inf)) (r := 0inf)) as Hstep.
        cbn [move_left hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * pose proof (step_left Htr (l := 0inf) (r := 0inf)) as Hstep.
        cbn [move_left hd tl] in Hstep. exact Hstep.
      * exact (step_left Htr).
    + destruct l as [|b ls]; inverts h;
      unfold evalBCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * pose proof (step_left Htr (l := 0inf) (r := b' >> (rs' *> 0inf))) as Hstep.
        cbn [move_left hd tl] in Hstep. exact Hstep.
      * exact (step_left Htr).
  - destruct l as [|b' ls']; cbn [is_nil_sym andb] in h.
    + destruct (sym_eqb w 0%sym) eqn:Hw; destruct r as [|b rs]; inverts h;
      unfold evalBCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_right Htr (l := 0inf) (r := 0inf)) as Hstep.
        cbn [move_right hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * apply sym_eqb_eq in Hw; subst w.
        pose proof (step_right Htr (l := 0inf) (r := b >> (rs *> 0inf))) as Hstep.
        cbn [move_right hd tl] in Hstep. rewrite <- const_unfold in Hstep. exact Hstep.
      * pose proof (step_right Htr (l := 0inf) (r := 0inf)) as Hstep.
        cbn [move_right hd tl] in Hstep. exact Hstep.
      * exact (step_right Htr).
    + destruct r as [|b rs]; inverts h;
      unfold evalBCfg, evalWindow; cbn [cc_q cc_cur cc_l cc_r Str_app].
      * pose proof (step_right Htr (l := b' >> (ls' *> 0inf)) (r := 0inf)) as Hstep.
        cbn [move_right hd tl] in Hstep. exact Hstep.
      * exact (step_right Htr).
Qed.

Fixpoint bmultiStep (M : TM) (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | O => Some c
  | S n' =>
    match bstep M c with
    | Some c1 => bmultiStep M n' c1
    | None => None
    end
  end.

Lemma bmultiStep_sound (M : TM) (n : nat) : forall (c c' : CCfg),
  bmultiStep M n c = Some c' ->
  evalBCfg c -[ M ]->* evalBCfg c'.
Proof.
  induction n as [|n ih]; intros c c' h.
  - cbn in h; inverts h; apply evstep_refl.
  - cbn [bmultiStep] in h.
    destruct (bstep M c) as [c1|] eqn:Hs; [|discriminate].
    exact (evstep_step _ _ _ _ (bstep_sound M c c1 Hs) (ih c1 c' h)).
Qed.

Inductive Tok :=
| U_tok | M_tok | W_tok | Z_tok | T_tok | P_tok | PTTTM_TAIL_tok.

Inductive Mode :=
| R0_mode | R1_mode | R1_ODD_mode.

Definition Rle := list (list Tok * N).

Definition tokEq (a b : Tok) : bool :=
  match a, b with
  | U_tok, U_tok => true
  | M_tok, M_tok => true
  | W_tok, W_tok => true
  | Z_tok, Z_tok => true
  | T_tok, T_tok => true
  | P_tok, P_tok => true
  | PTTTM_TAIL_tok, PTTTM_TAIL_tok => true
  | _, _ => false
  end.

Lemma tokEq_eq (a b : Tok) : tokEq a b = true <-> a = b.
Proof. destruct a, b; cbn; intuition congruence. Qed.

Definition modeEq (a b : Mode) : bool :=
  match a, b with
  | R0_mode, R0_mode => true
  | R1_mode, R1_mode => true
  | R1_ODD_mode, R1_ODD_mode => true
  | _, _ => false
  end.

Lemma modeEq_eq (a b : Mode) : modeEq a b = true <-> a = b.
Proof. destruct a, b; cbn; intuition congruence. Qed.

Fixpoint wordEq (l1 l2 : list Tok) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: as_, b :: bs => tokEq a b && wordEq as_ bs
  | _, _ => false
  end.

Lemma wordEq_eq (l1 : list Tok) : forall l2, wordEq l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|a as_ ih]; intros [|b bs]; cbn [wordEq].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, tokEq_eq, ih.
    split; [intros [-> ->]; reflexivity | intros H; inverts H; auto].
Qed.

Definition isZpTok (t : Tok) : bool :=
  match t with Z_tok | P_tok => true | _ => false end.

Fixpoint isZpWord (l : list Tok) : bool :=
  match l with
  | [] => true
  | t :: ts => isZpTok t && isZpWord ts
  end.

Fixpoint revWord (w : list Tok) : list Tok :=
  match w with
  | [] => []
  | t :: ts => revWord ts ++ [t]
  end.

Lemma revWord_append (w1 w2 : list Tok) :
  revWord (w1 ++ w2) = revWord w2 ++ revWord w1.
Proof.
  induction w1 as [|t ts ih]; cbn [app revWord].
  - rewrite app_nil_r; reflexivity.
  - rewrite ih, <- app_assoc; reflexivity.
Qed.

Lemma revWord_revWord (w : list Tok) : revWord (revWord w) = w.
Proof.
  induction w as [|t ts ih]; cbn [revWord]; [reflexivity|].
  rewrite revWord_append, ih; reflexivity.
Qed.

Lemma isZpWord_append (w1 w2 : list Tok) :
  isZpWord (w1 ++ w2) = isZpWord w1 && isZpWord w2.
Proof.
  induction w1 as [|t ts ih]; cbn [app isZpWord]; [reflexivity|].
  rewrite ih, Bool.andb_assoc; reflexivity.
Qed.

Lemma isZpWord_revWord (w : list Tok) : isZpWord (revWord w) = isZpWord w.
Proof.
  induction w as [|t ts ih]; cbn [revWord isZpWord]; [reflexivity|].
  rewrite isZpWord_append, ih; cbn [isZpWord]; rewrite Bool.andb_true_r, Bool.andb_comm; reflexivity.
Qed.

Definition tokL (t : Tok) : list Sym :=
  match t with
  | U_tok => [0; 1]%sym
  | M_tok => [0; 1; 1]%sym
  | W_tok => [0; 0; 1; 1]%sym
  | Z_tok => [0; 0; 0; 0; 1; 1]%sym
  | T_tok => [0; 1; 1; 1]%sym
  | P_tok => [0; 1; 0; 0; 1; 1]%sym
  | PTTTM_TAIL_tok => []
  end.

Definition tokR (t : Tok) : list Sym :=
  match t with
  | Z_tok => [1; 0; 1; 1; 0; 1]%sym
  | P_tok => [0; 0; 1; 1; 0; 1]%sym
  | PTTTM_TAIL_tok => [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym
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
  induction w1 as [|t ts ih]; cbn [app wordL]; [reflexivity|].
  rewrite ih, app_assoc; reflexivity.
Qed.

Lemma wordR_append (w1 w2 : list Tok) :
  wordR (w1 ++ w2) = wordR w1 ++ wordR w2.
Proof.
  induction w1 as [|t ts ih]; cbn [app wordR]; [reflexivity|].
  rewrite ih, app_assoc; reflexivity.
Qed.

Fixpoint evalRleG (l_end : side) (rle : Rle) : side :=
  match rle with
  | [] => l_end
  | (w, c) :: rest => npow (wordL w) c *> evalRleG l_end rest
  end.

Section GeneralizedRle.

Variable l_end : side.

Local Notation evalRle := (evalRleG l_end).

Fixpoint evalRStack (rs : Rle) (r_end : side) : side :=
  match rs with
  | [] => r_end
  | (w, c) :: rest => npow (wordR (revWord w)) c *> evalRStack rest r_end
  end.

Definition pushRlePos (w : list Tok) (c : N) (rle : Rle) : Rle :=
  match rle with
  | [] => [(w, c)]
  | (w', c') :: rest =>
    if wordEq w w' then (w, (c + c')%N) :: rest
    else (w, c) :: (w', c') :: rest
  end.

Definition pushRle (w : list Tok) (c : N) (rle : Rle) : Rle :=
  if (c =? 0)%N then rle else pushRlePos w c rle.

Lemma evalRle_pushRlePos (w : list Tok) (c : N) (rle : Rle) :
  evalRle (pushRlePos w c rle) = npow (wordL w) c *> evalRle rle.
Proof.
  destruct rle as [|[w' c'] rest]; cbn [pushRlePos evalRleG]; [reflexivity|].
  destruct (wordEq w w') eqn:Hw; cbn [evalRleG].
  - apply wordEq_eq in Hw; subst w'.
    rewrite npow_add, Str_app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma evalRle_pushRle (w : list Tok) (c : N) (rle : Rle) :
  evalRle (pushRle w c rle) = npow (wordL w) c *> evalRle rle.
Proof.
  unfold pushRle. destruct (c =? 0)%N eqn:Hc.
  - apply N.eqb_eq in Hc; subst c; rewrite npow_0; reflexivity.
  - apply evalRle_pushRlePos.
Qed.

Lemma evalRle_pushRlePos_one (w : list Tok) (rle : Rle) :
  evalRle (pushRlePos w 1%N rle) = wordL w *> evalRle rle.
Proof.
  rewrite evalRle_pushRlePos, npow_1. reflexivity.
Qed.

Lemma evalRStack_pushRlePos (w : list Tok) (c : N) (rs : Rle) (r_end : side) :
  evalRStack (pushRlePos w c rs) r_end = npow (wordR (revWord w)) c *> evalRStack rs r_end.
Proof.
  destruct rs as [|[w' c'] rest]; cbn [pushRlePos evalRStack]; [reflexivity|].
  destruct (wordEq w w') eqn:Hw; cbn [evalRStack].
  - apply wordEq_eq in Hw; subst w'.
    rewrite npow_add, Str_app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma evalRStack_pushRle (w : list Tok) (c : N) (rs : Rle) (r_end : side) :
  evalRStack (pushRle w c rs) r_end = npow (wordR (revWord w)) c *> evalRStack rs r_end.
Proof.
  unfold pushRle. destruct (c =? 0)%N eqn:Hc.
  - apply N.eqb_eq in Hc; subst c; rewrite npow_0; reflexivity.
  - apply evalRStack_pushRlePos.
Qed.

Local Opaque pushRlePos pushRle.

Fixpoint pushToksLtr (ts : list Tok) (rle : Rle) : Rle :=
  match ts with
  | [] => rle
  | t :: ts' => pushToksLtr ts' (pushRlePos [t] 1%N rle)
  end.

Lemma evalRle_pushToksLtr (ts : list Tok) : forall (rle : Rle),
  evalRle (pushToksLtr ts rle) = wordL (revWord ts) *> evalRle rle.
Proof.
  induction ts as [|t ts ih]; intro rle; cbn [pushToksLtr revWord wordL]; [reflexivity|].
  rewrite ih, evalRle_pushRlePos_one, wordL_append, Str_app_assoc; cbn [wordL]; rewrite app_nil_r.
  reflexivity.
Qed.

Definition popLastTok (rle : Rle) : option (Tok * Rle) :=
  match rle with
  | [] => None
  | (w, c) :: rest =>
    match w with
    | [] => None
    | t :: ts =>
      if (c =? 0)%N then None
      else
        match ts with
        | [] =>
          if (c =? 1)%N then Some (t, rest)
          else Some (t, ([t], (c - 1)%N) :: rest)
        | t2 :: ts2 =>
          if (c =? 1)%N then Some (t, pushRlePos (t2 :: ts2) 1%N rest)
          else Some (t, pushRlePos (t2 :: ts2) 1%N ((t :: t2 :: ts2, (c - 1)%N) :: rest))
        end
    end
  end.

Lemma popLastTok_sound (rle : Rle) (t : Tok) (rle' : Rle)
  (h : popLastTok rle = Some (t, rle')) :
  evalRle rle = tokL t *> evalRle rle'.
Proof.
  destruct rle as [|[w c] rest]; [discriminate|].
  destruct w as [|t0 ts]; [discriminate|].
  cbn [popLastTok] in h.
  destruct (c =? 0)%N eqn:Hc0; [discriminate|].
  apply N.eqb_neq in Hc0.
  assert (Hc_split : c = (1 + (c - 1))%N) by lia.
  destruct ts as [|t2 ts2].
  - destruct (c =? 1)%N eqn:Hc1; inverts h.
    + apply N.eqb_eq in Hc1; subst c.
      cbn [evalRleG]; rewrite npow_1; cbn [wordL]; rewrite app_nil_r; reflexivity.
    + cbn [evalRleG]; rewrite Hc_split at 1; rewrite npow_add, npow_1, Str_app_assoc.
      cbn [wordL]; rewrite app_nil_r; reflexivity.
  - destruct (c =? 1)%N eqn:Hc1; inverts h.
    + apply N.eqb_eq in Hc1; subst c.
      cbn [evalRleG]; rewrite evalRle_pushRlePos_one, npow_1; cbn [wordL]; rewrite Str_app_assoc; reflexivity.
    + cbn [evalRleG]; rewrite evalRle_pushRlePos_one; cbn [evalRleG].
      rewrite Hc_split at 1; rewrite npow_add, npow_1, Str_app_assoc.
      cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Definition popTok (t_exp : Tok) (rle : Rle) : option Rle :=
  match popLastTok rle with
  | None => None
  | Some (t, rle') => if tokEq t t_exp then Some rle' else None
  end.

Lemma popTok_sound (t_exp : Tok) (rle rle' : Rle)
  (h : popTok t_exp rle = Some rle') :
  evalRle rle = tokL t_exp *> evalRle rle'.
Proof.
  unfold popTok in h.
  destruct (popLastTok rle) as [[t r1]|] eqn:Hp; [|discriminate].
  destruct (tokEq t t_exp) eqn:Ht; [|discriminate].
  inverts h; apply tokEq_eq in Ht; subst t.
  exact (popLastTok_sound rle t_exp rle' Hp).
Qed.

Fixpoint popToks (ts : list Tok) (rle : Rle) : option Rle :=
  match ts with
  | [] => Some rle
  | t :: ts' =>
    match popTok t rle with
    | Some rle1 => popToks ts' rle1
    | None => None
    end
  end.

Lemma popToks_sound (ts : list Tok) : forall (rle rle' : Rle),
  popToks ts rle = Some rle' ->
  evalRle rle = wordL ts *> evalRle rle'.
Proof.
  induction ts as [|t ts ih]; intros rle rle' h; cbn [popToks] in h.
  - inverts h; reflexivity.
  - destruct (popTok t rle) as [r1|] eqn:Hp; [|discriminate].
    rewrite (popTok_sound t rle r1 Hp), (ih r1 rle' h); cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Fixpoint popTokCount (fuel : nat) (t_exp : Tok) (acc : N) (rle : Rle) : N * Rle :=
  match fuel with
  | O => (acc, rle)
  | S fuel' =>
    match rle with
    | [] => (acc, [])
    | ([], c) :: rest => (acc, ([], c) :: rest)
    | (t :: ts, c) :: rest =>
      if tokEq t t_exp then
        if (c =? 0)%N then (acc, (t :: ts, c) :: rest)
        else
          match ts with
          | [] => popTokCount fuel' t_exp (acc + c)%N rest
          | t2 :: ts2 =>
            if (c =? 1)%N then popTokCount fuel' t_exp (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N rest)
            else popTokCount fuel' t_exp (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N ((t :: t2 :: ts2, (c - 1)%N) :: rest))
          end
      else (acc, (t :: ts, c) :: rest)
    end
  end.

Lemma popTokCount_sound (fuel : nat) (t_exp : Tok) : forall (acc : N) (rle : Rle),
  (acc <= fst (popTokCount fuel t_exp acc rle))%N /\
  npow (tokL t_exp) acc *> evalRle rle =
    npow (tokL t_exp) (fst (popTokCount fuel t_exp acc rle)) *> evalRle (snd (popTokCount fuel t_exp acc rle)).
Proof.
  induction fuel as [|fuel ih]; intros acc rle; [cbn [popTokCount fst snd]; split; [lia | reflexivity]|].
  destruct rle as [|[[|t ts] c] rest]; cbn [popTokCount fst snd]; try (split; [lia | reflexivity]).
  destruct (tokEq t t_exp) eqn:Ht; [|cbn [fst snd]; split; [lia | reflexivity]].
  apply tokEq_eq in Ht; subst t.
  destruct (c =? 0)%N eqn:Hc0; [cbn [fst snd]; split; [lia | reflexivity]|].
  apply N.eqb_neq in Hc0.
  assert (Hc_split : c = (1 + (c - 1))%N) by lia.
  destruct ts as [|t2 ts2].
  - destruct (ih (acc + c)%N rest) as [Hle Heq].
    split; [lia |].
    rewrite <- Heq; cbn [evalRleG wordL]; rewrite app_nil_r, npow_add, Str_app_assoc; reflexivity.
  - destruct (c =? 1)%N eqn:Hc1.
    + apply N.eqb_eq in Hc1; subst c.
      destruct (ih (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N rest)) as [Hle Heq].
      split; [lia |].
      rewrite <- Heq, evalRle_pushRlePos_one, npow_add; cbn [evalRleG wordL].
      rewrite !npow_1, !Str_app_assoc; reflexivity.
    + destruct (ih (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N ((t_exp :: t2 :: ts2, (c - 1)%N) :: rest))) as [Hle Heq].
      split; [lia |].
      rewrite <- Heq, evalRle_pushRlePos_one; cbn [evalRleG].
      rewrite (npow_add (tokL t_exp) acc 1%N), npow_1, !Str_app_assoc.
      f_equal. rewrite Hc_split at 1.
      rewrite (npow_add (wordL (t_exp :: t2 :: ts2)) 1%N (c - 1)%N), npow_1, !Str_app_assoc.
      cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Local Opaque popTokCount.

Definition evalWK (k1 : N) : side :=
  [1; 0; 1; 1]%sym *> npow [0; 0; 1; 1]%sym k1 *> 0inf.

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
  r1OddShortCfg (tokL Z_tok *> l) r.

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

Ltac solve_wstep n c1 c2 l r :=
  exact (wmultiStep_sound tm n c1 c2 l r ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Ltac solve_cstep n c1 c2 r :=
  exact (cmultiStep_sound tm n c1 c2 r ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Ltac solve_rcstep n c1 c2 l :=
  exact (rcmultiStep_sound tm n c1 c2 l ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Lemma carry_Z (l r : side) :
  carryCfg (tokL Z_tok *> l) r -[ tm ]->* carryCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 54
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_P (l r : side) :
  carryCfg (tokL P_tok *> l) r -[ tm ]->* carryCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 18
    (mkCCfg B 1%sym [0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 78
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTW (l r : side) :
  carryCfg (tokL W_tok *> npow (tokL T_tok) 2%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 3%N *> r).
Proof.
  solve_wstep 120
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTT (l r : side) :
  carryCfg (npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 84
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTTM (l r : side) :
  carryCfg (tokL M_tok *> npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR PTTTM_TAIL_tok *> r).
Proof.
  solve_wstep 99
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_UM (r : side) :
  carryCfg (tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 61
    (mkCCfg B 1%sym [0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_UMT (r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 97
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_ZT (l r : side) :
  carryCfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 61
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_WM (l r : side) :
  carryCfg (tokL M_tok *> tokL W_tok *> l) r -[ tm ]->*
  r1Cfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 55
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PT (l r : side) :
  carryCfg (tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 115
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZM (l r : side) :
  carryCfg (tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 55
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 141
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 97
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 103
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL T_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 111
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 121
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 127
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 127
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_MUTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 141
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 163
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 163
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 109
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZPMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL P_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 163
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 157
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 205
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma carry_MU_to_pmuCfg (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 17
    (mkCCfg B 1%sym [0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmu_step (l r : side) :
  pmuCfg (tokL P_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 60
    (mkCCfg D 1%sym [0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_Z_turn (l r : side) :
  pmuCfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->*
  r0Cfg (tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 38
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma pmuCfg_M_to_carry (l r : side) :
  pmuCfg (tokL M_tok *> l) r -[ tm ]->*
  carryCfg (tokL U_tok *> l) r.
Proof.
  solve_wstep 7
    (mkCCfg D 1%sym [0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_T_to_carry (l r : side) :
  pmuCfg (tokL T_tok *> l) r -[ tm ]->*
  carryCfg (tokL M_tok *> l) r.
Proof.
  solve_wstep 7
    (mkCCfg D 1%sym [0; 1; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTU (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg (tokL Z_tok *> l) (tokR P_tok *> r).
Proof.
  solve_wstep 30
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_PTMT (l r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 163
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 163
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 145
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTU_halt (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  (F, ([1; 1; 0; 1; 1; 0; 1; 1; 1]%sym *> l, 0%sym, [0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).
Proof.
  solve_wstep 33
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg F 0%sym [1; 1; 0; 1; 1; 0; 1; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma r0_Z (l r : side) :
  r0Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_P (l r : side) :
  r0Cfg l (tokR P_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 48
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_PTTTM_TAIL (l r : side) :
  r0Cfg l (tokR PTTTM_TAIL_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 15
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_Z (l r : side) :
  r1Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_P (l r : side) :
  r1Cfg l (tokR P_tok *> r) -[ tm ]->* r1OddCfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 68
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShort_Z (l r : side) :
  r1OddShortCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddShortCfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_P (l r : side) :
  r1OddCfg l (tokR P_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_start (l : side) :
  cfgR l -[ tm ]->* wSweepCfg l 0inf.
Proof.
  solve_rcstep 2
    (mkCCfg B 0%sym [1; 1]%sym []%sym)
    (mkCCfg D 1%sym []%sym [1]%sym) l.
Qed.

Lemma wSweep_step (l r : side) :
  wSweepCfg (tokL W_tok *> l) r -[ tm ]->* wSweepCfg l ([0; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 6
    (mkCCfg D 1%sym [0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 1]%sym) l r.
Qed.

Lemma dSweep_step (l r : side) :
  dSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL W_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 1%sym [0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma dSweep_end (l : side) :
  dSweepCfg l 0inf -[ tm ]->* cfgR (tokL W_tok *> l).
Proof.
  solve_rcstep 5
    (mkCCfg E 1%sym [0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma tSweep_step (l r : side) :
  tSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 24
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma tSweep_end (l : side) :
  tSweepCfg l 0inf -[ tm ]->* cfgR (tokL Z_tok *> l).
Proof.
  solve_rcstep 2
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma r0_to_dSweep (l r : side) :
  r0Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_to_dSweep (l r : side) :
  r1Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_to_tSweep (l r : side) :
  r1OddCfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_Z_to_dSweep (l r : side) :
  wSweepCfg (tokL Z_tok *> l) r -[ tm ]->* dSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 11
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_ZT_to_dSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  dSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 53
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_PT_to_carry (l r : side) :
  wSweepCfg (tokL T_tok *> tokL P_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  carryCfg l ([1; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 40
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1]%sym) l r.
Qed.

Lemma wSweep_ZMT_to_tSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  tSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 77
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma cfgR_Z_to_TW (l : side) :
  cfgR (tokL Z_tok *> l) -[ tm ]->* cfgR (tokL W_tok *> tokL T_tok *> l).
Proof.
  solve_rcstep 18
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l.
Qed.

Lemma cfgR_TW_to_t3Cfg (l : side) :
  cfgR (tokL W_tok *> tokL T_tok *> l) -[ tm ]->* t3Cfg l (evalWK 0%N).
Proof.
  solve_rcstep 30
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym) l.
Qed.

Lemma t3_step (l r : side) :
  t3Cfg (npow (tokL T_tok) 3%N *> l) r -[ tm ]->* t3Cfg l (npow (tokR Z_tok) 2%N *> r).
Proof.
  solve_wstep 66
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma t3Cfg_Z_zero_to_carry (l : side) :
  t3Cfg (tokL Z_tok *> l) (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 120
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_Z_succ_to_r0 (l r : side) :
  t3Cfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 37
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma t3Cfg_TZ_to_r1OddShort (l r : side) :
  t3Cfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->* r1OddShortCfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 51
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShortCfg_evalWK0_to_carry (l : side) :
  r1OddShortCfg l (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 180
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_TTZ_to_r0 (l r : side) :
  t3Cfg (npow (tokL T_tok) 2%N *> tokL Z_tok *> l) r -[ tm ]->* r0Cfg (tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 79
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_Z (l r : side) :
  r1OddCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddCfg (tokL Z_tok *> l) r.
Proof.
  exact (r1OddShort_Z (tokL Z_tok *> l) r).
Qed.

Lemma wSweep_loop : forall (n : N) (l r : side),
  wSweepCfg (npow (tokL W_tok) n *> l) r -[ tm ]->*
  wSweepCfg l (npow [0; 0; 1; 1]%sym n *> r).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply wSweep_step|].
    rewrite (npow_succ_r [0; 0; 1; 1]%sym n), Str_app_assoc.
    apply ih.
Qed.

Lemma dSweep_loop : forall (n : N) (l r : side),
  dSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  dSweepCfg (npow (tokL W_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply dSweep_step|].
    rewrite (npow_succ_r (tokL W_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma tSweep_loop : forall (n : N) (l r : side),
  tSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  tSweepCfg (npow (tokL T_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply tSweep_step|].
    rewrite (npow_succ_r (tokL T_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma t3_loop : forall (q : N) (l r : side),
  t3Cfg (npow (tokL T_tok) (3 * q)%N *> l) r -[ tm ]->*
  t3Cfg l (npow (tokR Z_tok) (2 * q)%N *> r).
Proof.
  induction q as [|q ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - replace (3 * (q + 1))%N with (3 + 3 * q)%N by lia.
    replace (2 * (q + 1))%N with (2 * q + 2)%N by lia.
    rewrite (npow_add (tokL T_tok) 3%N (3 * q)%N), Str_app_assoc.
    eapply evstep_trans; [apply t3_step|].
    rewrite (npow_add (tokR Z_tok) (2 * q)%N 2%N), Str_app_assoc.
    apply ih.
Qed.

Lemma pmu_loop : forall (m : N) (l r : side),
  pmuCfg (npow (tokL P_tok) m *> l) r -[ tm ]->*
  pmuCfg l (npow (tokR Z_tok) m *> r).
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply pmu_step|].
    rewrite (npow_succ_r (tokR Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_Z_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_P_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR P_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_P|].
    rewrite (npow_succ_r (tokL P_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r1OddShort_Z_loop : forall (m : N) (l r : side),
  r1OddShortCfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r1OddShortCfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r1OddShort_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma cfgR_ZW_to_TW (n : N) (l : side) :
  cfgR (npow (tokL W_tok) n *> tokL Z_tok *> l) -[ tm ]->*
  cfgR (npow (tokL W_tok) (n + 1)%N *> tokL T_tok *> l).
Proof.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop n (tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply wSweep_Z_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop n (tokL T_tok *> l) 0inf)|].
  rewrite npow_succ_l, Str_app_assoc.
  apply dSweep_end.
Qed.

Lemma r0_end (k1 : N) (l : side) :
  r0Cfg l (evalWK k1) -[ tm ]->* carryCfg l (evalWK (k1 + 2)%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r0_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop k1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 1)%N (tokL Z_tok *> l))|].
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 2)%N (tokL T_tok *> tokL Z_tok *> l) 0inf)|].
  replace (k1 + 2)%N with ((k1 + 1) + 1)%N at 1 by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZT_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop (k1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 2)%N (tokL P_tok *> l))|].
  replace (k1 + 2 + 1)%N with (k1 + 3)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 3)%N (tokL T_tok *> tokL P_tok *> l) 0inf)|].
  replace (k1 + 3)%N with ((k1 + 2) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 2)%N), Str_app_assoc.
  unfold evalWK; apply wSweep_PT_to_carry.
Qed.

Lemma r1_end (kf1 : N) (l : side) :
  r1Cfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) (kf1 + 1)%N *> tokL Z_tok *> tokL P_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop kf1 (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (kf1 + 1)%N (tokL M_tok *> tokL Z_tok *> l))|].
  replace (kf1 + 1 + 1)%N with (kf1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (kf1 + 2)%N (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  replace (kf1 + 2)%N with ((kf1 + 1) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (kf1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZMT_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop (kf1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Lemma r1Odd_end (kf1 : N) (l : side) :
  r1OddCfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) kf1 *> tokL Z_tok *> tokL Z_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1Odd_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop kf1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Definition stepZtToCarry (rle2 : Rle) (n : N) : Rle * N :=
  let qr := N.div_eucl n 3%N in
  let q := fst qr in
  let rem := snd qr in
  if (rem =? 0)%N then
    if (q =? 0)%N then (rle2, 1%N)
    else (pushRle [Z_tok] (2 * q - 1)%N (pushRlePos [P_tok] 1%N rle2), 2%N)
  else if (rem =? 1)%N then
    (pushRle [Z_tok] (2 * q)%N (pushToksLtr [T_tok; M_tok] rle2), 1%N)
  else
    (pushRle [Z_tok] (2 * q)%N (pushToksLtr [T_tok; W_tok] rle2), 2%N).

Lemma stepZtToCarry_sound (rle2 : Rle) (n : N) :
  t3Cfg (npow (tokL T_tok) n *> tokL Z_tok *> evalRle rle2) (evalWK 0%N) -[ tm ]->*
  carryCfg (evalRle (fst (stepZtToCarry rle2 n))) (evalWK (snd (stepZtToCarry rle2 n))).
Proof.
  unfold stepZtToCarry; cbn zeta.
  fold (N.div n 3%N) (N.modulo n 3%N).
  pose proof (N.div_mod n 3 ltac:(discriminate)) as Hdiv.
  pose proof (N.mod_upper_bound n 3 ltac:(discriminate)) as Hmod.
  set (q := (n / 3)%N) in *.
  set (rem := (n mod 3)%N) in *.
  replace n with (3 * q + rem)%N at 1 by lia.
  rewrite (npow_add (tokL T_tok) (3 * q)%N rem), Str_app_assoc.
  eapply evstep_trans; [apply (t3_loop q (npow (tokL T_tok) rem *> tokL Z_tok *> evalRle rle2) (evalWK 0%N))|].
  assert (Hrem : rem = 0%N \/ rem = 1%N \/ rem = 2%N) by lia.
  destruct Hrem as [Hrem | [Hrem | Hrem]]; rewrite Hrem; cbn [N.eqb Pos.eqb fst snd].
  - rewrite npow_0; cbn [Str_app].
    destruct (q =? 0)%N eqn:Hq0; cbn [fst snd].
    + apply N.eqb_eq in Hq0; rewrite Hq0.
      cbn [N.mul npow Str_app].
      apply t3Cfg_Z_zero_to_carry.
    + apply N.eqb_neq in Hq0.
      replace (2 * q)%N with (1 + (2 * q - 1))%N at 1 by lia.
      rewrite (npow_add (tokR Z_tok) 1%N (2 * q - 1)%N), npow_1, Str_app_assoc.
      eapply evstep_trans; [apply t3Cfg_Z_succ_to_r0|].
      eapply evstep_trans; [apply (r0_Z_loop (2 * q - 1)%N (tokL P_tok *> evalRle rle2) (evalWK 0%N))|].
      rewrite evalRle_pushRle, evalRle_pushRlePos_one; cbn [wordL]; rewrite app_nil_r.
      apply (r0_end 0%N).
  - rewrite npow_1.
    eapply evstep_trans; [apply t3Cfg_TZ_to_r1OddShort|].
    eapply evstep_trans; [apply (r1OddShort_Z_loop (2 * q)%N (tokL M_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply r1OddShortCfg_evalWK0_to_carry.
  - rewrite npow_2, Str_app_assoc.
    eapply evstep_trans; [apply t3Cfg_TTZ_to_r0|].
    eapply evstep_trans; [apply (r0_Z_loop (2 * q)%N (tokL W_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply (r0_end 0%N).
Qed.

Local Opaque stepZtToCarry.

Lemma carry_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (wordL w *> l) r -[ tm ]->*
  carryCfg l (wordR (revWord w) *> r).
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordL revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply carry_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply carry_P | apply (ih _ _ hts)].
Qed.

Lemma carry_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (npow (wordL w) c *> l) r -[ tm ]->*
  carryCfg l (npow (wordR (revWord w)) c *> r).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordL w) c), Str_app_assoc.
    eapply evstep_trans; [apply (carry_word w _ _ hw)|].
    rewrite (npow_succ_r (wordR (revWord w)) c), Str_app_assoc.
    apply (ih w l _ hw).
Qed.

Definition popCarrySpecial (rle rs : Rle) : option (Rle * Rle) :=
  match popLastTok rle with
  | None => None
  | Some (t1, r1) =>
    match t1 with
    | U_tok =>
      match popLastTok r1 with
      | None => None
      | Some (t2, r2) =>
        match t2 with
        | M_tok =>
          let '(mVal, r3) := popTokCount 8 P_tok 0%N r2 in
          if (mVal =? 0)%N then None
          else
            match popLastTok r3 with
            | None => None
            | Some (M_tok, r4) =>
              Some (pushRlePos [U_tok] 1%N r4,
                    pushRlePos [Z_tok] mVal (pushRlePos [P_tok] 1%N rs))
            | Some (T_tok, r4) =>
              Some (pushRlePos [M_tok] 1%N r4,
                    pushRlePos [Z_tok] mVal (pushRlePos [P_tok] 1%N rs))
            | Some (_, _) => None
            end
        | T_tok =>
          match popTok P_tok r2 with
          | None => None
          | Some r3 => Some (pushRlePos [Z_tok] 1%N r3, pushRlePos [P_tok] 1%N rs)
          end
        | _ => None
        end
      end
    | M_tok =>
      match popToks [T_tok; U_tok; M_tok; P_tok] r1 with
      | Some r5 => Some (r5, pushRlePos [Z_tok] 2%N (pushRlePos [P_tok] 1%N rs))
      | None =>
        match popToks [T_tok; T_tok; T_tok; P_tok] r1 with
        | Some r5 => Some (r5, pushRlePos [Z_tok] 2%N (pushRlePos [PTTTM_TAIL_tok] 1%N rs))
        | None => None
        end
      end
    | W_tok =>
      match popToks [T_tok; T_tok; P_tok] r1 with
      | Some r4 => Some (r4, pushRlePos [Z_tok] 3%N rs)
      | None => None
      end
    | T_tok =>
      match popToks [T_tok; T_tok; P_tok] r1 with
      | Some r4 => Some (r4, pushRlePos [Z_tok] 2%N (pushRlePos [P_tok] 1%N rs))
      | None => None
      end
    | _ => None
    end
  end.

Lemma popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : side)
  (h : popCarrySpecial rle rs = Some (rle', rs')) :
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle rle') (evalRStack rs' r_end).
Proof.
  unfold popCarrySpecial in h.
  destruct (popLastTok rle) as [[t1 r1]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound rle t1 r1 Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popLastTok r1) as [[t2 r2]|] eqn:Hp2; [|discriminate].
    rewrite (popLastTok_sound r1 t2 r2 Hp2).
    destruct t2; try discriminate.
    +  
      pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2)) as Hpcs.
      destruct (popTokCount 8 P_tok 0%N r2) as [mVal r3] eqn:Hpc.
      cbn [fst snd] in Hpcs; rewrite npow_0 in Hpcs; cbn [Str_app] in Hpcs.
      rewrite Hpcs.
      destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
      destruct (popLastTok r3) as [[t3 r4]|] eqn:Hp3; [|discriminate].
      rewrite (popLastTok_sound r3 t3 r4 Hp3).
      destruct t3; try discriminate; inverts h.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL M_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_M_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL T_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_T_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
    +  
      destruct (popTok P_tok r2) as [r3|] eqn:Hp3; [|discriminate].
      inverts h.
      rewrite (popTok_sound P_tok r2 r3 Hp3).
      rewrite evalRle_pushRlePos_one, evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite !app_nil_r.
      apply carry_PTU.
  -  
    destruct (popToks [T_tok; U_tok; M_tok; P_tok] r1) as [r5|] eqn:Hp2.
    + rewrite (popToks_sound _ r1 r5 Hp2).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PMUTM.
    + destruct (popToks [T_tok; T_tok; T_tok; P_tok] r1) as [r5|] eqn:Hp3; [|discriminate].
      rewrite (popToks_sound _ r1 r5 Hp3).
      cbn [wordL app]; rewrite ?Str_app_assoc.
      change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r5)
        with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r5).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PTTTM.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 2%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTW.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos, npow_1.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTT.
Qed.

Local Opaque popCarrySpecial.

Fixpoint popCarryLoop (fuel : nat) (rle rs : Rle) : Rle * Rle :=
  match fuel with
  | O => (rle, rs)
  | S fuel' =>
    match rle with
    | [] => ([], rs)
    | (w, c) :: rest =>
      if isZpWord w then
        popCarryLoop fuel' rest (pushRlePos w c rs)
      else
        match popCarrySpecial ((w, c) :: rest) rs with
        | None => ((w, c) :: rest, rs)
        | Some (rle', rs') => popCarryLoop fuel' rle' rs'
        end
    end
  end.

Lemma popCarryLoop_sound : forall (fuel : nat) (rle rs : Rle) (r_end : side),
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle (fst (popCarryLoop fuel rle rs))) (evalRStack (snd (popCarryLoop fuel rle rs)) r_end).
Proof.
  induction fuel as [|fuel ih]; intros rle rs r_end; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  destruct rle as [|[w c] rest]; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  cbn [popCarryLoop].
  destruct (isZpWord w) eqn:Hw.
  - cbn [evalRleG].
    eapply evstep_trans; [apply (carry_pow c w (evalRle rest) (evalRStack rs r_end) Hw)|].
    rewrite <- (evalRStack_pushRlePos w c rs r_end).
    apply ih.
  - destruct (popCarrySpecial ((w, c) :: rest) rs) as [[rle' rs']|] eqn:Hsp.
    + eapply evstep_trans; [apply (popCarrySpecial_sound _ _ _ _ r_end Hsp)|].
      apply ih.
    + cbn [fst snd]; apply evstep_refl.
Qed.

Local Opaque popCarryLoop.

Lemma r0_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (wordR w *> r) -[ tm ]->*
  r0Cfg (wordL (revWord w) *> l) r.
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordR revWord]; rewrite wordL_append; cbn [wordL]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply r0_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply r0_P | apply (ih _ _ hts)].
Qed.

Lemma r0_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (npow (wordR w) c *> r) -[ tm ]->*
  r0Cfg (npow (wordL (revWord w)) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR w) c), Str_app_assoc.
    eapply evstep_trans; [apply (r0_word w _ _ hw)|].
    rewrite (npow_succ_r (wordL (revWord w)) c), Str_app_assoc.
    apply (ih w _ _ hw).
Qed.

Fixpoint allZpStack (rs : Rle) : bool :=
  match rs with
  | [] => true
  | (w, _) :: rest => isZpWord w && allZpStack rest
  end.

Fixpoint copyRStack (rle rs : Rle) : option Rle :=
  match rs with
  | [] => Some rle
  | (item, count) :: rest =>
    if isZpWord item then copyRStack (pushRlePos item count rle) rest
    else None
  end.

Lemma copyRStack_sound : forall (rs : Rle) (rle rle' : Rle) (r_end : side),
  copyRStack rle rs = Some rle' ->
  allZpStack rs = true /\
  r0Cfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->* r0Cfg (evalRle rle') r_end.
Proof.
  induction rs as [|[w c] rest ih]; intros rle rle' r_end h; cbn [copyRStack] in h.
  - inverts h; cbn [allZpStack evalRStack]; split; [reflexivity | apply evstep_refl].
  - destruct (isZpWord w) eqn:Hw; [|discriminate].
    destruct (ih (pushRlePos w c rle) rle' r_end h) as [Hrest Hstep].
    cbn [allZpStack]; rewrite Hw, Hrest; split; [reflexivity|].
    cbn [evalRStack].
    assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact Hw).
    eapply evstep_trans; [apply (r0_pow c (revWord w) (evalRle rle) (evalRStack rest r_end) Hrev)|].
    rewrite revWord_revWord, <- evalRle_pushRlePos.
    exact Hstep.
Qed.

Definition HasRoundtrip (R : N -> side) : Prop :=
  forall (l : side) (k1 : N),
    r0Cfg l (R k1) -[ tm ]->* carryCfg l (R (k1 + 2)%N).

Lemma hasRoundtrip_evalWK : HasRoundtrip evalWK.
Proof.
  intros l k1. exact (r0_end k1 l).
Qed.

Lemma hasRoundtrip_Z (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR Z_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_Z|].
  eapply evstep_trans; [apply (hR (tokL Z_tok *> l) k1)|].
  apply carry_Z.
Qed.

Lemma hasRoundtrip_P (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR P_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_P|].
  eapply evstep_trans; [apply (hR (tokL P_tok *> l) k1)|].
  apply carry_P.
Qed.

Lemma hasRoundtrip_word : forall (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => wordR w *> R k1).
Proof.
  induction w as [|t ts ih]; intros R hw hR; [exact hR|].
  cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
  destruct t; try discriminate; intros l k1; cbn [wordR]; rewrite Str_app_assoc.
  - exact (hasRoundtrip_Z _ (ih R hts hR) l k1).
  - exact (hasRoundtrip_P _ (ih R hts hR) l k1).
Qed.

Lemma hasRoundtrip_pow : forall (c : N) (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => npow (wordR w) c *> R k1).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w R hw hR; [exact hR|].
  intros l k1.
  rewrite (npow_succ_l (wordR w) c), !Str_app_assoc.
  exact (hasRoundtrip_word w _ hw (ih w R hw hR) l k1).
Qed.

Lemma hasRoundtrip_stack : forall (rs : Rle) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => evalRStack rs (R k1)).
Proof.
  induction rs as [|[w c] rest ih]; intros R hrs hR; [exact hR|].
  cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hw hrest].
  intros l k1; cbn [evalRStack].
  assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
  exact (hasRoundtrip_pow c (revWord w) _ Hrev (ih R hrest hR) l k1).
Qed.

Definition r1PhaseCfg (phase : bool) (l r : side) : Q * tape :=
  if phase then r1OddCfg l r else r1Cfg l r.

Fixpoint stepR1StarWordL (w : list Tok) (phase : bool) : list Tok * N * bool :=
  match w with
  | [] => ([], 0%N, phase)
  | t :: ts =>
    let '(out, res, p1) := stepR1StarWordL ts phase in
    if p1 then
      if tokEq t P_tok then (Z_tok :: out, res, false) else (Z_tok :: out, res, true)
    else
      if tokEq t Z_tok then (P_tok :: out, (res + 1)%N, false) else (P_tok :: out, res, true)
  end.

Definition r1_out (s : list Tok * N * bool) : list Tok := fst (fst s).

Definition r1_res (s : list Tok * N * bool) : N := snd (fst s).

Definition r1_phase (s : list Tok * N * bool) : bool := snd s.

Lemma stepR1StarWordL_phase_inv : forall (w : list Tok) (phase : bool),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w (negb phase)) = negb (r1_phase (stepR1StarWordL w phase)).
Proof.
  induction w as [|t ts ih]; intros phase hw; [reflexivity|].
  cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
  pose proof (ih phase hts) as Hih.
  cbn [stepR1StarWordL].
  destruct (stepR1StarWordL ts (negb phase)) as [[o1 r1] p1] eqn:H1.
  destruct (stepR1StarWordL ts phase) as [[o2 r2] p2] eqn:H2.
  unfold r1_phase in Hih; cbn [snd] in Hih; subst p1.
  destruct t; try discriminate; destruct p2; reflexivity.
Qed.

Lemma stepR1StarWordL_sound : forall (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (wordR (revWord w) *> R k1) -[ tm ]->*
    r1PhaseCfg (r1_phase (stepR1StarWordL w phase))
      (wordL (r1_out (stepR1StarWordL w phase)) *> l)
      (R (k1 + 2 * r1_res (stepR1StarWordL w phase))%N).
Proof.
  induction w as [|t ts ih]; intros phase l R hw hR k1.
  - cbn [stepR1StarWordL r1_phase r1_out r1_res revWord wordR wordL fst snd].
    replace (k1 + 2 * 0)%N with k1 by lia.
    apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    assert (hRt : HasRoundtrip (fun k => tokR t *> R k)).
    { destruct t; try discriminate; [exact (hasRoundtrip_Z R hR) | exact (hasRoundtrip_P R hR)]. }
    pose proof (ih phase l (fun k => tokR t *> R k) hts hRt k1) as Hih.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [exact Hih|].
    cbn [stepR1StarWordL].
    destruct (stepR1StarWordL ts phase) as [[out res] p1] eqn:Hs.
    unfold r1_phase, r1_out, r1_res; cbn [fst snd].
    destruct t; try discriminate; destruct p1; cbn [tokEq r1PhaseCfg r1_phase r1_out r1_res fst snd wordL];
    rewrite ?Str_app_assoc.
    +  
      apply r1Odd_Z.
    +  
      eapply evstep_trans; [apply r1_Z|].
      eapply evstep_trans; [apply (hR (tokL M_tok *> tokL Z_tok *> wordL out *> l) (k1 + 2 * res)%N)|].
      replace (k1 + 2 * res + 2)%N with (k1 + 2 * (res + 1))%N by lia.
      apply turn_ZM.
    +  
      apply r1Odd_P.
    +  
      apply r1_P.
Qed.

Lemma stepR1Star_same_pow : forall (c : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w phase) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (npow (wordR (revWord w)) c *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out (stepR1StarWordL w phase))) c *> l)
      (R (k1 + 2 * (c * r1_res (stepR1StarWordL w phase)))%N).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w phase l R hw hsame hR k1.
  - cbn [npow Str_app]; replace (k1 + 2 * (0 * r1_res (stepR1StarWordL w phase)))%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    pose proof (hasRoundtrip_pow c (revWord w) R Hrev hR) as hR'.
    rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    pose proof (stepR1StarWordL_sound w phase l _ hw hR' k1) as H1.
    rewrite hsame in H1.
    eapply evstep_trans; [exact H1|].
    pose proof (ih w phase (wordL (r1_out (stepR1StarWordL w phase)) *> l) R hw hsame hR
      (k1 + 2 * r1_res (stepR1StarWordL w phase))%N) as Hih.
    replace (k1 + 2 * r1_res (stepR1StarWordL w phase) + 2 * (c * r1_res (stepR1StarWordL w phase)))%N
      with (k1 + 2 * ((c + 1) * r1_res (stepR1StarWordL w phase)))%N in Hih by lia.
    rewrite (npow_succ_r (wordL (r1_out (stepR1StarWordL w phase))) c), Str_app_assoc.
    exact Hih.
Qed.

Lemma stepR1Star_alt_pow : forall (q : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w (r1_phase (stepR1StarWordL w phase))) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    let s1 := stepR1StarWordL w phase in
    let s2 := stepR1StarWordL w (r1_phase s1) in
    r1PhaseCfg phase l (npow (wordR (revWord w)) (2 * q)%N *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out s2 ++ r1_out s1)) q *> l)
      (R (k1 + 2 * (q * (r1_res s1 + r1_res s2)))%N).
Proof.
  induction q as [|q ih] using N_peano_ind; intros w phase l R hw halt hR k1 s1 s2.
  - cbn [N.mul npow Str_app]; replace (k1 + 0)%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    pose proof (hasRoundtrip_pow (2 * q)%N (revWord w) R Hrev hR) as hR2.
    pose proof (hasRoundtrip_word (revWord w) _ Hrev hR2) as hR1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w phase l _ hw hR1 k1)|].
    fold s1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w (r1_phase s1) (wordL (r1_out s1) *> l) _ hw hR2 (k1 + 2 * r1_res s1)%N)|].
    fold s2.
    fold s1 in halt; fold s2 in halt; rewrite halt.
    pose proof (ih w phase (wordL (r1_out s2 ++ r1_out s1) *> l) R hw halt hR
      (k1 + 2 * r1_res s1 + 2 * r1_res s2)%N) as Hih.
    cbn zeta in Hih; fold s1 in Hih; fold s2 in Hih.
    replace (k1 + 2 * r1_res s1 + 2 * r1_res s2 + 2 * (q * (r1_res s1 + r1_res s2)))%N
      with (k1 + 2 * ((q + 1) * (r1_res s1 + r1_res s2)))%N in Hih by lia.
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (r1_out s2 ++ r1_out s1)) q), Str_app_assoc.
    exact Hih.
Qed.

Fixpoint sweepStarLoop (rle : Rle) (phase : bool) (totalRes : N) (rs : Rle) : Rle * bool * N :=
  match rs with
  | [] => (rle, phase, totalRes)
  | (item, count) :: rest =>
    let s1 := stepR1StarWordL item phase in
    let out1 := r1_out s1 in
    let res1 := r1_res s1 in
    let nextPhase := r1_phase s1 in
    if Bool.eqb nextPhase phase then
      sweepStarLoop (pushRlePos out1 count rle) phase (totalRes + res1 * count)%N rest
    else
      let s2 := stepR1StarWordL item nextPhase in
      let out2 := r1_out s2 in
      let res2 := r1_res s2 in
      let q := N.div2 count in
      let rem := N.b2n (N.odd count) in
      let rle1 := pushRle (out2 ++ out1) q rle in
      let resAfterQ := (totalRes + (res1 + res2) * q)%N in
      if (rem =? 1)%N then
        sweepStarLoop (pushRlePos out1 1%N rle1) nextPhase (resAfterQ + res1)%N rest
      else
        sweepStarLoop rle1 phase resAfterQ rest
  end.

Lemma sweepStarLoop_sound : forall (rs : Rle) (rle : Rle) (phase : bool) (totalRes : N) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  forall (k1 : N),
    let res := sweepStarLoop rle phase totalRes rs in
    r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)%N)) -[ tm ]->*
    r1PhaseCfg (snd (fst res)) (evalRle (fst (fst res))) (R (k1 + 2 * snd res)%N).
Proof.
  induction rs as [|[item count] rest ih]; intros rle phase totalRes R hrs hR k1 res.
  - unfold res; cbn [sweepStarLoop evalRStack fst snd]; apply evstep_refl.
  - cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hitem hrest].
    assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact hitem).
    pose proof (hasRoundtrip_stack rest R hrest hR) as hR_rest.
    unfold res; cbn [sweepStarLoop evalRStack].
    set (s1 := stepR1StarWordL item phase).
    destruct (Bool.eqb (r1_phase s1) phase) eqn:Hsame.
    + apply Bool.eqb_prop in Hsame.
      eapply evstep_trans.
      * apply (stepR1Star_same_pow count item phase (evalRle rle) _ hitem Hsame hR_rest (k1 + 2 * totalRes)%N).
      * fold s1.
        replace (k1 + 2 * totalRes + 2 * (count * r1_res s1))%N
          with (k1 + 2 * (totalRes + r1_res s1 * count))%N by lia.
        rewrite <- evalRle_pushRlePos.
        apply (ih (pushRlePos (r1_out s1) count rle) phase (totalRes + r1_res s1 * count)%N R hrest hR k1).
    + assert (Hnot : r1_phase s1 = negb phase).
      { destruct (r1_phase s1), phase; cbn in Hsame; try discriminate; reflexivity. }
      assert (Halt : r1_phase (stepR1StarWordL item (r1_phase s1)) = phase).
      { rewrite Hnot, (stepR1StarWordL_phase_inv item phase hitem).
        fold s1; rewrite Hnot, Bool.negb_involutive; reflexivity. }
      set (s2 := stepR1StarWordL item (r1_phase s1)).
      cbn zeta.
      pose proof (N.div2_odd count) as Hdiv.
      set (q := N.div2 count) in *.
      set (rem := N.b2n (N.odd count)) in *.
      replace count with (2 * q + rem)%N at 1 by lia.
      rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
      pose proof (hasRoundtrip_pow rem (revWord item) _ Hrev hR_rest) as hR_rem.
      eapply evstep_trans.
      * apply (stepR1Star_alt_pow q item phase (evalRle rle) _ hitem Halt hR_rem (k1 + 2 * totalRes)%N).
      * fold s1; fold s2.
        rewrite <- evalRle_pushRle.
        replace (k1 + 2 * totalRes + 2 * (q * (r1_res s1 + r1_res s2)))%N
          with (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q))%N by lia.
        assert (Hrem : rem = 0%N \/ rem = 1%N) by (unfold rem; destruct (N.odd count); auto).
        destruct Hrem as [Hrem | Hrem]; rewrite Hrem; cbn [N.eqb Pos.eqb].
        -- rewrite npow_0; cbn [Str_app].
           apply (ih _ phase _ R hrest hR k1).
        -- rewrite npow_1.
           eapply evstep_trans.
           ++ apply (stepR1StarWordL_sound item phase _ _ hitem hR_rest
                (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q))%N).
           ++ fold s1.
              rewrite <- evalRle_pushRlePos_one.
              replace (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q) + 2 * r1_res s1)%N
                with (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q + r1_res s1))%N by lia.
              apply (ih _ (r1_phase s1) _ R hrest hR k1).
Qed.

Definition modeCfg (mode : Mode) (l r : side) : Q * tape :=
  match mode with
  | R0_mode => r0Cfg l r
  | R1_mode => r1Cfg l r
  | R1_ODD_mode => r1OddCfg l r
  end.

Definition stepOneTokPure (mode : Mode) (t : Tok) : option (list Tok * Mode) :=
  match mode, t with
  | R0_mode, Z_tok => Some ([Z_tok], R0_mode)
  | R0_mode, P_tok => Some ([P_tok], R0_mode)
  | R0_mode, PTTTM_TAIL_tok => Some ([Z_tok], R1_mode)
  | R1_mode, Z_tok => Some ([M_tok; Z_tok], R0_mode)
  | R1_mode, P_tok => Some ([P_tok], R1_ODD_mode)
  | R1_ODD_mode, Z_tok => Some ([Z_tok], R1_ODD_mode)
  | R1_ODD_mode, P_tok => Some ([Z_tok], R1_mode)
  | _, _ => None
  end.

Lemma stepOneTokPure_sound (mode mode' : Mode) (t : Tok) (toks : list Tok) (l r : side)
  (h : stepOneTokPure mode t = Some (toks, mode')) :
  modeCfg mode l (tokR t *> r) -[ tm ]->* modeCfg mode' (wordL toks *> l) r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg wordL app]; rewrite ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Fixpoint stepOneWordPureL (mode : Mode) (w : list Tok) : option (list Tok * Mode) :=
  match w with
  | [] => Some ([], mode)
  | t :: ts =>
    match stepOneWordPureL mode ts with
    | None => None
    | Some (outRest, mode1) =>
      match stepOneTokPure mode1 t with
      | None => None
      | Some (toks, mode2) => Some (toks ++ outRest, mode2)
      end
    end
  end.

Lemma stepOneWordPureL_sound : forall (w : list Tok) (mode mode' : Mode) (out : list Tok) (l r : side),
  stepOneWordPureL mode w = Some (out, mode') ->
  modeCfg mode l (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (wordL out *> l) r.
Proof.
  induction w as [|t ts ih]; intros mode mode' out l r h; cbn [stepOneWordPureL] in h.
  - inverts h; cbn [revWord wordR wordL Str_app]; apply evstep_refl.
  - destruct (stepOneWordPureL mode ts) as [[outRest mode1]|] eqn:H1; [|discriminate].
    destruct (stepOneTokPure mode1 t) as [[toks mode2]|] eqn:H2; [|discriminate].
    inverts h.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih mode mode1 outRest l (tokR t *> r) H1)|].
    eapply evstep_trans; [apply (stepOneTokPure_sound mode1 mode' t toks (wordL outRest *> l) r H2)|].
    rewrite wordL_append, Str_app_assoc. apply evstep_refl.
Qed.

Lemma stepOneWordPureL_same_pow : forall (c : N) (w out : list Tok) (mode : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) c *> r) -[ tm ]->*
  modeCfg mode (npow (wordL out) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w out mode l r h.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode out l _ h)|].
    rewrite (npow_succ_r (wordL out) c), Str_app_assoc.
    apply (ih w out mode _ r h).
Qed.

Lemma stepOneWordPureL_alt_pow : forall (q : N) (w out1 out2 : list Tok) (mode mode1 : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out1, mode1) ->
  stepOneWordPureL mode1 w = Some (out2, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) (2 * q)%N *> r) -[ tm ]->*
  modeCfg mode (npow (wordL (out2 ++ out1)) q *> l) r.
Proof.
  induction q as [|q ih] using N_peano_ind; intros w out1 out2 mode mode1 l r h1 h2.
  - cbn; apply evstep_refl.
  - replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode1 out1 l _ h1)|].
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode1 mode out2 (wordL out1 *> l) _ h2)|].
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (out2 ++ out1)) q), Str_app_assoc.
    apply (ih w out1 out2 mode mode1 _ r h1 h2).
Qed.

Definition stepOneTokL (rle : Rle) (mode : Mode) (t : Tok) : option (Rle * Mode) :=
  match mode, t with
  | R0_mode, Z_tok => Some (pushRlePos [Z_tok] 1%N rle, R0_mode)
  | R0_mode, P_tok => Some (pushRlePos [P_tok] 1%N rle, R0_mode)
  | R0_mode, PTTTM_TAIL_tok => Some (pushRlePos [Z_tok] 1%N rle, R1_mode)
  | R1_mode, Z_tok => Some (pushToksLtr [Z_tok; M_tok] rle, R0_mode)
  | R1_mode, P_tok => Some (pushRlePos [P_tok] 1%N rle, R1_ODD_mode)
  | R1_ODD_mode, Z_tok => Some (pushRlePos [Z_tok] 1%N rle, R1_ODD_mode)
  | R1_ODD_mode, P_tok => Some (pushRlePos [Z_tok] 1%N rle, R1_mode)
  | _, _ => None
  end.

Lemma stepOneTokL_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : side)
  (h : stepOneTokL rle mode t = Some (rle', mode')) :
  modeCfg mode (evalRle rle) (tokR t *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg]; rewrite ?evalRle_pushToksLtr, ?evalRle_pushRlePos_one;
  cbn [revWord wordL app]; rewrite ?app_nil_r, ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Fixpoint stepOneWordL (rle : Rle) (mode : Mode) (w : list Tok) : option (Rle * Mode) :=
  match w with
  | [] => Some (rle, mode)
  | t :: ts =>
    match stepOneWordL rle mode ts with
    | None => None
    | Some (rle1, mode1) => stepOneTokL rle1 mode1 t
    end
  end.

Lemma stepOneWordL_sound : forall (w : list Tok) (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneWordL rle mode w = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  induction w as [|t ts ih]; intros rle rle' mode mode' r h; cbn [stepOneWordL] in h.
  - inverts h; cbn [revWord wordR Str_app]; apply evstep_refl.
  - destruct (stepOneWordL rle mode ts) as [[rle1 mode1]|] eqn:H1; [|discriminate].
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih rle rle1 mode mode1 (tokR t *> r) H1)|].
    apply (stepOneTokL_sound rle1 rle' mode1 mode' t r h).
Qed.

Fixpoint stepOneBounceFuel (fuel : nat) (item : list Tok) (count : N) (rle : Rle) (mode : Mode)
  : option (Rle * Mode) :=
  match fuel with
  | O => if (count =? 0)%N then Some (rle, mode) else None
  | S fuel' =>
    if (count =? 0)%N then Some (rle, mode)
    else if modeEq mode R0_mode then
      if isZpWord item then Some (pushRlePos item count rle, R0_mode)
      else
        match stepOneWordL rle mode item with
        | None => None
        | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
        end
    else
      match stepOneWordPureL mode item with
      | None => None
      | Some (out1, mode1) =>
        if modeEq mode1 mode then
          Some (pushRlePos out1 count rle, mode)
        else if (2 <=? count)%N then
          match stepOneWordPureL mode1 item with
          | None => None
          | Some (out2, mode2) =>
            if modeEq mode2 mode then
              let q := N.div2 count in
              let rem := N.b2n (N.odd count) in
              stepOneBounceFuel fuel' item rem (pushRle (out2 ++ out1) q rle) mode
            else
              match stepOneWordL rle mode item with
              | None => None
              | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
              end
          end
        else
          match stepOneWordL rle mode item with
          | None => None
          | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
          end
      end
  end.

Lemma stepOneBounceFuel_sound : forall (fuel : nat) (item : list Tok) (count : N)
  (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneBounceFuel fuel item count rle mode = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (npow (wordR (revWord item)) count *> r) -[ tm ]->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction fuel as [|fuel ih]; intros item count rle rle' mode mode' r h; cbn [stepOneBounceFuel] in h.
  - destruct (count =? 0)%N eqn:Hc0; [|discriminate].
    apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
  - destruct (count =? 0)%N eqn:Hc0.
    + apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
    + apply N.eqb_neq in Hc0.
      assert (Hc_split : count = ((count - 1) + 1)%N) by lia.
      destruct (modeEq mode R0_mode) eqn:Hm0.
      * destruct (isZpWord item) eqn:Hzp.
        -- inverts h; apply modeEq_eq in Hm0; subst mode.
           cbn [modeCfg]; rewrite evalRle_pushRlePos.
           assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact Hzp).
           pose proof (r0_pow count (revWord item) (evalRle rle) r Hrev) as Hr0.
           rewrite revWord_revWord in Hr0; exact Hr0.
        -- destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
           rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
           eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
           exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
      * destruct (stepOneWordPureL mode item) as [[out1 mode1]|] eqn:Hp1; [|discriminate].
        destruct (modeEq mode1 mode) eqn:Hm1.
        -- inverts h; apply modeEq_eq in Hm1; subst mode1.
           rewrite evalRle_pushRlePos.
           exact (stepOneWordPureL_same_pow count item out1 mode' (evalRle rle) r Hp1).
        -- destruct (2 <=? count)%N eqn:Hle2.
           ++ destruct (stepOneWordPureL mode1 item) as [[out2 mode2]|] eqn:Hp2; [|discriminate].
              destruct (modeEq mode2 mode) eqn:Hm2.
              ** apply modeEq_eq in Hm2; subst mode2.
                 cbn zeta in h.
                 pose proof (N.div2_odd count) as Hdiv.
                 set (q := N.div2 count) in *.
                 set (rem := N.b2n (N.odd count)) in *.
                 replace count with (2 * q + rem)%N at 1 by lia.
                 rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordPureL_alt_pow q item out1 out2 mode mode1 (evalRle rle) _ Hp1 Hp2)|].
                 rewrite <- evalRle_pushRle.
                 exact (ih item rem (pushRle (out2 ++ out1) q rle) rle' mode mode' r h).
              ** destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
                 rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
                 exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
           ++ destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
              rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
              eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
              exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
Qed.

Local Opaque stepOneBounceFuel.

Fixpoint simpleOneBounceCarry (rle : Rle) (mode : Mode) (rs : Rle) (k1 : N) : option (Rle * N) :=
  match rs with
  | [] => if modeEq mode R0_mode then Some (rle, (k1 + 2)%N) else None
  | (item, count) :: rest =>
    match stepOneBounceFuel 3 item count rle mode with
    | None => None
    | Some (rle', mode') => simpleOneBounceCarry rle' mode' rest k1
    end
  end.

Lemma simpleOneBounceCarry_sound : forall (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : N),
  simpleOneBounceCarry rle mode rs k1 = Some (rle', kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rle') (evalWK kOut).
Proof.
  induction rs as [|[item count] rest ih]; intros rle rle' mode k1 kOut h; cbn [simpleOneBounceCarry] in h.
  - destruct (modeEq mode R0_mode) eqn:Hm; [|discriminate].
    inverts h; apply modeEq_eq in Hm; subst mode; cbn [modeCfg evalRStack].
    apply r0_end.
  - destruct (stepOneBounceFuel 3 item count rle mode) as [[rle1 mode1]|] eqn:Hb; [|discriminate].
    cbn [evalRStack].
    eapply evstep_trans; [apply (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ Hb)|].
    exact (ih rle1 rle' mode1 k1 kOut h).
Qed.

Definition hasSpecialWord (w : list Tok) : bool :=
  match w with
  | PTTTM_TAIL_tok :: _ => true
  | _ => false
  end.

Fixpoint hasSpecial (rs : Rle) : bool :=
  match rs with
  | [] => false
  | (it, _) :: rest => if hasSpecialWord it then true else hasSpecial rest
  end.

Definition runRightSweepStarCarry (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : option (Rle * N) :=
  if hasSpecial rStack then
    simpleOneBounceCarry rle mode rStack k1
  else if modeEq mode R0_mode then
    match copyRStack rle rStack with
    | None => None
    | Some rle' => Some (rle', (k1 + 2)%N)
    end
  else if allZpStack rStack then
    let initPhase := negb (modeEq mode R1_mode) in
    let res := sweepStarLoop rle initPhase 0%N rStack in
    let rle1 := fst (fst res) in
    let finalPhase := snd (fst res) in
    let totalRes := snd res in
    let kFinal1 := (k1 + 2 * totalRes)%N in
    if finalPhase then
      Some (stepZtToCarry (pushRlePos [Z_tok] 1%N rle1) kFinal1)
    else
      Some (stepZtToCarry (pushRlePos [P_tok] 1%N rle1) (kFinal1 + 1)%N)
  else None.

Lemma runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : N)
  (h : runRightSweepStarCarry rle mode rStack k1 = Some (rOut, kOut)) :
  modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rOut) (evalWK kOut).
Proof.
  unfold runRightSweepStarCarry in h.
  destruct (hasSpecial rStack) eqn:Hs.
  - exact (simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h).
  - destruct (modeEq mode R0_mode) eqn:Hm0.
    + destruct (copyRStack rle rStack) as [rle'|] eqn:Hc; [|discriminate].
      inverts h; apply modeEq_eq in Hm0; subst mode; cbn [modeCfg].
      eapply evstep_trans; [exact (proj2 (copyRStack_sound rStack rle rOut (evalWK k1) Hc))|].
      apply r0_end.
    + destruct (allZpStack rStack) eqn:Hall; [|discriminate].
      set (initPhase := negb (modeEq mode R1_mode)) in *.
      assert (Hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
        r1PhaseCfg initPhase (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0)%N))).
      { replace (k1 + 2 * 0)%N with k1 by lia.
        destruct mode; cbn in Hm0; try discriminate; reflexivity. }
      rewrite Hphase.
      pose proof (sweepStarLoop_sound rStack rle initPhase 0%N evalWK Hall hasRoundtrip_evalWK k1) as Hsw.
      cbn zeta in Hsw, h.
      set (res := sweepStarLoop rle initPhase 0%N rStack) in *.
      eapply evstep_trans; [exact Hsw|].
      destruct (snd (fst res)) eqn:Hfp.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1Odd_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [Z_tok] 1%N (fst (fst res))) (k1 + 2 * snd res)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [P_tok] 1%N (fst (fst res))) (k1 + 2 * snd res + 1)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
Qed.

Local Opaque runRightSweepStarCarry.

Inductive StepCarryRes :=
| SCR_halt
| SCR_next (rle : Rle) (k1 : N)
| SCR_err.

Definition StepCarryValid (cfg : Q * tape) (res : StepCarryRes) : Prop :=
  match res with
  | SCR_halt => exists cfg', (cfg -[ tm ]->* cfg') /\ halted tm cfg'
  | SCR_next rOut kOut => cfg -[ tm ]->* carryCfg (evalRle rOut) (evalWK kOut)
  | SCR_err => False
  end.

Lemma stepCarryValid_of_stepStar (cfg1 cfg2 : Q * tape) (res : StepCarryRes)
  (hstep : cfg1 -[ tm ]->* cfg2) (hval : StepCarryValid cfg2 res) :
  StepCarryValid cfg1 res.
Proof.
  destruct res; cbn [StepCarryValid] in *.
  - destruct hval as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact hstep | exact h2] | exact hhalt].
  - eapply evstep_trans; [exact hstep | exact hval].
  - exact hval.
Qed.

Definition finishTurn (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : StepCarryRes :=
  match runRightSweepStarCarry rle mode rStack k1 with
  | None => SCR_err
  | Some (rOut, kOut) => SCR_next rOut kOut
  end.

Lemma finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N)
  (hne : finishTurn rle mode rStack k1 <> SCR_err) :
  StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
    (finishTurn rle mode rStack k1).
Proof.
  unfold finishTurn in *.
  destruct (runRightSweepStarCarry rle mode rStack k1) as [[rOut kOut]|] eqn:Hr.
  - cbn [StepCarryValid].
    exact (runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut Hr).
  - exfalso; apply hne; reflexivity.
Qed.

Definition matchRule2 (t1 t2 : Tok) : option (list Tok * Mode) :=
  match t1, t2 with
  | M_tok, W_tok => Some ([T_tok], R1_mode)
  | M_tok, Z_tok => Some ([P_tok], R1_mode)
  | T_tok, Z_tok => Some ([T_tok; M_tok], R1_mode)
  | T_tok, P_tok => Some ([T_tok; P_tok], R0_mode)
  | _, _ => None
  end.

Lemma matchRule2_sound (t1 t2 : Tok) (out : list Tok) (mode : Mode) (r4 : Rle) (r : side)
  (h : matchRule2 t1 t2 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> evalRle r4) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r4)) r.
Proof.
  destruct t1, t2; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_WM.
  - apply turn_ZM.
  - apply turn_ZT.
  - apply turn_PT.
Qed.

Definition matchRule3 (t1 t2 t3 : Tok) : option (list Tok * Mode) :=
  match t1, t2, t3 with
  | U_tok, M_tok, Z_tok => Some ([T_tok; T_tok], R1_ODD_mode)
  | M_tok, T_tok, Z_tok => Some ([T_tok; M_tok; P_tok], R0_mode)
  | M_tok, T_tok, P_tok => Some ([T_tok; Z_tok], R1_mode)
  | W_tok, T_tok, Z_tok => Some ([T_tok; W_tok; Z_tok], R0_mode)
  | W_tok, T_tok, P_tok => Some ([M_tok; U_tok; Z_tok], R1_ODD_mode)
  | T_tok, T_tok, Z_tok => Some ([T_tok; W_tok; P_tok], R0_mode)
  | T_tok, T_tok, P_tok => Some ([M_tok; U_tok; Z_tok], R1_mode)
  | _, _, _ => None
  end.

Lemma matchRule3_sound (t1 t2 t3 : Tok) (out : list Tok) (mode : Mode) (r5 : Rle) (r : side)
  (h : matchRule3 t1 t2 t3 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r5)) r.
Proof.
  destruct t1, t2, t3; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMU.
  - apply turn_ZTM.
  - apply turn_PTM.
  - apply turn_ZTW.
  - apply turn_PTW.
  - apply turn_ZTT.
  - apply turn_PTT.
Qed.

Definition matchRule4 (t1 t2 t3 t4 : Tok) : option (list Tok * Mode) :=
  match t1, t2, t3, t4 with
  | U_tok, M_tok, P_tok, Z_tok => Some ([T_tok; W_tok; M_tok; P_tok], R0_mode)
  | M_tok, T_tok, T_tok, Z_tok => Some ([T_tok; W_tok; Z_tok], R1_mode)
  | M_tok, T_tok, T_tok, P_tok => Some ([M_tok; U_tok; Z_tok; P_tok], R0_mode)
  | W_tok, T_tok, U_tok, M_tok => Some ([T_tok; Z_tok], R1_ODD_mode)
  | W_tok, T_tok, T_tok, Z_tok => Some ([P_tok; Z_tok; Z_tok], R0_mode)
  | T_tok, M_tok, T_tok, P_tok => Some ([M_tok; U_tok; Z_tok; P_tok], R0_mode)
  | T_tok, T_tok, T_tok, Z_tok => Some ([P_tok; Z_tok; P_tok], R0_mode)
  | _, _, _, _ => None
  end.

Lemma matchRule4_sound (t1 t2 t3 t4 : Tok) (out : list Tok) (mode : Mode) (r6 : Rle) (r : side)
  (h : matchRule4 t1 t2 t3 t4 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> evalRle r6) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r6)) r.
Proof.
  destruct t1, t2, t3, t4; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZPMU.
  - apply turn_ZTTM.
  - apply turn_PTTM.
  - apply turn_MUTW.
  - apply turn_ZTTW.
  - apply turn_PTMT.
  - apply turn_ZTTT.
Qed.

Definition matchRule5 (t1 t2 t3 t4 t5 : Tok) : option (list Tok * Mode) :=
  match t1, t2, t3, t4, t5 with
  | M_tok, T_tok, U_tok, M_tok, Z_tok => Some ([P_tok; Z_tok; P_tok], R0_mode)
  | M_tok, T_tok, T_tok, T_tok, Z_tok => Some ([P_tok; Z_tok; Z_tok], R1_mode)
  | W_tok, T_tok, T_tok, T_tok, P_tok => Some ([T_tok; Z_tok; Z_tok; Z_tok], R0_mode)
  | _, _, _, _, _ => None
  end.

Lemma matchRule5_sound (t1 t2 t3 t4 t5 : Tok) (out : list Tok) (mode : Mode) (r7 : Rle) (r : side)
  (h : matchRule5 t1 t2 t3 t4 t5 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> tokL t5 *> evalRle r7) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r7)) r.
Proof.
  destruct t1, t2, t3, t4, t5; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMUTM.
  - apply turn_ZTTTM.
  - apply turn_PTTTW.
Qed.

Definition isEmptyRle (r : Rle) : bool :=
  match r with [] => true | _ => false end.

Lemma isEmptyRle_eq (r : Rle) : isEmptyRle r = true <-> r = [].
Proof. destruct r; cbn; intuition congruence. Qed.

Definition stepTurnFrom3 (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N) : StepCarryRes :=
  match matchRule3 t1 t2 t3 with
  | Some (out, mode) => finishTurn (pushToksLtr out r5) mode rStack k1
  | None =>
    match popLastTok r5 with
    | None => SCR_err
    | Some (t4, r6) =>
      match matchRule4 t1 t2 t3 t4 with
      | Some (out, mode) => finishTurn (pushToksLtr out r6) mode rStack k1
      | None =>
        match popLastTok r6 with
        | None => SCR_err
        | Some (t5, r7) =>
          match matchRule5 t1 t2 t3 t4 t5 with
          | Some (out, mode) => finishTurn (pushToksLtr out r7) mode rStack k1
          | None => SCR_err
          end
        end
      end
    end
  end.

Lemma stepTurnFrom3_sound (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom3 t1 t2 t3 r5 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom3 t1 t2 t3 r5 rStack k1).
Proof.
  unfold stepTurnFrom3 in *.
  destruct (matchRule3 t1 t2 t3) as [[out mode]|] eqn:Hm3.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule3_sound t1 t2 t3 out mode r5 _ Hm3)
      (finishTurn_sound (pushToksLtr out r5) mode rStack k1 hne)).
  - destruct (popLastTok r5) as [[t4 r6]|] eqn:Hp4; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r5 t4 r6 Hp4).
    destruct (matchRule4 t1 t2 t3 t4) as [[out mode]|] eqn:Hm4.
    + exact (stepCarryValid_of_stepStar _ _ _
        (matchRule4_sound t1 t2 t3 t4 out mode r6 _ Hm4)
        (finishTurn_sound (pushToksLtr out r6) mode rStack k1 hne)).
    + destruct (popLastTok r6) as [[t5 r7]|] eqn:Hp5; [|exfalso; apply hne; reflexivity].
      rewrite (popLastTok_sound r6 t5 r7 Hp5).
      destruct (matchRule5 t1 t2 t3 t4 t5) as [[out mode]|] eqn:Hm5; [|exfalso; apply hne; reflexivity].
      exact (stepCarryValid_of_stepStar _ _ _
        (matchRule5_sound t1 t2 t3 t4 t5 out mode r7 _ Hm5)
        (finishTurn_sound (pushToksLtr out r7) mode rStack k1 hne)).
Qed.

Definition stepTurnFrom2 (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N) : StepCarryRes :=
  match matchRule2 t1 t2 with
  | Some (out, mode) => finishTurn (pushToksLtr out r4) mode rStack k1
  | None =>
    match popLastTok r4 with
    | None => SCR_err
    | Some (t3, r5) =>
      if tokEq t1 T_tok then
        if tokEq t2 M_tok then
          if tokEq t3 U_tok then SCR_err
          else stepTurnFrom3 t1 t2 t3 r5 rStack k1
        else stepTurnFrom3 t1 t2 t3 r5 rStack k1
      else if tokEq t1 U_tok then
        if tokEq t2 T_tok then
          if tokEq t3 Z_tok then SCR_halt
          else stepTurnFrom3 t1 t2 t3 r5 rStack k1
        else stepTurnFrom3 t1 t2 t3 r5 rStack k1
      else stepTurnFrom3 t1 t2 t3 r5 rStack k1
    end
  end.

Lemma stepTurnFrom2_sound (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom2 t1 t2 r4 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> evalRle r4) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom2 t1 t2 r4 rStack k1).
Proof.
  unfold stepTurnFrom2 in *.
  destruct (matchRule2 t1 t2) as [[out mode]|] eqn:Hm2.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule2_sound t1 t2 out mode r4 _ Hm2)
      (finishTurn_sound (pushToksLtr out r4) mode rStack k1 hne)).
  - destruct (popLastTok r4) as [[t3 r5]|] eqn:Hp3; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r4 t3 r5 Hp3).
    destruct (tokEq t1 T_tok) eqn:Ht1.
    + destruct (tokEq t2 M_tok) eqn:Hm2'.
      * destruct (tokEq t3 U_tok) eqn:Hu3.
        -- exfalso; apply hne; reflexivity.
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
    + destruct (tokEq t1 U_tok) eqn:Hu1.
      * destruct (tokEq t2 T_tok) eqn:Ht2.
        -- destruct (tokEq t3 Z_tok) eqn:Hz3.
           ++ apply tokEq_eq in Hu1; apply tokEq_eq in Ht2; apply tokEq_eq in Hz3.
              subst t1 t2 t3.
              cbn [StepCarryValid].
              eexists; split; [apply turn_ZTU_halt | reflexivity].
           ++ exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
Qed.

Definition stepTurnaround (r2 rStack : Rle) (k1 : N) : StepCarryRes :=
  match popLastTok r2 with
  | None => SCR_err
  | Some (t1, r3) =>
    match popLastTok r3 with
    | None => SCR_err
    | Some (t2, r4) =>
      if tokEq t1 M_tok then
        if tokEq t2 U_tok then SCR_err
        else stepTurnFrom2 t1 t2 r4 rStack k1
      else stepTurnFrom2 t1 t2 r4 rStack k1
    end
  end.

Lemma stepTurnaround_sound (r2 rStack : Rle) (k1 : N)
  (hne : stepTurnaround r2 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (stepTurnaround r2 rStack k1).
Proof.
  unfold stepTurnaround in *.
  destruct (popLastTok r2) as [[t1 r3]|] eqn:Hp1; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r2 t1 r3 Hp1).
  destruct (popLastTok r3) as [[t2 r4]|] eqn:Hp2; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r3 t2 r4 Hp2).
  destruct (tokEq t1 M_tok) eqn:Hm1.
  - destruct (tokEq t2 U_tok) eqn:Hu2.
    + exfalso; apply hne; reflexivity.
    + exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
  - exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
Qed.

Local Opaque stepTurnaround.

Lemma special_ZTM_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL M_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL M_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTM.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTM|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_PT_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL T_tok *> npow (tokL P_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_PT.
  - rewrite (npow_succ_l (tokL P_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_PT|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_ZTW_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL W_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) (n + 1)%N *> tokL W_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTW.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTW|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_Z|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_Z R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_Z|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL Z_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Definition stepSpecialLoops (r2 rStack : Rle) (k1 : N) : option StepCarryRes :=
  match popLastTok r2 with
  | None => None
  | Some (t1, r2a) =>
    match t1 with
    | U_tok =>
      match popTok M_tok r2a with
      | None => None
      | Some rest =>
        let '(mVal, r3) := popTokCount 8 P_tok 0%N rest in
        if (mVal =? 0)%N then None
        else
          match popTok Z_tok r3 with
          | None => Some SCR_err
          | Some r4 =>
            let r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4)) in
            Some (finishTurn r5 R0_mode rStack k1)
          end
      end
    | M_tok =>
      match popTok T_tok r2a with
      | None => None
      | Some rest =>
        let '(b, r3) := popTokCount 8 Z_tok 0%N rest in
        if (b =? 0)%N then None
        else
          let r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3) in
          match copyRStack r3' rStack with
          | None => Some SCR_err
          | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
          end
      end
    | W_tok =>
      match popTok T_tok r2a with
      | None => None
      | Some rest =>
        let '(b, r3) := popTokCount 8 Z_tok 0%N rest in
        if (b =? 0)%N then None
        else
          let r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3) in
          match copyRStack r3' rStack with
          | None => Some SCR_err
          | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
          end
      end
    | T_tok =>
      let '(b, r3) := popTokCount 8 P_tok 0%N r2a in
      if (b =? 0)%N then None
      else
        let r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3) in
        match copyRStack r3' rStack with
        | None => Some SCR_err
        | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
        end
    | _ => None
    end
  end.

Lemma stepSpecialLoops_sound (r2 rStack : Rle) (k1 : N) (res : StepCarryRes)
  (h : stepSpecialLoops r2 rStack k1 = Some res) (hne : res <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res.
Proof.
  unfold stepSpecialLoops in h.
  destruct (popLastTok r2) as [[t1 r2a]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound r2 t1 r2a Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popTok M_tok r2a) as [rest|] eqn:Hpm; [|discriminate].
    rewrite (popTok_sound M_tok r2a rest Hpm).
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N rest) as [mVal r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
    apply N.eqb_neq in Hm0.
    destruct (popTok Z_tok r3) as [r4|] eqn:Hpz; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h.
    rewrite Hcnt, (popTok_sound Z_tok r3 r4 Hpz).
    eapply stepCarryValid_of_stepStar; [apply carry_MU_to_pmuCfg|].
    eapply stepCarryValid_of_stepStar; [apply (pmu_loop mVal (tokL Z_tok *> evalRle r4))|].
    replace mVal with (1 + (mVal - 1))%N at 1 by lia.
    rewrite (npow_add (tokR Z_tok) 1%N (mVal - 1)%N), npow_1, Str_app_assoc.
    eapply stepCarryValid_of_stepStar; [apply pmuCfg_Z_turn|].
    eapply stepCarryValid_of_stepStar; [apply (r0_Z_loop (mVal - 1)%N)|].
    eapply stepCarryValid_of_stepStar; [apply r0_P|].
    set (r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4))) in *.
    assert (Hr5 : tokL P_tok *> npow (tokL Z_tok) (mVal - 1)%N *> tokL M_tok *> tokL W_tok *> tokL T_tok *> evalRle r4 = evalRle r5).
    { unfold r5; rewrite evalRle_pushRlePos_one, evalRle_pushRle, evalRle_pushToksLtr.
      cbn [revWord wordL app]; rewrite app_nil_r, !Str_app_assoc; reflexivity. }
    rewrite Hr5.
    exact (finishTurn_sound r5 R0_mode rStack k1 hne).
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTM_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTW_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2a)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N r2a) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_PT_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushRlePos_one in Hcopy;
    cbn [wordL app] in Hcopy; rewrite app_nil_r in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
Qed.

Local Opaque stepSpecialLoops.

Definition stepCarry (rle : Rle) (k1 : N) : StepCarryRes :=
  let '(r2, rStack) := popCarryLoop 80 rle [] in
  if hasSpecial rStack then
    stepTurnaround r2 rStack k1
  else
    match stepSpecialLoops r2 rStack k1 with
    | None => stepTurnaround r2 rStack k1
    | Some res => res
    end.

Lemma stepCarry_sound (rle : Rle) (k1 : N) (hne : stepCarry rle k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarry rle k1).
Proof.
  pose proof (popCarryLoop_sound 80 rle [] (evalWK k1)) as Hp.
  cbn [evalRStack] in Hp.
  unfold stepCarry in *.
  destruct (popCarryLoop 80 rle []) as [r2 rStack] eqn:Hpop.
  cbn [fst snd] in Hp.
  eapply stepCarryValid_of_stepStar; [exact Hp|].
  destruct (hasSpecial rStack) eqn:Hns.
  - exact (stepTurnaround_sound r2 rStack k1 hne).
  - destruct (stepSpecialLoops r2 rStack k1) as [res|] eqn:Hsl.
    + exact (stepSpecialLoops_sound r2 rStack k1 res Hsl hne).
    + exact (stepTurnaround_sound r2 rStack k1 hne).
Qed.

Local Opaque stepCarry.

Fixpoint runCarryChunk (n : nat) (rle : Rle) (k1 : N) : StepCarryRes :=
  match n with
  | O => SCR_next rle k1
  | S n' =>
    match stepCarry rle k1 with
    | SCR_halt => SCR_halt
    | SCR_next rle' k1' => runCarryChunk n' rle' k1'
    | SCR_err => SCR_err
    end
  end.

Lemma runCarryChunk_sound : forall (n : nat) (rle : Rle) (k1 : N),
  runCarryChunk n rle k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (runCarryChunk n rle k1).
Proof.
  induction n as [|n ih]; intros rle k1 hne; cbn [runCarryChunk] in *.
  - cbn [StepCarryValid]; apply evstep_refl.
  - destruct (stepCarry rle k1) as [|rle' k1'|] eqn:Hs.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; exact Hv.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; cbn [StepCarryValid] in Hv.
      exact (stepCarryValid_of_stepStar _ _ _ Hv (ih rle' k1' hne)).
    + exfalso; apply hne; reflexivity.
Qed.

End GeneralizedRle.

Fixpoint takeRle (n : nat) (rle : Rle) : Rle :=
  match n, rle with
  | O, _ => []
  | S _, [] => []
  | S n', h :: t => h :: takeRle n' t
  end.

Fixpoint dropRle (n : nat) (rle : Rle) : Rle :=
  match n, rle with
  | O, _ => rle
  | S _, [] => []
  | S n', _ :: t => dropRle n' t
  end.

Lemma evalRleG_take_drop : forall (k : nat) (rle : Rle) (l_end : side),
  evalRleG l_end rle = evalRleG (evalRleG l_end (dropRle k rle)) (takeRle k rle).
Proof.
  induction k as [|k ih]; intros rle l_end; [reflexivity|].
  destruct rle as [|[w c] t]; [reflexivity|].
  cbn [evalRleG takeRle dropRle].
  rewrite (ih t l_end). reflexivity.
Qed.

Fixpoint runCarrySchedule (sched : list N) (k : nat) (rle : Rle) (k1 : N) : bool :=
  match sched with
  | [] => false
  | n :: rest =>
    match runCarryChunk (N.to_nat n) rle k1 with
    | SCR_halt => true
    | SCR_next rle' k1' => runCarrySchedule rest k (takeRle k rle') k1'
    | SCR_err => false
    end
  end.

Lemma runCarrySchedule_sound : forall (sched : list N) (k : nat) (rle : Rle) (k1 : N) (l_end : side),
  runCarrySchedule sched k rle k1 = true ->
  exists cfg', (carryCfg (evalRleG l_end rle) (evalWK k1) -[ tm ]->* cfg') /\ halted tm cfg'.
Proof.
  induction sched as [|n rest ih]; intros k rle k1 l_end h; cbn [runCarrySchedule] in h; [discriminate|].
  destruct (runCarryChunk (N.to_nat n) rle k1) as [|rle' k1'|] eqn:Hc; [| |discriminate].
  - pose proof (runCarryChunk_sound l_end (N.to_nat n) rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv; exact Hv.
  - pose proof (runCarryChunk_sound l_end (N.to_nat n) rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv.
    rewrite (evalRleG_take_drop k rle' l_end) in Hv.
    destruct (ih k (takeRle k rle') k1' (evalRleG l_end (dropRle k rle')) h) as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact Hv | exact h2] | exact hhalt].
Qed.

Local Transparent pushRlePos pushRle popTokCount stepZtToCarry
  popCarrySpecial popCarryLoop stepOneBounceFuel runRightSweepStarCarry
  stepTurnaround stepSpecialLoops stepCarry.

Definition ckptRle_0 : Rle :=
  [([Z_tok], 6%N); ([M_tok], 1%N); ([T_tok], 1%N); ([Z_tok], 4%N); ([P_tok], 5%N); ([Z_tok], 1%N); ([U_tok], 1%N)].

Definition ckpt0_ccfg : CCfg :=
  mkCCfg B 1%sym
    [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1]%sym
    [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym.

Lemma init_to_ckpt0 :
  c0 -[ tm ]->* carryCfg (evalRleG 0inf ckptRle_0) (evalWK 1%N).
Proof.
  exact (bmultiStep_sound tm (N.to_nat 8428%N)
    (mkCCfg A 0%sym []%sym []%sym)
    ckpt0_ccfg
    ltac:(vm_cast_no_check (eq_refl (Some ckpt0_ccfg)))).
Qed.

Definition carry_sched : list N := [3746; 3999; 4000; 4000; 4000; 4000; 4000; 3298]%N.

Lemma runCarrySchedule_ok : runCarrySchedule carry_sched 30%nat ckptRle_0 1%N = true.
Proof.
  vm_cast_no_check (eq_refl true).
Qed.

Theorem halt: halts tm c0.
Proof.
  destruct (runCarrySchedule_sound carry_sched 30%nat ckptRle_0 1%N 0inf runCarrySchedule_ok)
    as [cfg' [Hsteps Hhalted]].
  eapply halts_evstep.
  - exact (halted_halts tm cfg' Hhalted).
  - eapply evstep_trans; [exact init_to_ckpt0 | exact Hsteps].
Qed.

End TM1.
Print Assumptions TM1.halt.



Module TM2.
Import BusyCoq.Individual62.

Import Bool List Streams PeanoNat Lia NArith ZArith String.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB1LD_1RA0RF_1RA---").

Open Scope list_scope.

Notation N_peano_ind := TM1.N_peano_ind.

Notation npow := TM1.npow.

Notation npow_0 := TM1.npow_0.

Notation npow_1 := TM1.npow_1.

Notation npow_add := TM1.npow_add.

Notation npow_2 := TM1.npow_2.

Notation npow_3 := TM1.npow_3.

Notation npow_succ_l := TM1.npow_succ_l.

Notation npow_succ_r := TM1.npow_succ_r.

Notation zero_cons_0inf := TM1.zero_cons_0inf.

Notation CCfg := TM1.CCfg.

Notation mkCCfg := TM1.mkCCfg.

Notation cc_q := TM1.cc_q.

Notation cc_cur := TM1.cc_cur.

Notation cc_l := TM1.cc_l.

Notation cc_r := TM1.cc_r.

Notation sym_eqb := TM1.sym_eqb.

Notation sym_eqb_eq := TM1.sym_eqb_eq.

Notation is_nil_sym := TM1.is_nil_sym.

Notation evalWindow := TM1.evalWindow.

Notation evalCCfg := TM1.evalCCfg.

Notation evalRCCfg := TM1.evalRCCfg.

Notation evalBCfg := TM1.evalBCfg.

Notation wstep := TM1.wstep.

Notation wstep_sound := TM1.wstep_sound.

Notation wmultiStep := TM1.wmultiStep.

Notation wmultiStep_sound := TM1.wmultiStep_sound.

Notation cstep := TM1.cstep.

Notation cstep_sound := TM1.cstep_sound.

Notation cmultiStep := TM1.cmultiStep.

Notation cmultiStep_sound := TM1.cmultiStep_sound.

Notation rcstep := TM1.rcstep.

Notation rcstep_sound := TM1.rcstep_sound.

Notation rcmultiStep := TM1.rcmultiStep.

Notation rcmultiStep_sound := TM1.rcmultiStep_sound.

Notation bstep := TM1.bstep.

Notation bstep_sound := TM1.bstep_sound.

Notation bmultiStep := TM1.bmultiStep.

Notation bmultiStep_sound := TM1.bmultiStep_sound.

Notation Tok := TM1.Tok.

Notation U_tok := TM1.U_tok.

Notation M_tok := TM1.M_tok.

Notation W_tok := TM1.W_tok.

Notation Z_tok := TM1.Z_tok.

Notation T_tok := TM1.T_tok.

Notation P_tok := TM1.P_tok.

Notation PTTTM_TAIL_tok := TM1.PTTTM_TAIL_tok.

Notation Mode := TM1.Mode.

Notation R0_mode := TM1.R0_mode.

Notation R1_mode := TM1.R1_mode.

Notation R1_ODD_mode := TM1.R1_ODD_mode.

Notation Rle := TM1.Rle.

Notation tokEq := TM1.tokEq.

Notation tokEq_eq := TM1.tokEq_eq.

Notation modeEq := TM1.modeEq.

Notation modeEq_eq := TM1.modeEq_eq.

Notation wordEq := TM1.wordEq.

Notation wordEq_eq := TM1.wordEq_eq.

Notation isZpTok := TM1.isZpTok.

Notation isZpWord := TM1.isZpWord.

Notation revWord := TM1.revWord.

Notation revWord_append := TM1.revWord_append.

Notation revWord_revWord := TM1.revWord_revWord.

Notation isZpWord_append := TM1.isZpWord_append.

Notation isZpWord_revWord := TM1.isZpWord_revWord.

Notation tokL := TM1.tokL.

Notation tokR := TM1.tokR.

Notation wordL := TM1.wordL.

Notation wordR := TM1.wordR.

Notation wordL_append := TM1.wordL_append.

Notation wordR_append := TM1.wordR_append.

Notation evalRleG := TM1.evalRleG.

Section GeneralizedRle.

Variable l_end : side.

Local Notation evalRle := (evalRleG l_end).

Notation evalRStack := TM1.evalRStack.

Notation pushRlePos := TM1.pushRlePos.

Notation pushRle := TM1.pushRle.

Local Notation evalRle_pushRlePos := (TM1.evalRle_pushRlePos l_end).

Local Notation evalRle_pushRle := (TM1.evalRle_pushRle l_end).

Local Notation evalRle_pushRlePos_one := (TM1.evalRle_pushRlePos_one l_end).

Notation evalRStack_pushRlePos := TM1.evalRStack_pushRlePos.

Notation evalRStack_pushRle := TM1.evalRStack_pushRle.

Local Opaque pushRlePos pushRle.

Notation pushToksLtr := TM1.pushToksLtr.

Local Notation evalRle_pushToksLtr := (TM1.evalRle_pushToksLtr l_end).

Notation popLastTok := TM1.popLastTok.

Local Notation popLastTok_sound := (TM1.popLastTok_sound l_end).

Notation popTok := TM1.popTok.

Local Notation popTok_sound := (TM1.popTok_sound l_end).

Notation popToks := TM1.popToks.

Local Notation popToks_sound := (TM1.popToks_sound l_end).

Notation popTokCount := TM1.popTokCount.

Local Notation popTokCount_sound := (TM1.popTokCount_sound l_end).

Local Opaque popTokCount.

Notation evalWK := TM1.evalWK.

Notation cfgR := TM1.cfgR.

Notation carryCfg := TM1.carryCfg.

Notation r0Cfg := TM1.r0Cfg.

Notation r1Cfg := TM1.r1Cfg.

Notation r1OddShortCfg := TM1.r1OddShortCfg.

Notation r1OddCfg := TM1.r1OddCfg.

Notation wSweepCfg := TM1.wSweepCfg.

Notation dSweepCfg := TM1.dSweepCfg.

Notation tSweepCfg := TM1.tSweepCfg.

Notation t3Cfg := TM1.t3Cfg.

Notation pmuCfg := TM1.pmuCfg.

Ltac solve_wstep n c1 c2 l r :=
  exact (wmultiStep_sound tm n c1 c2 l r ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Ltac solve_cstep n c1 c2 r :=
  exact (cmultiStep_sound tm n c1 c2 r ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Ltac solve_rcstep n c1 c2 l :=
  exact (rcmultiStep_sound tm n c1 c2 l ltac:(vm_cast_no_check (eq_refl (Some c2)))).

Lemma carry_Z (l r : side) :
  carryCfg (tokL Z_tok *> l) r -[ tm ]->* carryCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 46
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_P (l r : side) :
  carryCfg (tokL P_tok *> l) r -[ tm ]->* carryCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 16
    (mkCCfg B 1%sym [0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 68
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTW (l r : side) :
  carryCfg (tokL W_tok *> npow (tokL T_tok) 2%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 3%N *> r).
Proof.
  solve_wstep 102
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTT (l r : side) :
  carryCfg (npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 72
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTTM (l r : side) :
  carryCfg (tokL M_tok *> npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR PTTTM_TAIL_tok *> r).
Proof.
  solve_wstep 85
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_UM (r : side) :
  carryCfg (tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 53
    (mkCCfg B 1%sym [0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_UMT (r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 83
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_ZT (l r : side) :
  carryCfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 53
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_WM (l r : side) :
  carryCfg (tokL M_tok *> tokL W_tok *> l) r -[ tm ]->*
  r1Cfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 47
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PT (l r : side) :
  carryCfg (tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 97
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZM (l r : side) :
  carryCfg (tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 47
    (mkCCfg B 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 119
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 83
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 87
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL T_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 93
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 103
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 105
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 105
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_MUTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 119
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 91
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZPMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL P_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 135
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 133
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 173
    (mkCCfg B 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma carry_MU_to_pmuCfg (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 15
    (mkCCfg B 1%sym [0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmu_step (l r : side) :
  pmuCfg (tokL P_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 50
    (mkCCfg D 1%sym [0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_Z_turn (l r : side) :
  pmuCfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->*
  r0Cfg (tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 30
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma pmuCfg_M_to_carry (l r : side) :
  pmuCfg (tokL M_tok *> l) r -[ tm ]->*
  carryCfg (tokL U_tok *> l) r.
Proof.
  solve_wstep 5
    (mkCCfg D 1%sym [0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_T_to_carry (l r : side) :
  pmuCfg (tokL T_tok *> l) r -[ tm ]->*
  carryCfg (tokL M_tok *> l) r.
Proof.
  solve_wstep 5
    (mkCCfg D 1%sym [0; 1; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTU (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg (tokL Z_tok *> l) (tokR P_tok *> r).
Proof.
  solve_wstep 24
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_PTMT (l r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 123
    (mkCCfg B 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTU_halt (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  (F, ([0; 0; 1; 1; 0; 1; 1; 1]%sym *> l, 1%sym, [0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).
Proof.
  solve_wstep 26
    (mkCCfg B 1%sym [0; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg F 1%sym [0; 0; 1; 1; 0; 1; 1; 1]%sym [0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma r0_Z (l r : side) :
  r0Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_P (l r : side) :
  r0Cfg l (tokR P_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 40
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_PTTTM_TAIL (l r : side) :
  r0Cfg l (tokR PTTTM_TAIL_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 13
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_Z (l r : side) :
  r1Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_P (l r : side) :
  r1Cfg l (tokR P_tok *> r) -[ tm ]->* r1OddCfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 58
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShort_Z (l r : side) :
  r1OddShortCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddShortCfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_P (l r : side) :
  r1OddCfg l (tokR P_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 8
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_start (l : side) :
  cfgR l -[ tm ]->* wSweepCfg l 0inf.
Proof.
  solve_rcstep 2
    (mkCCfg B 0%sym [1; 1]%sym []%sym)
    (mkCCfg D 1%sym []%sym [1]%sym) l.
Qed.

Lemma wSweep_step (l r : side) :
  wSweepCfg (tokL W_tok *> l) r -[ tm ]->* wSweepCfg l ([0; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 4
    (mkCCfg D 1%sym [0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg D 1%sym []%sym [1; 0; 0; 1; 1]%sym) l r.
Qed.

Lemma dSweep_step (l r : side) :
  dSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL W_tok *> l) r.
Proof.
  solve_wstep 4
    (mkCCfg E 1%sym [0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma dSweep_end (l : side) :
  dSweepCfg l 0inf -[ tm ]->* cfgR (tokL W_tok *> l).
Proof.
  solve_rcstep 3
    (mkCCfg E 1%sym [0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma tSweep_step (l r : side) :
  tSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 20
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma tSweep_end (l : side) :
  tSweepCfg l 0inf -[ tm ]->* cfgR (tokL Z_tok *> l).
Proof.
  solve_rcstep 2
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma r0_to_dSweep (l r : side) :
  r0Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_to_dSweep (l r : side) :
  r1Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_to_tSweep (l r : side) :
  r1OddCfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 8
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_Z_to_dSweep (l r : side) :
  wSweepCfg (tokL Z_tok *> l) r -[ tm ]->* dSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 9
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_ZT_to_dSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  dSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 45
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_PT_to_carry (l r : side) :
  wSweepCfg (tokL T_tok *> tokL P_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  carryCfg l ([1; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 34
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1]%sym) l r.
Qed.

Lemma wSweep_ZMT_to_tSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  tSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 65
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma cfgR_Z_to_TW (l : side) :
  cfgR (tokL Z_tok *> l) -[ tm ]->* cfgR (tokL W_tok *> tokL T_tok *> l).
Proof.
  solve_rcstep 14
    (mkCCfg B 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l.
Qed.

Lemma cfgR_TW_to_t3Cfg (l : side) :
  cfgR (tokL W_tok *> tokL T_tok *> l) -[ tm ]->* t3Cfg l (evalWK 0%N).
Proof.
  solve_rcstep 24
    (mkCCfg B 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym) l.
Qed.

Lemma t3_step (l r : side) :
  t3Cfg (npow (tokL T_tok) 3%N *> l) r -[ tm ]->* t3Cfg l (npow (tokR Z_tok) 2%N *> r).
Proof.
  solve_wstep 56
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma t3Cfg_Z_zero_to_carry (l : side) :
  t3Cfg (tokL Z_tok *> l) (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 96
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_Z_succ_to_r0 (l r : side) :
  t3Cfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 31
    (mkCCfg B 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma t3Cfg_TZ_to_r1OddShort (l r : side) :
  t3Cfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->* r1OddShortCfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 45
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShortCfg_evalWK0_to_carry (l : side) :
  r1OddShortCfg l (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 144
    (mkCCfg B 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg B 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_TTZ_to_r0 (l r : side) :
  t3Cfg (npow (tokL T_tok) 2%N *> tokL Z_tok *> l) r -[ tm ]->* r0Cfg (tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 65
    (mkCCfg B 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_Z (l r : side) :
  r1OddCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddCfg (tokL Z_tok *> l) r.
Proof.
  exact (r1OddShort_Z (tokL Z_tok *> l) r).
Qed.

Lemma wSweep_loop : forall (n : N) (l r : side),
  wSweepCfg (npow (tokL W_tok) n *> l) r -[ tm ]->*
  wSweepCfg l (npow [0; 0; 1; 1]%sym n *> r).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply wSweep_step|].
    rewrite (npow_succ_r [0; 0; 1; 1]%sym n), Str_app_assoc.
    apply ih.
Qed.

Lemma dSweep_loop : forall (n : N) (l r : side),
  dSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  dSweepCfg (npow (tokL W_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply dSweep_step|].
    rewrite (npow_succ_r (tokL W_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma tSweep_loop : forall (n : N) (l r : side),
  tSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  tSweepCfg (npow (tokL T_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply tSweep_step|].
    rewrite (npow_succ_r (tokL T_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma t3_loop : forall (q : N) (l r : side),
  t3Cfg (npow (tokL T_tok) (3 * q)%N *> l) r -[ tm ]->*
  t3Cfg l (npow (tokR Z_tok) (2 * q)%N *> r).
Proof.
  induction q as [|q ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - replace (3 * (q + 1))%N with (3 + 3 * q)%N by lia.
    replace (2 * (q + 1))%N with (2 * q + 2)%N by lia.
    rewrite (npow_add (tokL T_tok) 3%N (3 * q)%N), Str_app_assoc.
    eapply evstep_trans; [apply t3_step|].
    rewrite (npow_add (tokR Z_tok) (2 * q)%N 2%N), Str_app_assoc.
    apply ih.
Qed.

Lemma pmu_loop : forall (m : N) (l r : side),
  pmuCfg (npow (tokL P_tok) m *> l) r -[ tm ]->*
  pmuCfg l (npow (tokR Z_tok) m *> r).
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply pmu_step|].
    rewrite (npow_succ_r (tokR Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_Z_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_P_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR P_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_P|].
    rewrite (npow_succ_r (tokL P_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r1OddShort_Z_loop : forall (m : N) (l r : side),
  r1OddShortCfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r1OddShortCfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r1OddShort_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma cfgR_ZW_to_TW (n : N) (l : side) :
  cfgR (npow (tokL W_tok) n *> tokL Z_tok *> l) -[ tm ]->*
  cfgR (npow (tokL W_tok) (n + 1)%N *> tokL T_tok *> l).
Proof.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop n (tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply wSweep_Z_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop n (tokL T_tok *> l) 0inf)|].
  rewrite npow_succ_l, Str_app_assoc.
  apply dSweep_end.
Qed.

Lemma r0_end (k1 : N) (l : side) :
  r0Cfg l (evalWK k1) -[ tm ]->* carryCfg l (evalWK (k1 + 2)%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r0_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop k1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 1)%N (tokL Z_tok *> l))|].
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 2)%N (tokL T_tok *> tokL Z_tok *> l) 0inf)|].
  replace (k1 + 2)%N with ((k1 + 1) + 1)%N at 1 by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZT_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop (k1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 2)%N (tokL P_tok *> l))|].
  replace (k1 + 2 + 1)%N with (k1 + 3)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 3)%N (tokL T_tok *> tokL P_tok *> l) 0inf)|].
  replace (k1 + 3)%N with ((k1 + 2) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 2)%N), Str_app_assoc.
  unfold evalWK; apply wSweep_PT_to_carry.
Qed.

Lemma r1_end (kf1 : N) (l : side) :
  r1Cfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) (kf1 + 1)%N *> tokL Z_tok *> tokL P_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop kf1 (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (kf1 + 1)%N (tokL M_tok *> tokL Z_tok *> l))|].
  replace (kf1 + 1 + 1)%N with (kf1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (kf1 + 2)%N (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  replace (kf1 + 2)%N with ((kf1 + 1) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (kf1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZMT_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop (kf1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Lemma r1Odd_end (kf1 : N) (l : side) :
  r1OddCfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) kf1 *> tokL Z_tok *> tokL Z_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1Odd_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop kf1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Notation stepZtToCarry := TM1.stepZtToCarry.

Lemma stepZtToCarry_sound (rle2 : Rle) (n : N) :
  t3Cfg (npow (tokL T_tok) n *> tokL Z_tok *> evalRle rle2) (evalWK 0%N) -[ tm ]->*
  carryCfg (evalRle (fst (stepZtToCarry rle2 n))) (evalWK (snd (stepZtToCarry rle2 n))).
Proof.
  unfold stepZtToCarry; cbn zeta.
  fold (N.div n 3%N) (N.modulo n 3%N).
  pose proof (N.div_mod n 3 ltac:(discriminate)) as Hdiv.
  pose proof (N.mod_upper_bound n 3 ltac:(discriminate)) as Hmod.
  set (q := (n / 3)%N) in *.
  set (rem := (n mod 3)%N) in *.
  replace n with (3 * q + rem)%N at 1 by lia.
  rewrite (npow_add (tokL T_tok) (3 * q)%N rem), Str_app_assoc.
  eapply evstep_trans; [apply (t3_loop q (npow (tokL T_tok) rem *> tokL Z_tok *> evalRle rle2) (evalWK 0%N))|].
  assert (Hrem : rem = 0%N \/ rem = 1%N \/ rem = 2%N) by lia.
  destruct Hrem as [Hrem | [Hrem | Hrem]]; rewrite Hrem; cbn [N.eqb Pos.eqb fst snd].
  - rewrite npow_0; cbn [Str_app].
    destruct (q =? 0)%N eqn:Hq0; cbn [fst snd].
    + apply N.eqb_eq in Hq0; rewrite Hq0.
      cbn [N.mul npow Str_app].
      apply t3Cfg_Z_zero_to_carry.
    + apply N.eqb_neq in Hq0.
      replace (2 * q)%N with (1 + (2 * q - 1))%N at 1 by lia.
      rewrite (npow_add (tokR Z_tok) 1%N (2 * q - 1)%N), npow_1, Str_app_assoc.
      eapply evstep_trans; [apply t3Cfg_Z_succ_to_r0|].
      eapply evstep_trans; [apply (r0_Z_loop (2 * q - 1)%N (tokL P_tok *> evalRle rle2) (evalWK 0%N))|].
      rewrite evalRle_pushRle, evalRle_pushRlePos_one; cbn [wordL]; rewrite app_nil_r.
      apply (r0_end 0%N).
  - rewrite npow_1.
    eapply evstep_trans; [apply t3Cfg_TZ_to_r1OddShort|].
    eapply evstep_trans; [apply (r1OddShort_Z_loop (2 * q)%N (tokL M_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply r1OddShortCfg_evalWK0_to_carry.
  - rewrite npow_2, Str_app_assoc.
    eapply evstep_trans; [apply t3Cfg_TTZ_to_r0|].
    eapply evstep_trans; [apply (r0_Z_loop (2 * q)%N (tokL W_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply (r0_end 0%N).
Qed.

Local Opaque stepZtToCarry.

Lemma carry_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (wordL w *> l) r -[ tm ]->*
  carryCfg l (wordR (revWord w) *> r).
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordL revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply carry_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply carry_P | apply (ih _ _ hts)].
Qed.

Lemma carry_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (npow (wordL w) c *> l) r -[ tm ]->*
  carryCfg l (npow (wordR (revWord w)) c *> r).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordL w) c), Str_app_assoc.
    eapply evstep_trans; [apply (carry_word w _ _ hw)|].
    rewrite (npow_succ_r (wordR (revWord w)) c), Str_app_assoc.
    apply (ih w l _ hw).
Qed.

Notation popCarrySpecial := TM1.popCarrySpecial.

Lemma popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : side)
  (h : popCarrySpecial rle rs = Some (rle', rs')) :
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle rle') (evalRStack rs' r_end).
Proof.
  unfold popCarrySpecial in h.
  destruct (popLastTok rle) as [[t1 r1]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound rle t1 r1 Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popLastTok r1) as [[t2 r2]|] eqn:Hp2; [|discriminate].
    rewrite (popLastTok_sound r1 t2 r2 Hp2).
    destruct t2; try discriminate.
    +  
      pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2)) as Hpcs.
      destruct (popTokCount 8 P_tok 0%N r2) as [mVal r3] eqn:Hpc.
      cbn [fst snd] in Hpcs; rewrite npow_0 in Hpcs; cbn [Str_app] in Hpcs.
      rewrite Hpcs.
      destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
      destruct (popLastTok r3) as [[t3 r4]|] eqn:Hp3; [|discriminate].
      rewrite (popLastTok_sound r3 t3 r4 Hp3).
      destruct t3; try discriminate; inverts h.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL M_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_M_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL T_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_T_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
    +  
      destruct (popTok P_tok r2) as [r3|] eqn:Hp3; [|discriminate].
      inverts h.
      rewrite (popTok_sound P_tok r2 r3 Hp3).
      rewrite evalRle_pushRlePos_one, evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite !app_nil_r.
      apply carry_PTU.
  -  
    destruct (popToks [T_tok; U_tok; M_tok; P_tok] r1) as [r5|] eqn:Hp2.
    + rewrite (popToks_sound _ r1 r5 Hp2).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PMUTM.
    + destruct (popToks [T_tok; T_tok; T_tok; P_tok] r1) as [r5|] eqn:Hp3; [|discriminate].
      rewrite (popToks_sound _ r1 r5 Hp3).
      cbn [wordL app]; rewrite ?Str_app_assoc.
      change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r5)
        with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r5).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PTTTM.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 2%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTW.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos, npow_1.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTT.
Qed.

Local Opaque popCarrySpecial.

Notation popCarryLoop := TM1.popCarryLoop.

Lemma popCarryLoop_sound : forall (fuel : nat) (rle rs : Rle) (r_end : side),
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle (fst (popCarryLoop fuel rle rs))) (evalRStack (snd (popCarryLoop fuel rle rs)) r_end).
Proof.
  induction fuel as [|fuel ih]; intros rle rs r_end; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  destruct rle as [|[w c] rest]; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  cbn [popCarryLoop].
  destruct (isZpWord w) eqn:Hw.
  - cbn [evalRleG].
    eapply evstep_trans; [apply (carry_pow c w (evalRle rest) (evalRStack rs r_end) Hw)|].
    rewrite <- (evalRStack_pushRlePos w c rs r_end).
    apply ih.
  - destruct (popCarrySpecial ((w, c) :: rest) rs) as [[rle' rs']|] eqn:Hsp.
    + eapply evstep_trans; [apply (popCarrySpecial_sound _ _ _ _ r_end Hsp)|].
      apply ih.
    + cbn [fst snd]; apply evstep_refl.
Qed.

Local Opaque popCarryLoop.

Lemma r0_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (wordR w *> r) -[ tm ]->*
  r0Cfg (wordL (revWord w) *> l) r.
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordR revWord]; rewrite wordL_append; cbn [wordL]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply r0_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply r0_P | apply (ih _ _ hts)].
Qed.

Lemma r0_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (npow (wordR w) c *> r) -[ tm ]->*
  r0Cfg (npow (wordL (revWord w)) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR w) c), Str_app_assoc.
    eapply evstep_trans; [apply (r0_word w _ _ hw)|].
    rewrite (npow_succ_r (wordL (revWord w)) c), Str_app_assoc.
    apply (ih w _ _ hw).
Qed.

Notation allZpStack := TM1.allZpStack.

Notation copyRStack := TM1.copyRStack.

Lemma copyRStack_sound : forall (rs : Rle) (rle rle' : Rle) (r_end : side),
  copyRStack rle rs = Some rle' ->
  allZpStack rs = true /\
  r0Cfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->* r0Cfg (evalRle rle') r_end.
Proof.
  induction rs as [|[w c] rest ih]; intros rle rle' r_end h; cbn [copyRStack] in h.
  - inverts h; cbn [allZpStack evalRStack]; split; [reflexivity | apply evstep_refl].
  - destruct (isZpWord w) eqn:Hw; [|discriminate].
    destruct (ih (pushRlePos w c rle) rle' r_end h) as [Hrest Hstep].
    cbn [allZpStack]; rewrite Hw, Hrest; split; [reflexivity|].
    cbn [evalRStack].
    assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact Hw).
    eapply evstep_trans; [apply (r0_pow c (revWord w) (evalRle rle) (evalRStack rest r_end) Hrev)|].
    rewrite revWord_revWord, <- evalRle_pushRlePos.
    exact Hstep.
Qed.

Definition HasRoundtrip (R : N -> side) : Prop :=
  forall (l : side) (k1 : N),
    r0Cfg l (R k1) -[ tm ]->* carryCfg l (R (k1 + 2)%N).

Lemma hasRoundtrip_evalWK : HasRoundtrip evalWK.
Proof.
  intros l k1. exact (r0_end k1 l).
Qed.

Lemma hasRoundtrip_Z (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR Z_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_Z|].
  eapply evstep_trans; [apply (hR (tokL Z_tok *> l) k1)|].
  apply carry_Z.
Qed.

Lemma hasRoundtrip_P (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR P_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_P|].
  eapply evstep_trans; [apply (hR (tokL P_tok *> l) k1)|].
  apply carry_P.
Qed.

Lemma hasRoundtrip_word : forall (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => wordR w *> R k1).
Proof.
  induction w as [|t ts ih]; intros R hw hR; [exact hR|].
  cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
  destruct t; try discriminate; intros l k1; cbn [wordR]; rewrite Str_app_assoc.
  - exact (hasRoundtrip_Z _ (ih R hts hR) l k1).
  - exact (hasRoundtrip_P _ (ih R hts hR) l k1).
Qed.

Lemma hasRoundtrip_pow : forall (c : N) (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => npow (wordR w) c *> R k1).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w R hw hR; [exact hR|].
  intros l k1.
  rewrite (npow_succ_l (wordR w) c), !Str_app_assoc.
  exact (hasRoundtrip_word w _ hw (ih w R hw hR) l k1).
Qed.

Lemma hasRoundtrip_stack : forall (rs : Rle) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => evalRStack rs (R k1)).
Proof.
  induction rs as [|[w c] rest ih]; intros R hrs hR; [exact hR|].
  cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hw hrest].
  intros l k1; cbn [evalRStack].
  assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
  exact (hasRoundtrip_pow c (revWord w) _ Hrev (ih R hrest hR) l k1).
Qed.

Notation r1PhaseCfg := TM1.r1PhaseCfg.

Notation stepR1StarWordL := TM1.stepR1StarWordL.

Notation r1_out := TM1.r1_out.

Notation r1_res := TM1.r1_res.

Notation r1_phase := TM1.r1_phase.

Notation stepR1StarWordL_phase_inv := TM1.stepR1StarWordL_phase_inv.

Lemma stepR1StarWordL_sound : forall (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (wordR (revWord w) *> R k1) -[ tm ]->*
    r1PhaseCfg (r1_phase (stepR1StarWordL w phase))
      (wordL (r1_out (stepR1StarWordL w phase)) *> l)
      (R (k1 + 2 * r1_res (stepR1StarWordL w phase))%N).
Proof.
  induction w as [|t ts ih]; intros phase l R hw hR k1.
  - cbn [stepR1StarWordL r1_phase r1_out r1_res revWord wordR wordL fst snd].
    replace (k1 + 2 * 0)%N with k1 by lia.
    apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    assert (hRt : HasRoundtrip (fun k => tokR t *> R k)).
    { destruct t; try discriminate; [exact (hasRoundtrip_Z R hR) | exact (hasRoundtrip_P R hR)]. }
    pose proof (ih phase l (fun k => tokR t *> R k) hts hRt k1) as Hih.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [exact Hih|].
    cbn [stepR1StarWordL].
    destruct (stepR1StarWordL ts phase) as [[out res] p1] eqn:Hs.
    unfold r1_phase, r1_out, r1_res; cbn [fst snd].
    destruct t; try discriminate; destruct p1; cbn [tokEq r1PhaseCfg r1_phase r1_out r1_res fst snd wordL];
    rewrite ?Str_app_assoc.
    +  
      apply r1Odd_Z.
    +  
      eapply evstep_trans; [apply r1_Z|].
      eapply evstep_trans; [apply (hR (tokL M_tok *> tokL Z_tok *> wordL out *> l) (k1 + 2 * res)%N)|].
      replace (k1 + 2 * res + 2)%N with (k1 + 2 * (res + 1))%N by lia.
      apply turn_ZM.
    +  
      apply r1Odd_P.
    +  
      apply r1_P.
Qed.

Lemma stepR1Star_same_pow : forall (c : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w phase) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (npow (wordR (revWord w)) c *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out (stepR1StarWordL w phase))) c *> l)
      (R (k1 + 2 * (c * r1_res (stepR1StarWordL w phase)))%N).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w phase l R hw hsame hR k1.
  - cbn [npow Str_app]; replace (k1 + 2 * (0 * r1_res (stepR1StarWordL w phase)))%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    pose proof (hasRoundtrip_pow c (revWord w) R Hrev hR) as hR'.
    rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    pose proof (stepR1StarWordL_sound w phase l _ hw hR' k1) as H1.
    rewrite hsame in H1.
    eapply evstep_trans; [exact H1|].
    pose proof (ih w phase (wordL (r1_out (stepR1StarWordL w phase)) *> l) R hw hsame hR
      (k1 + 2 * r1_res (stepR1StarWordL w phase))%N) as Hih.
    replace (k1 + 2 * r1_res (stepR1StarWordL w phase) + 2 * (c * r1_res (stepR1StarWordL w phase)))%N
      with (k1 + 2 * ((c + 1) * r1_res (stepR1StarWordL w phase)))%N in Hih by lia.
    rewrite (npow_succ_r (wordL (r1_out (stepR1StarWordL w phase))) c), Str_app_assoc.
    exact Hih.
Qed.

Lemma stepR1Star_alt_pow : forall (q : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w (r1_phase (stepR1StarWordL w phase))) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    let s1 := stepR1StarWordL w phase in
    let s2 := stepR1StarWordL w (r1_phase s1) in
    r1PhaseCfg phase l (npow (wordR (revWord w)) (2 * q)%N *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out s2 ++ r1_out s1)) q *> l)
      (R (k1 + 2 * (q * (r1_res s1 + r1_res s2)))%N).
Proof.
  induction q as [|q ih] using N_peano_ind; intros w phase l R hw halt hR k1 s1 s2.
  - cbn [N.mul npow Str_app]; replace (k1 + 0)%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    pose proof (hasRoundtrip_pow (2 * q)%N (revWord w) R Hrev hR) as hR2.
    pose proof (hasRoundtrip_word (revWord w) _ Hrev hR2) as hR1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w phase l _ hw hR1 k1)|].
    fold s1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w (r1_phase s1) (wordL (r1_out s1) *> l) _ hw hR2 (k1 + 2 * r1_res s1)%N)|].
    fold s2.
    fold s1 in halt; fold s2 in halt; rewrite halt.
    pose proof (ih w phase (wordL (r1_out s2 ++ r1_out s1) *> l) R hw halt hR
      (k1 + 2 * r1_res s1 + 2 * r1_res s2)%N) as Hih.
    cbn zeta in Hih; fold s1 in Hih; fold s2 in Hih.
    replace (k1 + 2 * r1_res s1 + 2 * r1_res s2 + 2 * (q * (r1_res s1 + r1_res s2)))%N
      with (k1 + 2 * ((q + 1) * (r1_res s1 + r1_res s2)))%N in Hih by lia.
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (r1_out s2 ++ r1_out s1)) q), Str_app_assoc.
    exact Hih.
Qed.

Notation sweepStarLoop := TM1.sweepStarLoop.

Lemma sweepStarLoop_sound : forall (rs : Rle) (rle : Rle) (phase : bool) (totalRes : N) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  forall (k1 : N),
    let res := sweepStarLoop rle phase totalRes rs in
    r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)%N)) -[ tm ]->*
    r1PhaseCfg (snd (fst res)) (evalRle (fst (fst res))) (R (k1 + 2 * snd res)%N).
Proof.
  induction rs as [|[item count] rest ih]; intros rle phase totalRes R hrs hR k1 res.
  - unfold res; cbn [sweepStarLoop evalRStack fst snd]; apply evstep_refl.
  - cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hitem hrest].
    assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact hitem).
    pose proof (hasRoundtrip_stack rest R hrest hR) as hR_rest.
    unfold res; cbn [sweepStarLoop evalRStack].
    set (s1 := stepR1StarWordL item phase).
    destruct (Bool.eqb (r1_phase s1) phase) eqn:Hsame.
    + apply Bool.eqb_prop in Hsame.
      eapply evstep_trans.
      * apply (stepR1Star_same_pow count item phase (evalRle rle) _ hitem Hsame hR_rest (k1 + 2 * totalRes)%N).
      * fold s1.
        replace (k1 + 2 * totalRes + 2 * (count * r1_res s1))%N
          with (k1 + 2 * (totalRes + r1_res s1 * count))%N by lia.
        rewrite <- evalRle_pushRlePos.
        apply (ih (pushRlePos (r1_out s1) count rle) phase (totalRes + r1_res s1 * count)%N R hrest hR k1).
    + assert (Hnot : r1_phase s1 = negb phase).
      { destruct (r1_phase s1), phase; cbn in Hsame; try discriminate; reflexivity. }
      assert (Halt : r1_phase (stepR1StarWordL item (r1_phase s1)) = phase).
      { rewrite Hnot, (stepR1StarWordL_phase_inv item phase hitem).
        fold s1; rewrite Hnot, Bool.negb_involutive; reflexivity. }
      set (s2 := stepR1StarWordL item (r1_phase s1)).
      cbn zeta.
      pose proof (N.div2_odd count) as Hdiv.
      set (q := N.div2 count) in *.
      set (rem := N.b2n (N.odd count)) in *.
      replace count with (2 * q + rem)%N at 1 by lia.
      rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
      pose proof (hasRoundtrip_pow rem (revWord item) _ Hrev hR_rest) as hR_rem.
      eapply evstep_trans.
      * apply (stepR1Star_alt_pow q item phase (evalRle rle) _ hitem Halt hR_rem (k1 + 2 * totalRes)%N).
      * fold s1; fold s2.
        rewrite <- evalRle_pushRle.
        replace (k1 + 2 * totalRes + 2 * (q * (r1_res s1 + r1_res s2)))%N
          with (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q))%N by lia.
        assert (Hrem : rem = 0%N \/ rem = 1%N) by (unfold rem; destruct (N.odd count); auto).
        destruct Hrem as [Hrem | Hrem]; rewrite Hrem; cbn [N.eqb Pos.eqb].
        -- rewrite npow_0; cbn [Str_app].
           apply (ih _ phase _ R hrest hR k1).
        -- rewrite npow_1.
           eapply evstep_trans.
           ++ apply (stepR1StarWordL_sound item phase _ _ hitem hR_rest
                (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q))%N).
           ++ fold s1.
              rewrite <- evalRle_pushRlePos_one.
              replace (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q) + 2 * r1_res s1)%N
                with (k1 + 2 * (totalRes + (r1_res s1 + r1_res s2) * q + r1_res s1))%N by lia.
              apply (ih _ (r1_phase s1) _ R hrest hR k1).
Qed.

Notation modeCfg := TM1.modeCfg.

Notation stepOneTokPure := TM1.stepOneTokPure.

Lemma stepOneTokPure_sound (mode mode' : Mode) (t : Tok) (toks : list Tok) (l r : side)
  (h : stepOneTokPure mode t = Some (toks, mode')) :
  modeCfg mode l (tokR t *> r) -[ tm ]->* modeCfg mode' (wordL toks *> l) r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg wordL app]; rewrite ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Notation stepOneWordPureL := TM1.stepOneWordPureL.

Lemma stepOneWordPureL_sound : forall (w : list Tok) (mode mode' : Mode) (out : list Tok) (l r : side),
  stepOneWordPureL mode w = Some (out, mode') ->
  modeCfg mode l (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (wordL out *> l) r.
Proof.
  induction w as [|t ts ih]; intros mode mode' out l r h; cbn [stepOneWordPureL] in h.
  - inverts h; cbn [revWord wordR wordL Str_app]; apply evstep_refl.
  - destruct (stepOneWordPureL mode ts) as [[outRest mode1]|] eqn:H1; [|discriminate].
    destruct (stepOneTokPure mode1 t) as [[toks mode2]|] eqn:H2; [|discriminate].
    inverts h.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih mode mode1 outRest l (tokR t *> r) H1)|].
    eapply evstep_trans; [apply (stepOneTokPure_sound mode1 mode' t toks (wordL outRest *> l) r H2)|].
    rewrite wordL_append, Str_app_assoc. apply evstep_refl.
Qed.

Lemma stepOneWordPureL_same_pow : forall (c : N) (w out : list Tok) (mode : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) c *> r) -[ tm ]->*
  modeCfg mode (npow (wordL out) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w out mode l r h.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode out l _ h)|].
    rewrite (npow_succ_r (wordL out) c), Str_app_assoc.
    apply (ih w out mode _ r h).
Qed.

Lemma stepOneWordPureL_alt_pow : forall (q : N) (w out1 out2 : list Tok) (mode mode1 : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out1, mode1) ->
  stepOneWordPureL mode1 w = Some (out2, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) (2 * q)%N *> r) -[ tm ]->*
  modeCfg mode (npow (wordL (out2 ++ out1)) q *> l) r.
Proof.
  induction q as [|q ih] using N_peano_ind; intros w out1 out2 mode mode1 l r h1 h2.
  - cbn; apply evstep_refl.
  - replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode1 out1 l _ h1)|].
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode1 mode out2 (wordL out1 *> l) _ h2)|].
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (out2 ++ out1)) q), Str_app_assoc.
    apply (ih w out1 out2 mode mode1 _ r h1 h2).
Qed.

Notation stepOneTokL := TM1.stepOneTokL.

Lemma stepOneTokL_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : side)
  (h : stepOneTokL rle mode t = Some (rle', mode')) :
  modeCfg mode (evalRle rle) (tokR t *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg]; rewrite ?evalRle_pushToksLtr, ?evalRle_pushRlePos_one;
  cbn [revWord wordL app]; rewrite ?app_nil_r, ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Notation stepOneWordL := TM1.stepOneWordL.

Lemma stepOneWordL_sound : forall (w : list Tok) (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneWordL rle mode w = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  induction w as [|t ts ih]; intros rle rle' mode mode' r h; cbn [stepOneWordL] in h.
  - inverts h; cbn [revWord wordR Str_app]; apply evstep_refl.
  - destruct (stepOneWordL rle mode ts) as [[rle1 mode1]|] eqn:H1; [|discriminate].
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih rle rle1 mode mode1 (tokR t *> r) H1)|].
    apply (stepOneTokL_sound rle1 rle' mode1 mode' t r h).
Qed.

Notation stepOneBounceFuel := TM1.stepOneBounceFuel.

Lemma stepOneBounceFuel_sound : forall (fuel : nat) (item : list Tok) (count : N)
  (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneBounceFuel fuel item count rle mode = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (npow (wordR (revWord item)) count *> r) -[ tm ]->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction fuel as [|fuel ih]; intros item count rle rle' mode mode' r h; cbn [stepOneBounceFuel] in h.
  - destruct (count =? 0)%N eqn:Hc0; [|discriminate].
    apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
  - destruct (count =? 0)%N eqn:Hc0.
    + apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
    + apply N.eqb_neq in Hc0.
      assert (Hc_split : count = ((count - 1) + 1)%N) by lia.
      destruct (modeEq mode R0_mode) eqn:Hm0.
      * destruct (isZpWord item) eqn:Hzp.
        -- inverts h; apply modeEq_eq in Hm0; subst mode.
           cbn [modeCfg]; rewrite evalRle_pushRlePos.
           assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact Hzp).
           pose proof (r0_pow count (revWord item) (evalRle rle) r Hrev) as Hr0.
           rewrite revWord_revWord in Hr0; exact Hr0.
        -- destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
           rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
           eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
           exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
      * destruct (stepOneWordPureL mode item) as [[out1 mode1]|] eqn:Hp1; [|discriminate].
        destruct (modeEq mode1 mode) eqn:Hm1.
        -- inverts h; apply modeEq_eq in Hm1; subst mode1.
           rewrite evalRle_pushRlePos.
           exact (stepOneWordPureL_same_pow count item out1 mode' (evalRle rle) r Hp1).
        -- destruct (2 <=? count)%N eqn:Hle2.
           ++ destruct (stepOneWordPureL mode1 item) as [[out2 mode2]|] eqn:Hp2; [|discriminate].
              destruct (modeEq mode2 mode) eqn:Hm2.
              ** apply modeEq_eq in Hm2; subst mode2.
                 cbn zeta in h.
                 pose proof (N.div2_odd count) as Hdiv.
                 set (q := N.div2 count) in *.
                 set (rem := N.b2n (N.odd count)) in *.
                 replace count with (2 * q + rem)%N at 1 by lia.
                 rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordPureL_alt_pow q item out1 out2 mode mode1 (evalRle rle) _ Hp1 Hp2)|].
                 rewrite <- evalRle_pushRle.
                 exact (ih item rem (pushRle (out2 ++ out1) q rle) rle' mode mode' r h).
              ** destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
                 rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
                 exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
           ++ destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
              rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
              eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
              exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
Qed.

Local Opaque stepOneBounceFuel.

Notation simpleOneBounceCarry := TM1.simpleOneBounceCarry.

Lemma simpleOneBounceCarry_sound : forall (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : N),
  simpleOneBounceCarry rle mode rs k1 = Some (rle', kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rle') (evalWK kOut).
Proof.
  induction rs as [|[item count] rest ih]; intros rle rle' mode k1 kOut h; cbn [simpleOneBounceCarry] in h.
  - destruct (modeEq mode R0_mode) eqn:Hm; [|discriminate].
    inverts h; apply modeEq_eq in Hm; subst mode; cbn [modeCfg evalRStack].
    apply r0_end.
  - destruct (stepOneBounceFuel 3 item count rle mode) as [[rle1 mode1]|] eqn:Hb; [|discriminate].
    cbn [evalRStack].
    eapply evstep_trans; [apply (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ Hb)|].
    exact (ih rle1 rle' mode1 k1 kOut h).
Qed.

Notation hasSpecialWord := TM1.hasSpecialWord.

Notation hasSpecial := TM1.hasSpecial.

Notation runRightSweepStarCarry := TM1.runRightSweepStarCarry.

Lemma runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : N)
  (h : runRightSweepStarCarry rle mode rStack k1 = Some (rOut, kOut)) :
  modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rOut) (evalWK kOut).
Proof.
  unfold runRightSweepStarCarry in h.
  destruct (hasSpecial rStack) eqn:Hs.
  - exact (simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h).
  - destruct (modeEq mode R0_mode) eqn:Hm0.
    + destruct (copyRStack rle rStack) as [rle'|] eqn:Hc; [|discriminate].
      inverts h; apply modeEq_eq in Hm0; subst mode; cbn [modeCfg].
      eapply evstep_trans; [exact (proj2 (copyRStack_sound rStack rle rOut (evalWK k1) Hc))|].
      apply r0_end.
    + destruct (allZpStack rStack) eqn:Hall; [|discriminate].
      set (initPhase := negb (modeEq mode R1_mode)) in *.
      assert (Hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
        r1PhaseCfg initPhase (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0)%N))).
      { replace (k1 + 2 * 0)%N with k1 by lia.
        destruct mode; cbn in Hm0; try discriminate; reflexivity. }
      rewrite Hphase.
      pose proof (sweepStarLoop_sound rStack rle initPhase 0%N evalWK Hall hasRoundtrip_evalWK k1) as Hsw.
      cbn zeta in Hsw, h.
      set (res := sweepStarLoop rle initPhase 0%N rStack) in *.
      eapply evstep_trans; [exact Hsw|].
      destruct (snd (fst res)) eqn:Hfp.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1Odd_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [Z_tok] 1%N (fst (fst res))) (k1 + 2 * snd res)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [P_tok] 1%N (fst (fst res))) (k1 + 2 * snd res + 1)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
Qed.

Local Opaque runRightSweepStarCarry.

Notation StepCarryRes := TM1.StepCarryRes.

Notation SCR_halt := TM1.SCR_halt.

Notation SCR_next := TM1.SCR_next.

Notation SCR_err := TM1.SCR_err.

Definition StepCarryValid (cfg : Q * tape) (res : StepCarryRes) : Prop :=
  match res with
  | SCR_halt => exists cfg', (cfg -[ tm ]->* cfg') /\ halted tm cfg'
  | SCR_next rOut kOut => cfg -[ tm ]->* carryCfg (evalRle rOut) (evalWK kOut)
  | SCR_err => False
  end.

Lemma stepCarryValid_of_stepStar (cfg1 cfg2 : Q * tape) (res : StepCarryRes)
  (hstep : cfg1 -[ tm ]->* cfg2) (hval : StepCarryValid cfg2 res) :
  StepCarryValid cfg1 res.
Proof.
  destruct res; cbn [StepCarryValid] in *.
  - destruct hval as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact hstep | exact h2] | exact hhalt].
  - eapply evstep_trans; [exact hstep | exact hval].
  - exact hval.
Qed.

Notation finishTurn := TM1.finishTurn.

Lemma finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N)
  (hne : finishTurn rle mode rStack k1 <> SCR_err) :
  StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
    (finishTurn rle mode rStack k1).
Proof.
  unfold finishTurn in *.
  destruct (runRightSweepStarCarry rle mode rStack k1) as [[rOut kOut]|] eqn:Hr.
  - cbn [StepCarryValid].
    exact (runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut Hr).
  - exfalso; apply hne; reflexivity.
Qed.

Notation matchRule2 := TM1.matchRule2.

Lemma matchRule2_sound (t1 t2 : Tok) (out : list Tok) (mode : Mode) (r4 : Rle) (r : side)
  (h : matchRule2 t1 t2 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> evalRle r4) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r4)) r.
Proof.
  destruct t1, t2; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_WM.
  - apply turn_ZM.
  - apply turn_ZT.
  - apply turn_PT.
Qed.

Notation matchRule3 := TM1.matchRule3.

Lemma matchRule3_sound (t1 t2 t3 : Tok) (out : list Tok) (mode : Mode) (r5 : Rle) (r : side)
  (h : matchRule3 t1 t2 t3 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r5)) r.
Proof.
  destruct t1, t2, t3; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMU.
  - apply turn_ZTM.
  - apply turn_PTM.
  - apply turn_ZTW.
  - apply turn_PTW.
  - apply turn_ZTT.
  - apply turn_PTT.
Qed.

Notation matchRule4 := TM1.matchRule4.

Lemma matchRule4_sound (t1 t2 t3 t4 : Tok) (out : list Tok) (mode : Mode) (r6 : Rle) (r : side)
  (h : matchRule4 t1 t2 t3 t4 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> evalRle r6) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r6)) r.
Proof.
  destruct t1, t2, t3, t4; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZPMU.
  - apply turn_ZTTM.
  - apply turn_PTTM.
  - apply turn_MUTW.
  - apply turn_ZTTW.
  - apply turn_PTMT.
  - apply turn_ZTTT.
Qed.

Notation matchRule5 := TM1.matchRule5.

Lemma matchRule5_sound (t1 t2 t3 t4 t5 : Tok) (out : list Tok) (mode : Mode) (r7 : Rle) (r : side)
  (h : matchRule5 t1 t2 t3 t4 t5 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> tokL t5 *> evalRle r7) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r7)) r.
Proof.
  destruct t1, t2, t3, t4, t5; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMUTM.
  - apply turn_ZTTTM.
  - apply turn_PTTTW.
Qed.

Notation isEmptyRle := TM1.isEmptyRle.

Notation isEmptyRle_eq := TM1.isEmptyRle_eq.

Notation stepTurnFrom3 := TM1.stepTurnFrom3.

Lemma stepTurnFrom3_sound (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom3 t1 t2 t3 r5 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom3 t1 t2 t3 r5 rStack k1).
Proof.
  unfold stepTurnFrom3 in *.
  destruct (matchRule3 t1 t2 t3) as [[out mode]|] eqn:Hm3.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule3_sound t1 t2 t3 out mode r5 _ Hm3)
      (finishTurn_sound (pushToksLtr out r5) mode rStack k1 hne)).
  - destruct (popLastTok r5) as [[t4 r6]|] eqn:Hp4; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r5 t4 r6 Hp4).
    destruct (matchRule4 t1 t2 t3 t4) as [[out mode]|] eqn:Hm4.
    + exact (stepCarryValid_of_stepStar _ _ _
        (matchRule4_sound t1 t2 t3 t4 out mode r6 _ Hm4)
        (finishTurn_sound (pushToksLtr out r6) mode rStack k1 hne)).
    + destruct (popLastTok r6) as [[t5 r7]|] eqn:Hp5; [|exfalso; apply hne; reflexivity].
      rewrite (popLastTok_sound r6 t5 r7 Hp5).
      destruct (matchRule5 t1 t2 t3 t4 t5) as [[out mode]|] eqn:Hm5; [|exfalso; apply hne; reflexivity].
      exact (stepCarryValid_of_stepStar _ _ _
        (matchRule5_sound t1 t2 t3 t4 t5 out mode r7 _ Hm5)
        (finishTurn_sound (pushToksLtr out r7) mode rStack k1 hne)).
Qed.

Notation stepTurnFrom2 := TM1.stepTurnFrom2.

Lemma stepTurnFrom2_sound (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom2 t1 t2 r4 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> evalRle r4) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom2 t1 t2 r4 rStack k1).
Proof.
  unfold stepTurnFrom2 in *.
  destruct (matchRule2 t1 t2) as [[out mode]|] eqn:Hm2.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule2_sound t1 t2 out mode r4 _ Hm2)
      (finishTurn_sound (pushToksLtr out r4) mode rStack k1 hne)).
  - destruct (popLastTok r4) as [[t3 r5]|] eqn:Hp3; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r4 t3 r5 Hp3).
    destruct (tokEq t1 T_tok) eqn:Ht1.
    + destruct (tokEq t2 M_tok) eqn:Hm2'.
      * destruct (tokEq t3 U_tok) eqn:Hu3.
        -- exfalso; apply hne; reflexivity.
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
    + destruct (tokEq t1 U_tok) eqn:Hu1.
      * destruct (tokEq t2 T_tok) eqn:Ht2.
        -- destruct (tokEq t3 Z_tok) eqn:Hz3.
           ++ apply tokEq_eq in Hu1; apply tokEq_eq in Ht2; apply tokEq_eq in Hz3.
              subst t1 t2 t3.
              cbn [StepCarryValid].
              eexists; split; [apply turn_ZTU_halt | reflexivity].
           ++ exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
Qed.

Notation stepTurnaround := TM1.stepTurnaround.

Lemma stepTurnaround_sound (r2 rStack : Rle) (k1 : N)
  (hne : stepTurnaround r2 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (stepTurnaround r2 rStack k1).
Proof.
  unfold stepTurnaround in *.
  destruct (popLastTok r2) as [[t1 r3]|] eqn:Hp1; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r2 t1 r3 Hp1).
  destruct (popLastTok r3) as [[t2 r4]|] eqn:Hp2; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r3 t2 r4 Hp2).
  destruct (tokEq t1 M_tok) eqn:Hm1.
  - destruct (tokEq t2 U_tok) eqn:Hu2.
    + exfalso; apply hne; reflexivity.
    + exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
  - exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
Qed.

Local Opaque stepTurnaround.

Lemma special_ZTM_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL M_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL M_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTM.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTM|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_PT_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL T_tok *> npow (tokL P_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_PT.
  - rewrite (npow_succ_l (tokL P_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_PT|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_ZTW_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL W_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) (n + 1)%N *> tokL W_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTW.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTW|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_Z|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_Z R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_Z|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL Z_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Notation stepSpecialLoops := TM1.stepSpecialLoops.

Lemma stepSpecialLoops_sound (r2 rStack : Rle) (k1 : N) (res : StepCarryRes)
  (h : stepSpecialLoops r2 rStack k1 = Some res) (hne : res <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res.
Proof.
  unfold stepSpecialLoops in h.
  destruct (popLastTok r2) as [[t1 r2a]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound r2 t1 r2a Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popTok M_tok r2a) as [rest|] eqn:Hpm; [|discriminate].
    rewrite (popTok_sound M_tok r2a rest Hpm).
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N rest) as [mVal r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
    apply N.eqb_neq in Hm0.
    destruct (popTok Z_tok r3) as [r4|] eqn:Hpz; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h.
    rewrite Hcnt, (popTok_sound Z_tok r3 r4 Hpz).
    eapply stepCarryValid_of_stepStar; [apply carry_MU_to_pmuCfg|].
    eapply stepCarryValid_of_stepStar; [apply (pmu_loop mVal (tokL Z_tok *> evalRle r4))|].
    replace mVal with (1 + (mVal - 1))%N at 1 by lia.
    rewrite (npow_add (tokR Z_tok) 1%N (mVal - 1)%N), npow_1, Str_app_assoc.
    eapply stepCarryValid_of_stepStar; [apply pmuCfg_Z_turn|].
    eapply stepCarryValid_of_stepStar; [apply (r0_Z_loop (mVal - 1)%N)|].
    eapply stepCarryValid_of_stepStar; [apply r0_P|].
    set (r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4))) in *.
    assert (Hr5 : tokL P_tok *> npow (tokL Z_tok) (mVal - 1)%N *> tokL M_tok *> tokL W_tok *> tokL T_tok *> evalRle r4 = evalRle r5).
    { unfold r5; rewrite evalRle_pushRlePos_one, evalRle_pushRle, evalRle_pushToksLtr.
      cbn [revWord wordL app]; rewrite app_nil_r, !Str_app_assoc; reflexivity. }
    rewrite Hr5.
    exact (finishTurn_sound r5 R0_mode rStack k1 hne).
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTM_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTW_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2a)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N r2a) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_PT_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushRlePos_one in Hcopy;
    cbn [wordL app] in Hcopy; rewrite app_nil_r in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
Qed.

Local Opaque stepSpecialLoops.

Definition stepCarryAux (fuel : nat) (rle : Rle) (k1 : N) : StepCarryRes :=
  let '(r2, rStack) := popCarryLoop fuel rle [] in
  if hasSpecial rStack then
    stepTurnaround r2 rStack k1
  else
    match stepSpecialLoops r2 rStack k1 with
    | None => stepTurnaround r2 rStack k1
    | Some res => res
    end.

Lemma stepCarryAux_sound (fuel : nat) (rle : Rle) (k1 : N)
  (hne : stepCarryAux fuel rle k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarryAux fuel rle k1).
Proof.
  pose proof (popCarryLoop_sound fuel rle [] (evalWK k1)) as Hp.
  cbn [evalRStack] in Hp.
  unfold stepCarryAux in *.
  destruct (popCarryLoop fuel rle []) as [r2 rStack] eqn:Hpop.
  cbn [fst snd] in Hp.
  eapply stepCarryValid_of_stepStar; [exact Hp|].
  destruct (hasSpecial rStack) eqn:Hns.
  - exact (stepTurnaround_sound r2 rStack k1 hne).
  - destruct (stepSpecialLoops r2 rStack k1) as [res|] eqn:Hsl.
    + exact (stepSpecialLoops_sound r2 rStack k1 res Hsl hne).
    + exact (stepTurnaround_sound r2 rStack k1 hne).
Qed.

Fixpoint runCarryChunkAux (fuel : nat) (n : nat) (rle : Rle) (k1 : N) : StepCarryRes :=
  match n with
  | O => SCR_next rle k1
  | S n' =>
    match stepCarryAux fuel rle k1 with
    | SCR_halt => SCR_halt
    | SCR_next rle' k1' => runCarryChunkAux fuel n' rle' k1'
    | SCR_err => SCR_err
    end
  end.

Lemma runCarryChunkAux_sound (fuel : nat) : forall (n : nat) (rle : Rle) (k1 : N),
  runCarryChunkAux fuel n rle k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (runCarryChunkAux fuel n rle k1).
Proof.
  induction n as [|n ih]; intros rle k1 hne; cbn [runCarryChunkAux] in *.
  - cbn [StepCarryValid]; apply evstep_refl.
  - destruct (stepCarryAux fuel rle k1) as [|rle' k1'|] eqn:Hs.
    + pose proof (stepCarryAux_sound fuel rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; exact Hv.
    + pose proof (stepCarryAux_sound fuel rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; cbn [StepCarryValid] in Hv.
      exact (stepCarryValid_of_stepStar _ _ _ Hv (ih rle' k1' hne)).
    + exfalso; apply hne; reflexivity.
Qed.

End GeneralizedRle.

Notation evalRStack := TM1.evalRStack.

Notation pushRlePos := TM1.pushRlePos.

Notation pushRle := TM1.pushRle.

Notation evalRle_pushRlePos := TM1.evalRle_pushRlePos.

Notation evalRle_pushRle := TM1.evalRle_pushRle.

Notation evalRle_pushRlePos_one := TM1.evalRle_pushRlePos_one.

Notation evalRStack_pushRlePos := TM1.evalRStack_pushRlePos.

Notation evalRStack_pushRle := TM1.evalRStack_pushRle.

Notation pushToksLtr := TM1.pushToksLtr.

Notation evalRle_pushToksLtr := TM1.evalRle_pushToksLtr.

Notation popLastTok := TM1.popLastTok.

Notation popLastTok_sound := TM1.popLastTok_sound.

Notation popTok := TM1.popTok.

Notation popTok_sound := TM1.popTok_sound.

Notation popToks := TM1.popToks.

Notation popToks_sound := TM1.popToks_sound.

Notation popTokCount := TM1.popTokCount.

Notation popTokCount_sound := TM1.popTokCount_sound.

Notation evalWK := TM1.evalWK.

Notation cfgR := TM1.cfgR.

Notation carryCfg := TM1.carryCfg.

Notation r0Cfg := TM1.r0Cfg.

Notation r1Cfg := TM1.r1Cfg.

Notation r1OddShortCfg := TM1.r1OddShortCfg.

Notation r1OddCfg := TM1.r1OddCfg.

Notation wSweepCfg := TM1.wSweepCfg.

Notation dSweepCfg := TM1.dSweepCfg.

Notation tSweepCfg := TM1.tSweepCfg.

Notation t3Cfg := TM1.t3Cfg.

Notation pmuCfg := TM1.pmuCfg.

Notation stepZtToCarry := TM1.stepZtToCarry.

Notation popCarrySpecial := TM1.popCarrySpecial.

Notation popCarryLoop := TM1.popCarryLoop.

Notation allZpStack := TM1.allZpStack.

Notation copyRStack := TM1.copyRStack.

Notation r1PhaseCfg := TM1.r1PhaseCfg.

Notation stepR1StarWordL := TM1.stepR1StarWordL.

Notation r1_out := TM1.r1_out.

Notation r1_res := TM1.r1_res.

Notation r1_phase := TM1.r1_phase.

Notation stepR1StarWordL_phase_inv := TM1.stepR1StarWordL_phase_inv.

Notation sweepStarLoop := TM1.sweepStarLoop.

Notation modeCfg := TM1.modeCfg.

Notation stepOneTokPure := TM1.stepOneTokPure.

Notation stepOneWordPureL := TM1.stepOneWordPureL.

Notation stepOneTokL := TM1.stepOneTokL.

Notation stepOneWordL := TM1.stepOneWordL.

Notation stepOneBounceFuel := TM1.stepOneBounceFuel.

Notation simpleOneBounceCarry := TM1.simpleOneBounceCarry.

Notation hasSpecialWord := TM1.hasSpecialWord.

Notation hasSpecial := TM1.hasSpecial.

Notation runRightSweepStarCarry := TM1.runRightSweepStarCarry.

Notation StepCarryRes := TM1.StepCarryRes.

Notation SCR_halt := TM1.SCR_halt.

Notation SCR_next := TM1.SCR_next.

Notation SCR_err := TM1.SCR_err.

Notation finishTurn := TM1.finishTurn.

Notation matchRule2 := TM1.matchRule2.

Notation matchRule3 := TM1.matchRule3.

Notation matchRule4 := TM1.matchRule4.

Notation matchRule5 := TM1.matchRule5.

Notation isEmptyRle := TM1.isEmptyRle.

Notation isEmptyRle_eq := TM1.isEmptyRle_eq.

Notation stepTurnFrom3 := TM1.stepTurnFrom3.

Notation stepTurnFrom2 := TM1.stepTurnFrom2.

Notation stepTurnaround := TM1.stepTurnaround.

Notation stepSpecialLoops := TM1.stepSpecialLoops.

Notation takeRle := TM1.takeRle.

Notation dropRle := TM1.dropRle.

Notation evalRleG_take_drop := TM1.evalRleG_take_drop.

Fixpoint runCarryScheduleAux (fuel : nat) (sched : list N) (k : nat) (rle : Rle) (k1 : N) : bool :=
  match sched with
  | [] => false
  | n :: rest =>
    match runCarryChunkAux fuel (N.to_nat n) rle k1 with
    | SCR_halt => true
    | SCR_next rle' k1' => runCarryScheduleAux fuel rest k (takeRle k rle') k1'
    | SCR_err => false
    end
  end.

Lemma runCarryScheduleAux_sound (fuel : nat) : forall (sched : list N) (k : nat) (rle : Rle) (k1 : N) (l_end : side),
  runCarryScheduleAux fuel sched k rle k1 = true ->
  exists cfg', (carryCfg (evalRleG l_end rle) (evalWK k1) -[ tm ]->* cfg') /\ halted tm cfg'.
Proof.
  induction sched as [|n rest ih]; intros k rle k1 l_end h; cbn [runCarryScheduleAux] in h; [discriminate|].
  destruct (runCarryChunkAux fuel (N.to_nat n) rle k1) as [|rle' k1'|] eqn:Hc; [| |discriminate].
  - pose proof (runCarryChunkAux_sound l_end fuel (N.to_nat n) rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv; exact Hv.
  - pose proof (runCarryChunkAux_sound l_end fuel (N.to_nat n) rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv.
    rewrite (evalRleG_take_drop k rle' l_end) in Hv.
    destruct (ih k (takeRle k rle') k1' (evalRleG l_end (dropRle k rle')) h) as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact Hv | exact h2] | exact hhalt].
Qed.

Notation ckptRle_0 := TM1.ckptRle_0.

Notation ckpt0_ccfg := TM1.ckpt0_ccfg.

Lemma init_to_ckpt0_vm :
  bmultiStep tm (N.to_nat 6724%N) (mkCCfg A 0%sym []%sym []%sym) = Some ckpt0_ccfg.
Proof. vm_cast_no_check (eq_refl (Some ckpt0_ccfg)). Qed.

Lemma init_to_ckpt0 :
  c0 -[ tm ]->* carryCfg (evalRleG 0inf ckptRle_0) (evalWK 1%N).
Proof.
  exact (bmultiStep_sound tm (N.to_nat 6724%N)
    (mkCCfg A 0%sym []%sym []%sym)
    ckpt0_ccfg
    init_to_ckpt0_vm).
Qed.

Notation carry_sched := TM1.carry_sched.

Lemma runCarrySchedule_ok :
  runCarryScheduleAux (N.to_nat 80%N) carry_sched (N.to_nat 30%N) ckptRle_0 1%N = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem halt: halts tm c0.
Proof.
  destruct (runCarryScheduleAux_sound (N.to_nat 80%N) carry_sched (N.to_nat 30%N) ckptRle_0 1%N 0inf runCarrySchedule_ok)
    as [cfg' [Hsteps Hhalted]].
  eapply halts_evstep.
  - exact (halted_halts tm cfg' Hhalted).
  - eapply evstep_trans; [exact init_to_ckpt0 | exact Hsteps].
Qed.

End TM2.
Print Assumptions TM2.halt.

From Coq Require Import Bool Lists.List NArith.BinNat NArith.Nnat Lia String.

Module TM3.
Import BusyCoq.Individual62.

Import Bool List BinNat Nnat Lia String.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope sym.

Open Scope list.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

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

Definition evalWK (k1 : N) : side :=
  [1; 0; 1; 1]%sym *> (npow [0; 0; 1; 1]%sym k1 *> 0inf).

Notation cfgR := TM1.cfgR.

Notation carryCfg := TM1.carryCfg.

Notation r0Cfg := TM1.r0Cfg.

Notation r1Cfg := TM1.r1Cfg.

Notation r1OddShortCfg := TM1.r1OddShortCfg.

Definition r1OddCfg (l r : side) : Q * tape :=
  r1OddShortCfg (tokL Z *> l) r.

Notation wSweepCfg := TM1.wSweepCfg.

Notation dSweepCfg := TM1.dSweepCfg.

Notation tSweepCfg := TM1.tSweepCfg.

Notation t3Cfg := TM1.t3Cfg.

Notation pmuCfg := TM1.pmuCfg.

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
    +  
      eapply evstep_trans; [apply r1Odd_Z |].
      exact (IH true (tokL Z *> l) R Hw hR k1).
    +  
      pose proof (hasRoundtrip_word ts Hw hR) as hR'.
      eapply evstep_trans; [apply r1_Z |].
      eapply evstep_trans; [exact (hR' (tokL M *> (tokL Z *> l)) k1) |].
      eapply evstep_trans; [apply turn_ZM |].
      pose proof (IH false (tokL P *> l) R Hw hR (k1 + 2)%N) as Hsub.
      replace (k1 + 2 * (sr1_res (stepR1StarWord ts false) + 1))%N
        with (k1 + 2 + 2 * sr1_res (stepR1StarWord ts false))%N by lia.
      exact Hsub.
    +  
      eapply evstep_trans; [apply r1Odd_P |].
      exact (IH false (tokL Z *> l) R Hw hR k1).
    +  
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

Theorem halt: halts tm c0.
Proof.
  exact (halts_of_evstep _ _ init_to_initRle
    (runCarryAux_sound (N.to_nat 80%N) (N.to_nat 2605%N) initRle 1%N runCarry_2605)).
Qed.

End TM3.
Print Assumptions TM3.halt.



Module TM4.
Import BusyCoq.Individual62.

Import Bool List Streams PeanoNat Lia NArith ZArith String.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---").

Open Scope list_scope.

Notation N_peano_ind := TM1.N_peano_ind.

Notation npow := TM1.npow.

Notation npow_0 := TM1.npow_0.

Notation npow_1 := TM1.npow_1.

Notation npow_add := TM1.npow_add.

Notation npow_2 := TM1.npow_2.

Notation npow_3 := TM1.npow_3.

Notation npow_succ_l := TM1.npow_succ_l.

Notation npow_succ_r := TM1.npow_succ_r.

Notation zero_cons_0inf := TM1.zero_cons_0inf.

Notation CCfg := TM1.CCfg.

Notation mkCCfg := TM1.mkCCfg.

Notation cc_q := TM1.cc_q.

Notation cc_cur := TM1.cc_cur.

Notation cc_l := TM1.cc_l.

Notation cc_r := TM1.cc_r.

Notation sym_eqb := TM1.sym_eqb.

Notation sym_eqb_eq := TM1.sym_eqb_eq.

Notation is_nil_sym := TM1.is_nil_sym.

Notation evalWindow := TM1.evalWindow.

Notation evalCCfg := TM1.evalCCfg.

Notation evalRCCfg := TM1.evalRCCfg.

Notation evalBCfg := TM1.evalBCfg.

Notation wstep := TM1.wstep.

Notation wstep_sound := TM1.wstep_sound.

Notation wmultiStep := TM1.wmultiStep.

Notation wmultiStep_sound := TM1.wmultiStep_sound.

Notation cstep := TM1.cstep.

Notation cstep_sound := TM1.cstep_sound.

Notation cmultiStep := TM1.cmultiStep.

Notation cmultiStep_sound := TM1.cmultiStep_sound.

Notation rcstep := TM1.rcstep.

Notation rcstep_sound := TM1.rcstep_sound.

Notation rcmultiStep := TM1.rcmultiStep.

Notation rcmultiStep_sound := TM1.rcmultiStep_sound.

Notation bstep := TM1.bstep.

Notation bstep_sound := TM1.bstep_sound.

Notation bmultiStep := TM1.bmultiStep.

Notation bmultiStep_sound := TM1.bmultiStep_sound.

Notation Tok := TM1.Tok.

Notation U_tok := TM1.U_tok.

Notation M_tok := TM1.M_tok.

Notation W_tok := TM1.W_tok.

Notation Z_tok := TM1.Z_tok.

Notation T_tok := TM1.T_tok.

Notation P_tok := TM1.P_tok.

Notation PTTTM_TAIL_tok := TM1.PTTTM_TAIL_tok.

Notation Mode := TM1.Mode.

Notation R0_mode := TM1.R0_mode.

Notation R1_mode := TM1.R1_mode.

Notation R1_ODD_mode := TM1.R1_ODD_mode.

Notation Rle := TM1.Rle.

Notation tokEq := TM1.tokEq.

Notation tokEq_eq := TM1.tokEq_eq.

Notation modeEq := TM1.modeEq.

Notation modeEq_eq := TM1.modeEq_eq.

Notation wordEq := TM1.wordEq.

Notation wordEq_eq := TM1.wordEq_eq.

Notation isZpTok := TM1.isZpTok.

Notation isZpWord := TM1.isZpWord.

Notation revWord := TM1.revWord.

Notation revWord_append := TM1.revWord_append.

Notation revWord_revWord := TM1.revWord_revWord.

Notation isZpWord_append := TM1.isZpWord_append.

Notation isZpWord_revWord := TM1.isZpWord_revWord.

Notation tokL := TM1.tokL.

Notation tokR := TM1.tokR.

Notation wordL := TM1.wordL.

Notation wordR := TM1.wordR.

Notation wordL_append := TM1.wordL_append.

Notation wordR_append := TM1.wordR_append.

Fixpoint evalRle (rle : Rle) : side :=
  match rle with
  | [] => 0inf
  | (w, c) :: rest => npow (wordL w) c *> evalRle rest
  end.

Notation evalRStack := TM1.evalRStack.

Notation pushRlePos := TM1.pushRlePos.

Notation pushRle := TM1.pushRle.

Lemma evalRle_pushRlePos (w : list Tok) (c : N) (rle : Rle) :
  evalRle (pushRlePos w c rle) = npow (wordL w) c *> evalRle rle.
Proof.
  destruct rle as [|[w' c'] rest]; cbn [pushRlePos evalRle]; [reflexivity|].
  destruct (wordEq w w') eqn:Hw; cbn [evalRle].
  - apply wordEq_eq in Hw; subst w'.
    rewrite npow_add, Str_app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma evalRle_pushRle (w : list Tok) (c : N) (rle : Rle) :
  evalRle (pushRle w c rle) = npow (wordL w) c *> evalRle rle.
Proof.
  unfold pushRle. destruct (c =? 0)%N eqn:Hc.
  - apply N.eqb_eq in Hc; subst c; rewrite npow_0; reflexivity.
  - apply evalRle_pushRlePos.
Qed.

Lemma evalRle_pushRlePos_one (w : list Tok) (rle : Rle) :
  evalRle (pushRlePos w 1%N rle) = wordL w *> evalRle rle.
Proof.
  rewrite evalRle_pushRlePos, npow_1. reflexivity.
Qed.

Notation evalRStack_pushRlePos := TM1.evalRStack_pushRlePos.

Notation evalRStack_pushRle := TM1.evalRStack_pushRle.

Local Opaque pushRlePos pushRle.

Notation pushToksLtr := TM1.pushToksLtr.

Lemma evalRle_pushToksLtr (ts : list Tok) : forall (rle : Rle),
  evalRle (pushToksLtr ts rle) = wordL (revWord ts) *> evalRle rle.
Proof.
  induction ts as [|t ts ih]; intro rle; cbn [pushToksLtr revWord wordL]; [reflexivity|].
  rewrite ih, evalRle_pushRlePos_one, wordL_append, Str_app_assoc; cbn [wordL]; rewrite app_nil_r.
  reflexivity.
Qed.

Notation popLastTok := TM1.popLastTok.

Lemma popLastTok_sound (rle : Rle) (t : Tok) (rle' : Rle)
  (h : popLastTok rle = Some (t, rle')) :
  evalRle rle = tokL t *> evalRle rle'.
Proof.
  destruct rle as [|[w c] rest]; [discriminate|].
  destruct w as [|t0 ts]; [discriminate|].
  cbn [popLastTok] in h.
  destruct (c =? 0)%N eqn:Hc0; [discriminate|].
  apply N.eqb_neq in Hc0.
  assert (Hc_split : c = (1 + (c - 1))%N) by lia.
  destruct ts as [|t2 ts2].
  - destruct (c =? 1)%N eqn:Hc1; inverts h.
    + apply N.eqb_eq in Hc1; subst c.
      cbn [evalRle]; rewrite npow_1; cbn [wordL]; rewrite app_nil_r; reflexivity.
    + cbn [evalRle]; rewrite Hc_split at 1; rewrite npow_add, npow_1, Str_app_assoc.
      cbn [wordL]; rewrite app_nil_r; reflexivity.
  - destruct (c =? 1)%N eqn:Hc1; inverts h.
    + apply N.eqb_eq in Hc1; subst c.
      cbn [evalRle]; rewrite evalRle_pushRlePos_one, npow_1; cbn [wordL]; rewrite Str_app_assoc; reflexivity.
    + cbn [evalRle]; rewrite evalRle_pushRlePos_one; cbn [evalRle].
      rewrite Hc_split at 1; rewrite npow_add, npow_1, Str_app_assoc.
      cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Notation popTok := TM1.popTok.

Lemma popTok_sound (t_exp : Tok) (rle rle' : Rle)
  (h : popTok t_exp rle = Some rle') :
  evalRle rle = tokL t_exp *> evalRle rle'.
Proof.
  unfold popTok in h.
  destruct (popLastTok rle) as [[t r1]|] eqn:Hp; [|discriminate].
  destruct (tokEq t t_exp) eqn:Ht; [|discriminate].
  inverts h; apply tokEq_eq in Ht; subst t.
  exact (popLastTok_sound rle t_exp rle' Hp).
Qed.

Notation popToks := TM1.popToks.

Lemma popToks_sound (ts : list Tok) : forall (rle rle' : Rle),
  popToks ts rle = Some rle' ->
  evalRle rle = wordL ts *> evalRle rle'.
Proof.
  induction ts as [|t ts ih]; intros rle rle' h; cbn [popToks] in h.
  - inverts h; reflexivity.
  - destruct (popTok t rle) as [r1|] eqn:Hp; [|discriminate].
    rewrite (popTok_sound t rle r1 Hp), (ih r1 rle' h); cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Notation popTokCount := TM1.popTokCount.

Lemma popTokCount_sound (fuel : nat) (t_exp : Tok) : forall (acc : N) (rle : Rle),
  (acc <= fst (popTokCount fuel t_exp acc rle))%N /\
  npow (tokL t_exp) acc *> evalRle rle =
    npow (tokL t_exp) (fst (popTokCount fuel t_exp acc rle)) *> evalRle (snd (popTokCount fuel t_exp acc rle)).
Proof.
  induction fuel as [|fuel ih]; intros acc rle; [cbn [popTokCount fst snd]; split; [lia | reflexivity]|].
  destruct rle as [|[[|t ts] c] rest]; cbn [popTokCount fst snd]; try (split; [lia | reflexivity]).
  destruct (tokEq t t_exp) eqn:Ht; [|cbn [fst snd]; split; [lia | reflexivity]].
  apply tokEq_eq in Ht; subst t.
  destruct (c =? 0)%N eqn:Hc0; [cbn [fst snd]; split; [lia | reflexivity]|].
  apply N.eqb_neq in Hc0.
  assert (Hc_split : c = (1 + (c - 1))%N) by lia.
  destruct ts as [|t2 ts2].
  - destruct (ih (acc + c)%N rest) as [Hle Heq].
    split; [lia |].
    rewrite <- Heq; cbn [evalRle wordL]; rewrite app_nil_r, npow_add, Str_app_assoc; reflexivity.
  - destruct (c =? 1)%N eqn:Hc1.
    + apply N.eqb_eq in Hc1; subst c.
      destruct (ih (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N rest)) as [Hle Heq].
      split; [lia |].
      rewrite <- Heq, evalRle_pushRlePos_one, npow_add; cbn [evalRle wordL].
      rewrite !npow_1, !Str_app_assoc; reflexivity.
    + destruct (ih (acc + 1)%N (pushRlePos (t2 :: ts2) 1%N ((t_exp :: t2 :: ts2, (c - 1)%N) :: rest))) as [Hle Heq].
      split; [lia |].
      rewrite <- Heq, evalRle_pushRlePos_one; cbn [evalRle].
      rewrite (npow_add (tokL t_exp) acc 1%N), npow_1, !Str_app_assoc.
      f_equal. rewrite Hc_split at 1.
      rewrite (npow_add (wordL (t_exp :: t2 :: ts2)) 1%N (c - 1)%N), npow_1, !Str_app_assoc.
      cbn [wordL]; rewrite Str_app_assoc; reflexivity.
Qed.

Local Opaque popTokCount.

Notation evalWK := TM1.evalWK.

Definition cfgR (l : side) : Q * tape :=
  (D, ([1; 1]%sym *> l, 0%sym, 0inf)).

Definition carryCfg (l r : side) : Q * tape :=
  (D, (l, 1%sym, [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).

Notation r0Cfg := TM1.r0Cfg.

Notation r1Cfg := TM1.r1Cfg.

Definition r1OddShortCfg (l r : side) : Q * tape :=
  (D, ([1; 1; 0; 0; 0; 0; 1; 1]%sym *> l, 1%sym, r)).

Definition r1OddCfg (l r : side) : Q * tape :=
  r1OddShortCfg (tokL Z_tok *> l) r.

Definition wSweepCfg (l r : side) : Q * tape :=
  (A, (l, 1%sym, [1]%sym *> r)).

Notation dSweepCfg := TM1.dSweepCfg.

Notation tSweepCfg := TM1.tSweepCfg.

Definition t3Cfg (l r : side) : Q * tape :=
  (D, (l, 1%sym, [0; 1; 0; 0; 1]%sym *> r)).

Definition pmuCfg (l r : side) : Q * tape :=
  (A, (l, 1%sym, [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).

Ltac solve_wstep n c1 c2 l r :=
  exact (wmultiStep_sound tm n c1 c2 l r ltac:(vm_compute; reflexivity)).

Ltac solve_cstep n c1 c2 r :=
  exact (cmultiStep_sound tm n c1 c2 r ltac:(vm_compute; reflexivity)).

Ltac solve_rcstep n c1 c2 l :=
  exact (rcmultiStep_sound tm n c1 c2 l ltac:(vm_compute; reflexivity)).

Lemma carry_Z (l r : side) :
  carryCfg (tokL Z_tok *> l) r -[ tm ]->* carryCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 62
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_P (l r : side) :
  carryCfg (tokL P_tok *> l) r -[ tm ]->* carryCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 22
    (mkCCfg D 1%sym [0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 90
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTW (l r : side) :
  carryCfg (tokL W_tok *> npow (tokL T_tok) 2%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 3%N *> r).
Proof.
  solve_wstep 134
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTT (l r : side) :
  carryCfg (npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR P_tok *> r).
Proof.
  solve_wstep 94
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTTTM (l r : side) :
  carryCfg (tokL M_tok *> npow (tokL T_tok) 3%N *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg l (npow (tokR Z_tok) 2%N *> tokR PTTTM_TAIL_tok *> r).
Proof.
  solve_wstep 111
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_UM (r : side) :
  carryCfg (tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 67
    (mkCCfg D 1%sym [0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_UMT (r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL U_tok *> 0inf) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> 0inf) r.
Proof.
  solve_cstep 105
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1]%sym []%sym) r.
Qed.

Lemma turn_ZT (l r : side) :
  carryCfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 67
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_WM (l r : side) :
  carryCfg (tokL M_tok *> tokL W_tok *> l) r -[ tm ]->*
  r1Cfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 59
    (mkCCfg D 1%sym [0; 1; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PT (l r : side) :
  carryCfg (tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 125
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZM (l r : side) :
  carryCfg (tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 59
    (mkCCfg D 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 151
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 105
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 109
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL T_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 121
    (mkCCfg D 1%sym [0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 133
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 137
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_MUTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  r1OddCfg (tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 151
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 175
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 175
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 117
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZPMU (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> tokL P_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 177
    (mkCCfg D 1%sym [0; 1; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZMUTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL U_tok *> tokL M_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 171
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_PTTTW (l r : side) :
  carryCfg (tokL W_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL Z_tok *> tokL Z_tok *> tokL Z_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 221
    (mkCCfg D 1%sym [0; 0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma carry_MU_to_pmuCfg (l r : side) :
  carryCfg (tokL U_tok *> tokL M_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR P_tok *> r).
Proof.
  solve_wstep 19
    (mkCCfg D 1%sym [0; 1; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg A 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmu_step (l r : side) :
  pmuCfg (tokL P_tok *> l) r -[ tm ]->*
  pmuCfg l (tokR Z_tok *> r).
Proof.
  solve_wstep 66
    (mkCCfg A 1%sym [0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg A 1%sym []%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_Z_turn (l r : side) :
  pmuCfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->*
  r0Cfg (tokL M_tok *> tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 40
    (mkCCfg A 1%sym [0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma pmuCfg_M_to_carry (l r : side) :
  pmuCfg (tokL M_tok *> l) r -[ tm ]->*
  carryCfg (tokL U_tok *> l) r.
Proof.
  solve_wstep 7
    (mkCCfg A 1%sym [0; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [0; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma pmuCfg_T_to_carry (l r : side) :
  pmuCfg (tokL T_tok *> l) r -[ tm ]->*
  carryCfg (tokL M_tok *> l) r.
Proof.
  solve_wstep 7
    (mkCCfg A 1%sym [0; 1; 1; 1]%sym [1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma carry_PTU (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  carryCfg (tokL Z_tok *> l) (tokR P_tok *> r).
Proof.
  solve_wstep 30
    (mkCCfg D 1%sym [0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma turn_PTMT (l r : side) :
  carryCfg (tokL T_tok *> tokL M_tok *> tokL T_tok *> tokL P_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL U_tok *> tokL M_tok *> l) r.
Proof.
  solve_wstep 175
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTT (l r : side) :
  carryCfg (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r0Cfg (tokL P_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 175
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTTTM (l r : side) :
  carryCfg (tokL M_tok *> tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  r1Cfg (tokL Z_tok *> tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 155
    (mkCCfg D 1%sym [0; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma turn_ZTU_halt (l r : side) :
  carryCfg (tokL U_tok *> tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->*
  (F, ([1; 0; 1; 1; 0; 1; 1; 1]%sym *> l, 1%sym, [0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym *> r)).
Proof.
  solve_wstep 34
    (mkCCfg D 1%sym [0; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg F 1%sym [1; 0; 1; 1; 0; 1; 1; 1]%sym [0; 0; 1; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma r0_Z (l r : side) :
  r0Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_P (l r : side) :
  r0Cfg l (tokR P_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 52
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r0_PTTTM_TAIL (l r : side) :
  r0Cfg l (tokR PTTTM_TAIL_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 15
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_Z (l r : side) :
  r1Cfg l (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_P (l r : side) :
  r1Cfg l (tokR P_tok *> r) -[ tm ]->* r1OddCfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 74
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShort_Z (l r : side) :
  r1OddShortCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddShortCfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 12
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_P (l r : side) :
  r1OddCfg l (tokR P_tok *> r) -[ tm ]->* r1Cfg (tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_start (l : side) :
  cfgR l -[ tm ]->* wSweepCfg l 0inf.
Proof.
  solve_rcstep 2
    (mkCCfg D 0%sym [1; 1]%sym []%sym)
    (mkCCfg A 1%sym []%sym [1]%sym) l.
Qed.

Lemma wSweep_step (l r : side) :
  wSweepCfg (tokL W_tok *> l) r -[ tm ]->* wSweepCfg l ([0; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 6
    (mkCCfg A 1%sym [0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg A 1%sym []%sym [1; 0; 0; 1; 1]%sym) l r.
Qed.

Lemma dSweep_step (l r : side) :
  dSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL W_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 1%sym [0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma dSweep_end (l : side) :
  dSweepCfg l 0inf -[ tm ]->* cfgR (tokL W_tok *> l).
Proof.
  solve_rcstep 5
    (mkCCfg E 1%sym [0; 1; 1]%sym []%sym)
    (mkCCfg D 0%sym [1; 1; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma tSweep_step (l r : side) :
  tSweepCfg l ([0; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 26
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym [0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma tSweep_end (l : side) :
  tSweepCfg l 0inf -[ tm ]->* cfgR (tokL Z_tok *> l).
Proof.
  solve_rcstep 2
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg D 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l.
Qed.

Lemma r0_to_dSweep (l r : side) :
  r0Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1_to_dSweep (l r : side) :
  r1Cfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* dSweepCfg (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 6
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_to_tSweep (l r : side) :
  r1OddCfg l ([1; 0; 1; 1]%sym *> r) -[ tm ]->* tSweepCfg (tokL Z_tok *> tokL Z_tok *> l) r.
Proof.
  solve_wstep 10
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_Z_to_dSweep (l r : side) :
  wSweepCfg (tokL Z_tok *> l) r -[ tm ]->* dSweepCfg (tokL T_tok *> l) r.
Proof.
  solve_wstep 13
    (mkCCfg A 1%sym [0; 0; 0; 0; 1; 1]%sym [1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_ZT_to_dSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  dSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 57
    (mkCCfg A 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 1%sym [0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma wSweep_PT_to_carry (l r : side) :
  wSweepCfg (tokL T_tok *> tokL P_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  carryCfg l ([1; 0; 1; 1]%sym *> r).
Proof.
  solve_wstep 46
    (mkCCfg A 1%sym [0; 1; 1; 1; 0; 1; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1]%sym) l r.
Qed.

Lemma wSweep_ZMT_to_tSweep (l r : side) :
  wSweepCfg (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) ([0; 0; 1; 1]%sym *> r) -[ tm ]->*
  tSweepCfg (tokL Z_tok *> tokL P_tok *> l) r.
Proof.
  solve_wstep 83
    (mkCCfg A 1%sym [0; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 0; 1; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma cfgR_Z_to_TW (l : side) :
  cfgR (tokL Z_tok *> l) -[ tm ]->* cfgR (tokL W_tok *> tokL T_tok *> l).
Proof.
  solve_rcstep 20
    (mkCCfg D 0%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym []%sym)
    (mkCCfg D 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l.
Qed.

Lemma cfgR_TW_to_t3Cfg (l : side) :
  cfgR (tokL W_tok *> tokL T_tok *> l) -[ tm ]->* t3Cfg l (evalWK 0%N).
Proof.
  solve_rcstep 32
    (mkCCfg D 0%sym [1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym) l.
Qed.

Lemma t3_step (l r : side) :
  t3Cfg (npow (tokL T_tok) 3%N *> l) r -[ tm ]->* t3Cfg l (npow (tokR Z_tok) 2%N *> r).
Proof.
  solve_wstep 72
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 1]%sym) l r.
Qed.

Lemma t3Cfg_Z_zero_to_carry (l : side) :
  t3Cfg (tokL Z_tok *> l) (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 130
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_Z_succ_to_r0 (l r : side) :
  t3Cfg (tokL Z_tok *> l) (tokR Z_tok *> r) -[ tm ]->* r0Cfg (tokL P_tok *> l) r.
Proof.
  solve_wstep 39
    (mkCCfg D 1%sym [0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1]%sym []%sym) l r.
Qed.

Lemma t3Cfg_TZ_to_r1OddShort (l r : side) :
  t3Cfg (tokL T_tok *> tokL Z_tok *> l) r -[ tm ]->* r1OddShortCfg (tokL M_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 57
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1OddShortCfg_evalWK0_to_carry (l : side) :
  r1OddShortCfg l (evalWK 0%N) -[ tm ]->* carryCfg l (evalWK 1%N).
Proof.
  solve_rcstep 194
    (mkCCfg D 1%sym [1; 1; 0; 0; 0; 0; 1; 1]%sym [1; 0; 1; 1]%sym)
    (mkCCfg D 1%sym []%sym [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym) l.
Qed.

Lemma t3Cfg_TTZ_to_r0 (l r : side) :
  t3Cfg (npow (tokL T_tok) 2%N *> tokL Z_tok *> l) r -[ tm ]->* r0Cfg (tokL W_tok *> tokL T_tok *> l) r.
Proof.
  solve_wstep 85
    (mkCCfg D 1%sym [0; 1; 1; 1; 0; 1; 1; 1; 0; 0; 0; 0; 1; 1]%sym [0; 1; 0; 0; 1]%sym)
    (mkCCfg E 0%sym [0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 1; 1; 1]%sym []%sym) l r.
Qed.

Lemma r1Odd_Z (l r : side) :
  r1OddCfg l (tokR Z_tok *> r) -[ tm ]->* r1OddCfg (tokL Z_tok *> l) r.
Proof.
  exact (r1OddShort_Z (tokL Z_tok *> l) r).
Qed.

Lemma wSweep_loop : forall (n : N) (l r : side),
  wSweepCfg (npow (tokL W_tok) n *> l) r -[ tm ]->*
  wSweepCfg l (npow [0; 0; 1; 1]%sym n *> r).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply wSweep_step|].
    rewrite (npow_succ_r [0; 0; 1; 1]%sym n), Str_app_assoc.
    apply ih.
Qed.

Lemma dSweep_loop : forall (n : N) (l r : side),
  dSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  dSweepCfg (npow (tokL W_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply dSweep_step|].
    rewrite (npow_succ_r (tokL W_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma tSweep_loop : forall (n : N) (l r : side),
  tSweepCfg l (npow [0; 0; 1; 1]%sym n *> r) -[ tm ]->*
  tSweepCfg (npow (tokL T_tok) n *> l) r.
Proof.
  induction n as [|n ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply tSweep_step|].
    rewrite (npow_succ_r (tokL T_tok) n), Str_app_assoc.
    apply ih.
Qed.

Lemma t3_loop : forall (q : N) (l r : side),
  t3Cfg (npow (tokL T_tok) (3 * q)%N *> l) r -[ tm ]->*
  t3Cfg l (npow (tokR Z_tok) (2 * q)%N *> r).
Proof.
  induction q as [|q ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - replace (3 * (q + 1))%N with (3 + 3 * q)%N by lia.
    replace (2 * (q + 1))%N with (2 * q + 2)%N by lia.
    rewrite (npow_add (tokL T_tok) 3%N (3 * q)%N), Str_app_assoc.
    eapply evstep_trans; [apply t3_step|].
    rewrite (npow_add (tokR Z_tok) (2 * q)%N 2%N), Str_app_assoc.
    apply ih.
Qed.

Lemma pmu_loop : forall (m : N) (l r : side),
  pmuCfg (npow (tokL P_tok) m *> l) r -[ tm ]->*
  pmuCfg l (npow (tokR Z_tok) m *> r).
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply pmu_step|].
    rewrite (npow_succ_r (tokR Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_Z_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r0_P_loop : forall (m : N) (l r : side),
  r0Cfg l (npow (tokR P_tok) m *> r) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r0_P|].
    rewrite (npow_succ_r (tokL P_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma r1OddShort_Z_loop : forall (m : N) (l r : side),
  r1OddShortCfg l (npow (tokR Z_tok) m *> r) -[ tm ]->*
  r1OddShortCfg (npow (tokL Z_tok) m *> l) r.
Proof.
  induction m as [|m ih] using N_peano_ind; intros l r.
  - cbn; apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply evstep_trans; [apply r1OddShort_Z|].
    rewrite (npow_succ_r (tokL Z_tok) m), Str_app_assoc.
    apply ih.
Qed.

Lemma cfgR_ZW_to_TW (n : N) (l : side) :
  cfgR (npow (tokL W_tok) n *> tokL Z_tok *> l) -[ tm ]->*
  cfgR (npow (tokL W_tok) (n + 1)%N *> tokL T_tok *> l).
Proof.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop n (tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply wSweep_Z_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop n (tokL T_tok *> l) 0inf)|].
  rewrite npow_succ_l, Str_app_assoc.
  apply dSweep_end.
Qed.

Lemma r0_end (k1 : N) (l : side) :
  r0Cfg l (evalWK k1) -[ tm ]->* carryCfg l (evalWK (k1 + 2)%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r0_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop k1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 1)%N (tokL Z_tok *> l))|].
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 2)%N (tokL T_tok *> tokL Z_tok *> l) 0inf)|].
  replace (k1 + 2)%N with ((k1 + 1) + 1)%N at 1 by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZT_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop (k1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  replace (k1 + 1 + 1)%N with (k1 + 2)%N by lia.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (k1 + 2)%N (tokL P_tok *> l))|].
  replace (k1 + 2 + 1)%N with (k1 + 3)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (k1 + 3)%N (tokL T_tok *> tokL P_tok *> l) 0inf)|].
  replace (k1 + 3)%N with ((k1 + 2) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (k1 + 2)%N), Str_app_assoc.
  unfold evalWK; apply wSweep_PT_to_carry.
Qed.

Lemma r1_end (kf1 : N) (l : side) :
  r1Cfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) (kf1 + 1)%N *> tokL Z_tok *> tokL P_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1_to_dSweep|].
  eapply evstep_trans; [apply (dSweep_loop kf1 (tokL Z_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply dSweep_end|].
  rewrite <- Str_app_assoc, <- npow_succ_l.
  eapply evstep_trans; [apply (cfgR_ZW_to_TW (kf1 + 1)%N (tokL M_tok *> tokL Z_tok *> l))|].
  replace (kf1 + 1 + 1)%N with (kf1 + 2)%N by lia.
  eapply evstep_trans; [apply wSweep_start|].
  eapply evstep_trans; [apply (wSweep_loop (kf1 + 2)%N (tokL T_tok *> tokL M_tok *> tokL Z_tok *> l) 0inf)|].
  replace (kf1 + 2)%N with ((kf1 + 1) + 1)%N by lia.
  rewrite (npow_succ_l [0; 0; 1; 1]%sym (kf1 + 1)%N), Str_app_assoc.
  eapply evstep_trans; [apply wSweep_ZMT_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop (kf1 + 1)%N (tokL Z_tok *> tokL P_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Lemma r1Odd_end (kf1 : N) (l : side) :
  r1OddCfg l (evalWK kf1) -[ tm ]->*
  t3Cfg (npow (tokL T_tok) kf1 *> tokL Z_tok *> tokL Z_tok *> l) (evalWK 0%N).
Proof.
  unfold evalWK at 1.
  eapply evstep_trans; [apply r1Odd_to_tSweep|].
  eapply evstep_trans; [apply (tSweep_loop kf1 (tokL Z_tok *> tokL Z_tok *> l) 0inf)|].
  eapply evstep_trans; [apply tSweep_end|].
  eapply evstep_trans; [apply cfgR_Z_to_TW|].
  apply cfgR_TW_to_t3Cfg.
Qed.

Definition stepZtToCarry (rle2 : Rle) (n : N) : Rle * N :=
  let q := (n / 3)%N in
  let rem := (n mod 3)%N in
  if (rem =? 0)%N then
    if (q =? 0)%N then (rle2, 1%N)
    else (pushRle [Z_tok] (2 * q - 1)%N (pushRlePos [P_tok] 1%N rle2), 2%N)
  else if (rem =? 1)%N then
    (pushRle [Z_tok] (2 * q)%N (pushToksLtr [T_tok; M_tok] rle2), 1%N)
  else
    (pushRle [Z_tok] (2 * q)%N (pushToksLtr [T_tok; W_tok] rle2), 2%N).

Lemma stepZtToCarry_sound (rle2 : Rle) (n : N) :
  t3Cfg (npow (tokL T_tok) n *> tokL Z_tok *> evalRle rle2) (evalWK 0%N) -[ tm ]->*
  carryCfg (evalRle (fst (stepZtToCarry rle2 n))) (evalWK (snd (stepZtToCarry rle2 n))).
Proof.
  unfold stepZtToCarry; cbn zeta.
  pose proof (N.div_mod n 3 ltac:(discriminate)) as Hdiv.
  pose proof (N.mod_upper_bound n 3 ltac:(discriminate)) as Hmod.
  set (q := (n / 3)%N) in *.
  set (rem := (n mod 3)%N) in *.
  replace n with (3 * q + rem)%N at 1 by lia.
  rewrite (npow_add (tokL T_tok) (3 * q)%N rem), Str_app_assoc.
  eapply evstep_trans; [apply (t3_loop q (npow (tokL T_tok) rem *> tokL Z_tok *> evalRle rle2) (evalWK 0%N))|].
  assert (Hrem : rem = 0%N \/ rem = 1%N \/ rem = 2%N) by lia.
  destruct Hrem as [Hrem | [Hrem | Hrem]]; rewrite Hrem; cbn [N.eqb Pos.eqb fst snd].
  - rewrite npow_0; cbn [Str_app].
    destruct (q =? 0)%N eqn:Hq0; cbn [fst snd].
    + apply N.eqb_eq in Hq0; rewrite Hq0.
      cbn [N.mul npow Str_app].
      apply t3Cfg_Z_zero_to_carry.
    + apply N.eqb_neq in Hq0.
      replace (2 * q)%N with (1 + (2 * q - 1))%N at 1 by lia.
      rewrite (npow_add (tokR Z_tok) 1%N (2 * q - 1)%N), npow_1, Str_app_assoc.
      eapply evstep_trans; [apply t3Cfg_Z_succ_to_r0|].
      eapply evstep_trans; [apply (r0_Z_loop (2 * q - 1)%N (tokL P_tok *> evalRle rle2) (evalWK 0%N))|].
      rewrite evalRle_pushRle, evalRle_pushRlePos_one; cbn [wordL]; rewrite app_nil_r.
      apply (r0_end 0%N).
  - rewrite npow_1.
    eapply evstep_trans; [apply t3Cfg_TZ_to_r1OddShort|].
    eapply evstep_trans; [apply (r1OddShort_Z_loop (2 * q)%N (tokL M_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply r1OddShortCfg_evalWK0_to_carry.
  - rewrite npow_2, Str_app_assoc.
    eapply evstep_trans; [apply t3Cfg_TTZ_to_r0|].
    eapply evstep_trans; [apply (r0_Z_loop (2 * q)%N (tokL W_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply (r0_end 0%N).
Qed.

Local Opaque stepZtToCarry.

Lemma carry_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (wordL w *> l) r -[ tm ]->*
  carryCfg l (wordR (revWord w) *> r).
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordL revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply carry_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply carry_P | apply (ih _ _ hts)].
Qed.

Lemma carry_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  carryCfg (npow (wordL w) c *> l) r -[ tm ]->*
  carryCfg l (npow (wordR (revWord w)) c *> r).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordL w) c), Str_app_assoc.
    eapply evstep_trans; [apply (carry_word w _ _ hw)|].
    rewrite (npow_succ_r (wordR (revWord w)) c), Str_app_assoc.
    apply (ih w l _ hw).
Qed.

Notation popCarrySpecial := TM1.popCarrySpecial.

Lemma popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : side)
  (h : popCarrySpecial rle rs = Some (rle', rs')) :
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle rle') (evalRStack rs' r_end).
Proof.
  unfold popCarrySpecial in h.
  destruct (popLastTok rle) as [[t1 r1]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound rle t1 r1 Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popLastTok r1) as [[t2 r2]|] eqn:Hp2; [|discriminate].
    rewrite (popLastTok_sound r1 t2 r2 Hp2).
    destruct t2; try discriminate.
    +  
      pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2)) as Hpcs.
      destruct (popTokCount 8 P_tok 0%N r2) as [mVal r3] eqn:Hpc.
      cbn [fst snd] in Hpcs; rewrite npow_0 in Hpcs; cbn [Str_app] in Hpcs.
      rewrite Hpcs.
      destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
      destruct (popLastTok r3) as [[t3 r4]|] eqn:Hp3; [|discriminate].
      rewrite (popLastTok_sound r3 t3 r4 Hp3).
      destruct t3; try discriminate; inverts h.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL M_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_M_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL T_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_T_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
    +  
      destruct (popTok P_tok r2) as [r3|] eqn:Hp3; [|discriminate].
      inverts h.
      rewrite (popTok_sound P_tok r2 r3 Hp3).
      rewrite evalRle_pushRlePos_one, evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite !app_nil_r.
      apply carry_PTU.
  -  
    destruct (popToks [T_tok; U_tok; M_tok; P_tok] r1) as [r5|] eqn:Hp2.
    + rewrite (popToks_sound _ r1 r5 Hp2).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PMUTM.
    + destruct (popToks [T_tok; T_tok; T_tok; P_tok] r1) as [r5|] eqn:Hp3; [|discriminate].
      rewrite (popToks_sound _ r1 r5 Hp3).
      cbn [wordL app]; rewrite ?Str_app_assoc.
      change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r5)
        with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r5).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PTTTM.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 2%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTW.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos, npow_1.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTT.
Qed.

Local Opaque popCarrySpecial.

Notation popCarryLoop := TM1.popCarryLoop.

Lemma popCarryLoop_sound : forall (fuel : nat) (rle rs : Rle) (r_end : side),
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->*
  carryCfg (evalRle (fst (popCarryLoop fuel rle rs))) (evalRStack (snd (popCarryLoop fuel rle rs)) r_end).
Proof.
  induction fuel as [|fuel ih]; intros rle rs r_end; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  destruct rle as [|[w c] rest]; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  cbn [popCarryLoop].
  destruct (isZpWord w) eqn:Hw.
  - cbn [evalRle].
    eapply evstep_trans; [apply (carry_pow c w (evalRle rest) (evalRStack rs r_end) Hw)|].
    rewrite <- (evalRStack_pushRlePos w c rs r_end).
    apply ih.
  - destruct (popCarrySpecial ((w, c) :: rest) rs) as [[rle' rs']|] eqn:Hsp.
    + eapply evstep_trans; [apply (popCarrySpecial_sound _ _ _ _ r_end Hsp)|].
      apply ih.
    + cbn [fst snd]; apply evstep_refl.
Qed.

Local Opaque popCarryLoop.

Lemma r0_word : forall (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (wordR w *> r) -[ tm ]->*
  r0Cfg (wordL (revWord w) *> l) r.
Proof.
  induction w as [|t ts ih]; intros l r hw.
  - cbn; apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    destruct t; try discriminate;
    cbn [wordR revWord]; rewrite wordL_append; cbn [wordL]; rewrite app_nil_r, !Str_app_assoc.
    + eapply evstep_trans; [apply r0_Z | apply (ih _ _ hts)].
    + eapply evstep_trans; [apply r0_P | apply (ih _ _ hts)].
Qed.

Lemma r0_pow : forall (c : N) (w : list Tok) (l r : side),
  isZpWord w = true ->
  r0Cfg l (npow (wordR w) c *> r) -[ tm ]->*
  r0Cfg (npow (wordL (revWord w)) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w l r hw.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR w) c), Str_app_assoc.
    eapply evstep_trans; [apply (r0_word w _ _ hw)|].
    rewrite (npow_succ_r (wordL (revWord w)) c), Str_app_assoc.
    apply (ih w _ _ hw).
Qed.

Notation allZpStack := TM1.allZpStack.

Notation copyRStack := TM1.copyRStack.

Lemma copyRStack_sound : forall (rs : Rle) (rle rle' : Rle) (r_end : side),
  copyRStack rle rs = Some rle' ->
  allZpStack rs = true /\
  r0Cfg (evalRle rle) (evalRStack rs r_end) -[ tm ]->* r0Cfg (evalRle rle') r_end.
Proof.
  induction rs as [|[w c] rest ih]; intros rle rle' r_end h; cbn [copyRStack] in h.
  - inverts h; cbn [allZpStack evalRStack]; split; [reflexivity | apply evstep_refl].
  - destruct (isZpWord w) eqn:Hw; [|discriminate].
    destruct (ih (pushRlePos w c rle) rle' r_end h) as [Hrest Hstep].
    cbn [allZpStack]; rewrite Hw, Hrest; split; [reflexivity|].
    cbn [evalRStack].
    assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact Hw).
    eapply evstep_trans; [apply (r0_pow c (revWord w) (evalRle rle) (evalRStack rest r_end) Hrev)|].
    rewrite revWord_revWord, <- evalRle_pushRlePos.
    exact Hstep.
Qed.

Definition HasRoundtrip (R : N -> side) : Prop :=
  forall (l : side) (k1 : N),
    r0Cfg l (R k1) -[ tm ]->* carryCfg l (R (k1 + 2)%N).

Lemma hasRoundtrip_evalWK : HasRoundtrip evalWK.
Proof.
  intros l k1. exact (r0_end k1 l).
Qed.

Lemma hasRoundtrip_Z (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR Z_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_Z|].
  eapply evstep_trans; [apply (hR (tokL Z_tok *> l) k1)|].
  apply carry_Z.
Qed.

Lemma hasRoundtrip_P (R : N -> side) (hR : HasRoundtrip R) :
  HasRoundtrip (fun k1 => tokR P_tok *> R k1).
Proof.
  intros l k1.
  eapply evstep_trans; [apply r0_P|].
  eapply evstep_trans; [apply (hR (tokL P_tok *> l) k1)|].
  apply carry_P.
Qed.

Lemma hasRoundtrip_word : forall (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => wordR w *> R k1).
Proof.
  induction w as [|t ts ih]; intros R hw hR; [exact hR|].
  cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
  destruct t; try discriminate; intros l k1; cbn [wordR]; rewrite Str_app_assoc.
  - exact (hasRoundtrip_Z _ (ih R hts hR) l k1).
  - exact (hasRoundtrip_P _ (ih R hts hR) l k1).
Qed.

Lemma hasRoundtrip_pow : forall (c : N) (w : list Tok) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => npow (wordR w) c *> R k1).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w R hw hR; [exact hR|].
  intros l k1.
  rewrite (npow_succ_l (wordR w) c), !Str_app_assoc.
  exact (hasRoundtrip_word w _ hw (ih w R hw hR) l k1).
Qed.

Lemma hasRoundtrip_stack : forall (rs : Rle) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  HasRoundtrip (fun k1 => evalRStack rs (R k1)).
Proof.
  induction rs as [|[w c] rest ih]; intros R hrs hR; [exact hR|].
  cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hw hrest].
  intros l k1; cbn [evalRStack].
  assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
  exact (hasRoundtrip_pow c (revWord w) _ Hrev (ih R hrest hR) l k1).
Qed.

Definition r1PhaseCfg (phase : bool) (l r : side) : Q * tape :=
  if phase then r1OddCfg l r else r1Cfg l r.

Notation stepR1StarWordL := TM1.stepR1StarWordL.

Notation r1_out := TM1.r1_out.

Notation r1_res := TM1.r1_res.

Notation r1_phase := TM1.r1_phase.

Notation stepR1StarWordL_phase_inv := TM1.stepR1StarWordL_phase_inv.

Lemma stepR1StarWordL_sound : forall (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true -> HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (wordR (revWord w) *> R k1) -[ tm ]->*
    r1PhaseCfg (r1_phase (stepR1StarWordL w phase))
      (wordL (r1_out (stepR1StarWordL w phase)) *> l)
      (R (k1 + 2 * r1_res (stepR1StarWordL w phase))%N).
Proof.
  induction w as [|t ts ih]; intros phase l R hw hR k1.
  - cbn [stepR1StarWordL r1_phase r1_out r1_res revWord wordR wordL fst snd].
    replace (k1 + 2 * 0)%N with k1 by lia.
    apply evstep_refl.
  - cbn [isZpWord] in hw; apply andb_true_iff in hw; destruct hw as [ht hts].
    assert (hRt : HasRoundtrip (fun k => tokR t *> R k)).
    { destruct t; try discriminate; [exact (hasRoundtrip_Z R hR) | exact (hasRoundtrip_P R hR)]. }
    pose proof (ih phase l (fun k => tokR t *> R k) hts hRt k1) as Hih.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [exact Hih|].
    cbn [stepR1StarWordL].
    destruct (stepR1StarWordL ts phase) as [[out res] p1] eqn:Hs.
    unfold r1_phase, r1_out, r1_res; cbn [fst snd].
    destruct t; try discriminate; destruct p1; cbn [tokEq r1PhaseCfg r1_phase r1_out r1_res fst snd wordL];
    rewrite ?Str_app_assoc.
    +  
      apply r1Odd_Z.
    +  
      eapply evstep_trans; [apply r1_Z|].
      eapply evstep_trans; [apply (hR (tokL M_tok *> tokL Z_tok *> wordL out *> l) (k1 + 2 * res)%N)|].
      replace (k1 + 2 * res + 2)%N with (k1 + 2 * (res + 1))%N by lia.
      apply turn_ZM.
    +  
      apply r1Odd_P.
    +  
      apply r1_P.
Qed.

Lemma stepR1Star_same_pow : forall (c : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w phase) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    r1PhaseCfg phase l (npow (wordR (revWord w)) c *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out (stepR1StarWordL w phase))) c *> l)
      (R (k1 + 2 * (c * r1_res (stepR1StarWordL w phase)))%N).
Proof.
  induction c as [|c ih] using N_peano_ind; intros w phase l R hw hsame hR k1.
  - cbn [npow Str_app]; replace (k1 + 2 * (0 * r1_res (stepR1StarWordL w phase)))%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    pose proof (hasRoundtrip_pow c (revWord w) R Hrev hR) as hR'.
    rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    pose proof (stepR1StarWordL_sound w phase l _ hw hR' k1) as H1.
    rewrite hsame in H1.
    eapply evstep_trans; [exact H1|].
    pose proof (ih w phase (wordL (r1_out (stepR1StarWordL w phase)) *> l) R hw hsame hR
      (k1 + 2 * r1_res (stepR1StarWordL w phase))%N) as Hih.
    replace (k1 + 2 * r1_res (stepR1StarWordL w phase) + 2 * (c * r1_res (stepR1StarWordL w phase)))%N
      with (k1 + 2 * ((c + 1) * r1_res (stepR1StarWordL w phase)))%N in Hih by lia.
    rewrite (npow_succ_r (wordL (r1_out (stepR1StarWordL w phase))) c), Str_app_assoc.
    exact Hih.
Qed.

Lemma stepR1Star_alt_pow : forall (q : N) (w : list Tok) (phase : bool) (l : side) (R : N -> side),
  isZpWord w = true ->
  r1_phase (stepR1StarWordL w (r1_phase (stepR1StarWordL w phase))) = phase ->
  HasRoundtrip R ->
  forall (k1 : N),
    let s1 := stepR1StarWordL w phase in
    let s2 := stepR1StarWordL w (r1_phase s1) in
    r1PhaseCfg phase l (npow (wordR (revWord w)) (2 * q)%N *> R k1) -[ tm ]->*
    r1PhaseCfg phase (npow (wordL (r1_out s2 ++ r1_out s1)) q *> l)
      (R (k1 + 2 * (q * (r1_res s1 + r1_res s2)))%N).
Proof.
  induction q as [|q ih] using N_peano_ind; intros w phase l R hw halt hR k1 s1 s2.
  - cbn [N.mul npow Str_app]; replace (k1 + 0)%N with k1 by lia.
    apply evstep_refl.
  - assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact hw).
    replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    pose proof (hasRoundtrip_pow (2 * q)%N (revWord w) R Hrev hR) as hR2.
    pose proof (hasRoundtrip_word (revWord w) _ Hrev hR2) as hR1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w phase l _ hw hR1 k1)|].
    fold s1.
    eapply evstep_trans; [apply (stepR1StarWordL_sound w (r1_phase s1) (wordL (r1_out s1) *> l) _ hw hR2 (k1 + 2 * r1_res s1)%N)|].
    fold s2.
    fold s1 in halt; fold s2 in halt; rewrite halt.
    pose proof (ih w phase (wordL (r1_out s2 ++ r1_out s1) *> l) R hw halt hR
      (k1 + 2 * r1_res s1 + 2 * r1_res s2)%N) as Hih.
    cbn zeta in Hih; fold s1 in Hih; fold s2 in Hih.
    replace (k1 + 2 * r1_res s1 + 2 * r1_res s2 + 2 * (q * (r1_res s1 + r1_res s2)))%N
      with (k1 + 2 * ((q + 1) * (r1_res s1 + r1_res s2)))%N in Hih by lia.
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (r1_out s2 ++ r1_out s1)) q), Str_app_assoc.
    exact Hih.
Qed.

Fixpoint sweepStarLoop (rle : Rle) (phase : bool) (totalRes : N) (rs : Rle) : Rle * bool * N :=
  match rs with
  | [] => (rle, phase, totalRes)
  | (item, count) :: rest =>
    let s1 := stepR1StarWordL item phase in
    let out1 := r1_out s1 in
    let res1 := r1_res s1 in
    let nextPhase := r1_phase s1 in
    if Bool.eqb nextPhase phase then
      sweepStarLoop (pushRlePos out1 count rle) phase (totalRes + count * res1)%N rest
    else
      let s2 := stepR1StarWordL item nextPhase in
      let out2 := r1_out s2 in
      let res2 := r1_res s2 in
      let q := (count / 2)%N in
      let rem := (count mod 2)%N in
      let rle1 := pushRle (out2 ++ out1) q rle in
      let resAfterQ := (totalRes + q * (res1 + res2))%N in
      if (rem =? 1)%N then
        sweepStarLoop (pushRlePos out1 1%N rle1) nextPhase (resAfterQ + res1)%N rest
      else
        sweepStarLoop rle1 phase resAfterQ rest
  end.

Lemma sweepStarLoop_sound : forall (rs : Rle) (rle : Rle) (phase : bool) (totalRes : N) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  forall (k1 : N),
    let res := sweepStarLoop rle phase totalRes rs in
    r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)%N)) -[ tm ]->*
    r1PhaseCfg (snd (fst res)) (evalRle (fst (fst res))) (R (k1 + 2 * snd res)%N).
Proof.
  induction rs as [|[item count] rest ih]; intros rle phase totalRes R hrs hR k1 res.
  - unfold res; cbn [sweepStarLoop evalRStack fst snd]; apply evstep_refl.
  - cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hitem hrest].
    assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact hitem).
    pose proof (hasRoundtrip_stack rest R hrest hR) as hR_rest.
    unfold res; cbn [sweepStarLoop evalRStack].
    set (s1 := stepR1StarWordL item phase).
    destruct (Bool.eqb (r1_phase s1) phase) eqn:Hsame.
    + apply Bool.eqb_prop in Hsame.
      eapply evstep_trans.
      * apply (stepR1Star_same_pow count item phase (evalRle rle) _ hitem Hsame hR_rest (k1 + 2 * totalRes)%N).
      * fold s1.
        replace (k1 + 2 * totalRes + 2 * (count * r1_res s1))%N
          with (k1 + 2 * (totalRes + count * r1_res s1))%N by lia.
        rewrite <- evalRle_pushRlePos.
        apply (ih (pushRlePos (r1_out s1) count rle) phase (totalRes + count * r1_res s1)%N R hrest hR k1).
    + assert (Hnot : r1_phase s1 = negb phase).
      { destruct (r1_phase s1), phase; cbn in Hsame; try discriminate; reflexivity. }
      assert (Halt : r1_phase (stepR1StarWordL item (r1_phase s1)) = phase).
      { rewrite Hnot, (stepR1StarWordL_phase_inv item phase hitem).
        fold s1; rewrite Hnot, Bool.negb_involutive; reflexivity. }
      set (s2 := stepR1StarWordL item (r1_phase s1)).
      cbn zeta.
      pose proof (N.div_mod count 2 ltac:(discriminate)) as Hdiv.
      pose proof (N.mod_upper_bound count 2 ltac:(discriminate)) as Hmod.
      set (q := (count / 2)%N) in *.
      set (rem := (count mod 2)%N) in *.
      replace count with (2 * q + rem)%N at 1 by lia.
      rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
      pose proof (hasRoundtrip_pow rem (revWord item) _ Hrev hR_rest) as hR_rem.
      eapply evstep_trans.
      * apply (stepR1Star_alt_pow q item phase (evalRle rle) _ hitem Halt hR_rem (k1 + 2 * totalRes)%N).
      * fold s1; fold s2.
        rewrite <- evalRle_pushRle.
        replace (k1 + 2 * totalRes + 2 * (q * (r1_res s1 + r1_res s2)))%N
          with (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)))%N by lia.
        assert (Hrem : rem = 0%N \/ rem = 1%N) by lia.
        destruct Hrem as [Hrem | Hrem]; rewrite Hrem; cbn [N.eqb Pos.eqb].
        -- rewrite npow_0; cbn [Str_app].
           apply (ih _ phase _ R hrest hR k1).
        -- rewrite npow_1.
           eapply evstep_trans.
           ++ apply (stepR1StarWordL_sound item phase _ _ hitem hR_rest
                (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)))%N).
           ++ fold s1.
              rewrite <- evalRle_pushRlePos_one.
              replace (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)) + 2 * r1_res s1)%N
                with (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2) + r1_res s1))%N by lia.
              apply (ih _ (r1_phase s1) _ R hrest hR k1).
Qed.

Definition modeCfg (mode : Mode) (l r : side) : Q * tape :=
  match mode with
  | R0_mode => r0Cfg l r
  | R1_mode => r1Cfg l r
  | R1_ODD_mode => r1OddCfg l r
  end.

Notation stepOneTokPure := TM1.stepOneTokPure.

Lemma stepOneTokPure_sound (mode mode' : Mode) (t : Tok) (toks : list Tok) (l r : side)
  (h : stepOneTokPure mode t = Some (toks, mode')) :
  modeCfg mode l (tokR t *> r) -[ tm ]->* modeCfg mode' (wordL toks *> l) r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg wordL app]; rewrite ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Notation stepOneWordPureL := TM1.stepOneWordPureL.

Lemma stepOneWordPureL_sound : forall (w : list Tok) (mode mode' : Mode) (out : list Tok) (l r : side),
  stepOneWordPureL mode w = Some (out, mode') ->
  modeCfg mode l (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (wordL out *> l) r.
Proof.
  induction w as [|t ts ih]; intros mode mode' out l r h; cbn [stepOneWordPureL] in h.
  - inverts h; cbn [revWord wordR wordL Str_app]; apply evstep_refl.
  - destruct (stepOneWordPureL mode ts) as [[outRest mode1]|] eqn:H1; [|discriminate].
    destruct (stepOneTokPure mode1 t) as [[toks mode2]|] eqn:H2; [|discriminate].
    inverts h.
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih mode mode1 outRest l (tokR t *> r) H1)|].
    eapply evstep_trans; [apply (stepOneTokPure_sound mode1 mode' t toks (wordL outRest *> l) r H2)|].
    rewrite wordL_append, Str_app_assoc. apply evstep_refl.
Qed.

Lemma stepOneWordPureL_same_pow : forall (c : N) (w out : list Tok) (mode : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) c *> r) -[ tm ]->*
  modeCfg mode (npow (wordL out) c *> l) r.
Proof.
  induction c as [|c ih] using N_peano_ind; intros w out mode l r h.
  - cbn; apply evstep_refl.
  - rewrite (npow_succ_l (wordR (revWord w)) c), Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode out l _ h)|].
    rewrite (npow_succ_r (wordL out) c), Str_app_assoc.
    apply (ih w out mode _ r h).
Qed.

Lemma stepOneWordPureL_alt_pow : forall (q : N) (w out1 out2 : list Tok) (mode mode1 : Mode) (l r : side),
  stepOneWordPureL mode w = Some (out1, mode1) ->
  stepOneWordPureL mode1 w = Some (out2, mode) ->
  modeCfg mode l (npow (wordR (revWord w)) (2 * q)%N *> r) -[ tm ]->*
  modeCfg mode (npow (wordL (out2 ++ out1)) q *> l) r.
Proof.
  induction q as [|q ih] using N_peano_ind; intros w out1 out2 mode mode1 l r h1 h2.
  - cbn; apply evstep_refl.
  - replace (2 * (q + 1))%N with (1 + (1 + 2 * q))%N by lia.
    rewrite (npow_add (wordR (revWord w)) 1%N (1 + 2 * q)%N),
            (npow_add (wordR (revWord w)) 1%N (2 * q)%N), !npow_1, !Str_app_assoc.
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode mode1 out1 l _ h1)|].
    eapply evstep_trans; [apply (stepOneWordPureL_sound w mode1 mode out2 (wordL out1 *> l) _ h2)|].
    rewrite <- Str_app_assoc, <- wordL_append.
    rewrite (npow_succ_r (wordL (out2 ++ out1)) q), Str_app_assoc.
    apply (ih w out1 out2 mode mode1 _ r h1 h2).
Qed.

Notation stepOneTokL := TM1.stepOneTokL.

Lemma stepOneTokL_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : side)
  (h : stepOneTokL rle mode t = Some (rle', mode')) :
  modeCfg mode (evalRle rle) (tokR t *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg]; rewrite ?evalRle_pushToksLtr, ?evalRle_pushRlePos_one;
  cbn [revWord wordL app]; rewrite ?app_nil_r, ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Notation stepOneWordL := TM1.stepOneWordL.

Lemma stepOneWordL_sound : forall (w : list Tok) (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneWordL rle mode w = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (wordR (revWord w) *> r) -[ tm ]->* modeCfg mode' (evalRle rle') r.
Proof.
  induction w as [|t ts ih]; intros rle rle' mode mode' r h; cbn [stepOneWordL] in h.
  - inverts h; cbn [revWord wordR Str_app]; apply evstep_refl.
  - destruct (stepOneWordL rle mode ts) as [[rle1 mode1]|] eqn:H1; [|discriminate].
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih rle rle1 mode mode1 (tokR t *> r) H1)|].
    apply (stepOneTokL_sound rle1 rle' mode1 mode' t r h).
Qed.

Fixpoint stepOneBounceFuel (fuel : nat) (item : list Tok) (count : N) (rle : Rle) (mode : Mode)
  : option (Rle * Mode) :=
  match fuel with
  | O => if (count =? 0)%N then Some (rle, mode) else None
  | S fuel' =>
    if (count =? 0)%N then Some (rle, mode)
    else if modeEq mode R0_mode then
      if isZpWord item then Some (pushRlePos item count rle, R0_mode)
      else
        match stepOneWordL rle mode item with
        | None => None
        | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
        end
    else
      match stepOneWordPureL mode item with
      | None => None
      | Some (out1, mode1) =>
        if modeEq mode1 mode then
          Some (pushRlePos out1 count rle, mode)
        else if (2 <=? count)%N then
          match stepOneWordPureL mode1 item with
          | None => None
          | Some (out2, mode2) =>
            if modeEq mode2 mode then
              let q := (count / 2)%N in
              let rem := (count mod 2)%N in
              stepOneBounceFuel fuel' item rem (pushRle (out2 ++ out1) q rle) mode
            else
              match stepOneWordL rle mode item with
              | None => None
              | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
              end
          end
        else
          match stepOneWordL rle mode item with
          | None => None
          | Some (rle', mode') => stepOneBounceFuel fuel' item (count - 1)%N rle' mode'
          end
      end
  end.

Lemma stepOneBounceFuel_sound : forall (fuel : nat) (item : list Tok) (count : N)
  (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneBounceFuel fuel item count rle mode = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (npow (wordR (revWord item)) count *> r) -[ tm ]->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction fuel as [|fuel ih]; intros item count rle rle' mode mode' r h; cbn [stepOneBounceFuel] in h.
  - destruct (count =? 0)%N eqn:Hc0; [|discriminate].
    apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
  - destruct (count =? 0)%N eqn:Hc0.
    + apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
    + apply N.eqb_neq in Hc0.
      assert (Hc_split : count = ((count - 1) + 1)%N) by lia.
      destruct (modeEq mode R0_mode) eqn:Hm0.
      * destruct (isZpWord item) eqn:Hzp.
        -- inverts h; apply modeEq_eq in Hm0; subst mode.
           cbn [modeCfg]; rewrite evalRle_pushRlePos.
           assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact Hzp).
           pose proof (r0_pow count (revWord item) (evalRle rle) r Hrev) as Hr0.
           rewrite revWord_revWord in Hr0; exact Hr0.
        -- destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
           rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
           eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
           exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
      * destruct (stepOneWordPureL mode item) as [[out1 mode1]|] eqn:Hp1; [|discriminate].
        destruct (modeEq mode1 mode) eqn:Hm1.
        -- inverts h; apply modeEq_eq in Hm1; subst mode1.
           rewrite evalRle_pushRlePos.
           exact (stepOneWordPureL_same_pow count item out1 mode' (evalRle rle) r Hp1).
        -- destruct (2 <=? count)%N eqn:Hle2.
           ++ destruct (stepOneWordPureL mode1 item) as [[out2 mode2]|] eqn:Hp2; [|discriminate].
              destruct (modeEq mode2 mode) eqn:Hm2.
              ** apply modeEq_eq in Hm2; subst mode2.
                 cbn zeta in h.
                 pose proof (N.div_mod count 2 ltac:(discriminate)) as Hdiv.
                 set (q := (count / 2)%N) in *.
                 set (rem := (count mod 2)%N) in *.
                 replace count with (2 * q + rem)%N at 1 by lia.
                 rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordPureL_alt_pow q item out1 out2 mode mode1 (evalRle rle) _ Hp1 Hp2)|].
                 rewrite <- evalRle_pushRle.
                 exact (ih item rem (pushRle (out2 ++ out1) q rle) rle' mode mode' r h).
              ** destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
                 rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
                 exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
           ++ destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
              rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
              eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
              exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
Qed.

Local Opaque stepOneBounceFuel.

Fixpoint simpleOneBounceCarry (rle : Rle) (mode : Mode) (rs : Rle) (k1 : N) : option (Rle * N) :=
  match rs with
  | [] => if modeEq mode R0_mode then Some (rle, (k1 + 2)%N) else None
  | (item, count) :: rest =>
    match stepOneBounceFuel 3 item count rle mode with
    | None => None
    | Some (rle', mode') => simpleOneBounceCarry rle' mode' rest k1
    end
  end.

Lemma simpleOneBounceCarry_sound : forall (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : N),
  simpleOneBounceCarry rle mode rs k1 = Some (rle', kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rle') (evalWK kOut).
Proof.
  induction rs as [|[item count] rest ih]; intros rle rle' mode k1 kOut h; cbn [simpleOneBounceCarry] in h.
  - destruct (modeEq mode R0_mode) eqn:Hm; [|discriminate].
    inverts h; apply modeEq_eq in Hm; subst mode; cbn [modeCfg evalRStack].
    apply r0_end.
  - destruct (stepOneBounceFuel 3 item count rle mode) as [[rle1 mode1]|] eqn:Hb; [|discriminate].
    cbn [evalRStack].
    eapply evstep_trans; [apply (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ Hb)|].
    exact (ih rle1 rle' mode1 k1 kOut h).
Qed.

Notation hasSpecialWord := TM1.hasSpecialWord.

Notation hasSpecial := TM1.hasSpecial.

Definition runRightSweepStarCarry (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : option (Rle * N) :=
  if hasSpecial rStack then
    simpleOneBounceCarry rle mode rStack k1
  else if modeEq mode R0_mode then
    match copyRStack rle rStack with
    | None => None
    | Some rle' => Some (rle', (k1 + 2)%N)
    end
  else if allZpStack rStack then
    let initPhase := negb (modeEq mode R1_mode) in
    let res := sweepStarLoop rle initPhase 0%N rStack in
    let rle1 := fst (fst res) in
    let finalPhase := snd (fst res) in
    let totalRes := snd res in
    let kFinal1 := (k1 + 2 * totalRes)%N in
    if finalPhase then
      Some (stepZtToCarry (pushRlePos [Z_tok] 1%N rle1) kFinal1)
    else
      Some (stepZtToCarry (pushRlePos [P_tok] 1%N rle1) (kFinal1 + 1)%N)
  else None.

Lemma runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : N)
  (h : runRightSweepStarCarry rle mode rStack k1 = Some (rOut, kOut)) :
  modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) -[ tm ]->*
  carryCfg (evalRle rOut) (evalWK kOut).
Proof.
  unfold runRightSweepStarCarry in h.
  destruct (hasSpecial rStack) eqn:Hs.
  - exact (simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h).
  - destruct (modeEq mode R0_mode) eqn:Hm0.
    + destruct (copyRStack rle rStack) as [rle'|] eqn:Hc; [|discriminate].
      inverts h; apply modeEq_eq in Hm0; subst mode; cbn [modeCfg].
      eapply evstep_trans; [exact (proj2 (copyRStack_sound rStack rle rOut (evalWK k1) Hc))|].
      apply r0_end.
    + destruct (allZpStack rStack) eqn:Hall; [|discriminate].
      set (initPhase := negb (modeEq mode R1_mode)) in *.
      assert (Hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
        r1PhaseCfg initPhase (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0)%N))).
      { replace (k1 + 2 * 0)%N with k1 by lia.
        destruct mode; cbn in Hm0; try discriminate; reflexivity. }
      rewrite Hphase.
      pose proof (sweepStarLoop_sound rStack rle initPhase 0%N evalWK Hall hasRoundtrip_evalWK k1) as Hsw.
      cbn zeta in Hsw, h.
      set (res := sweepStarLoop rle initPhase 0%N rStack) in *.
      eapply evstep_trans; [exact Hsw|].
      destruct (snd (fst res)) eqn:Hfp.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1Odd_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [Z_tok] 1%N (fst (fst res))) (k1 + 2 * snd res)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [P_tok] 1%N (fst (fst res))) (k1 + 2 * snd res + 1)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
Qed.

Local Opaque runRightSweepStarCarry.

Notation StepCarryRes := TM1.StepCarryRes.

Notation SCR_halt := TM1.SCR_halt.

Notation SCR_next := TM1.SCR_next.

Notation SCR_err := TM1.SCR_err.

Definition StepCarryValid (cfg : Q * tape) (res : StepCarryRes) : Prop :=
  match res with
  | SCR_halt => exists cfg', (cfg -[ tm ]->* cfg') /\ halted tm cfg'
  | SCR_next rOut kOut => cfg -[ tm ]->* carryCfg (evalRle rOut) (evalWK kOut)
  | SCR_err => False
  end.

Lemma stepCarryValid_of_stepStar (cfg1 cfg2 : Q * tape) (res : StepCarryRes)
  (hstep : cfg1 -[ tm ]->* cfg2) (hval : StepCarryValid cfg2 res) :
  StepCarryValid cfg1 res.
Proof.
  destruct res; cbn [StepCarryValid] in *.
  - destruct hval as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact hstep | exact h2] | exact hhalt].
  - eapply evstep_trans; [exact hstep | exact hval].
  - exact hval.
Qed.

Definition finishTurn (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N) : StepCarryRes :=
  match runRightSweepStarCarry rle mode rStack k1 with
  | None => SCR_err
  | Some (rOut, kOut) => SCR_next rOut kOut
  end.

Lemma finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N)
  (hne : finishTurn rle mode rStack k1 <> SCR_err) :
  StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
    (finishTurn rle mode rStack k1).
Proof.
  unfold finishTurn in *.
  destruct (runRightSweepStarCarry rle mode rStack k1) as [[rOut kOut]|] eqn:Hr.
  - cbn [StepCarryValid].
    exact (runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut Hr).
  - exfalso; apply hne; reflexivity.
Qed.

Notation matchRule2 := TM1.matchRule2.

Lemma matchRule2_sound (t1 t2 : Tok) (out : list Tok) (mode : Mode) (r4 : Rle) (r : side)
  (h : matchRule2 t1 t2 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> evalRle r4) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r4)) r.
Proof.
  destruct t1, t2; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_WM.
  - apply turn_ZM.
  - apply turn_ZT.
  - apply turn_PT.
Qed.

Notation matchRule3 := TM1.matchRule3.

Lemma matchRule3_sound (t1 t2 t3 : Tok) (out : list Tok) (mode : Mode) (r5 : Rle) (r : side)
  (h : matchRule3 t1 t2 t3 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r5)) r.
Proof.
  destruct t1, t2, t3; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMU.
  - apply turn_ZTM.
  - apply turn_PTM.
  - apply turn_ZTW.
  - apply turn_PTW.
  - apply turn_ZTT.
  - apply turn_PTT.
Qed.

Notation matchRule4 := TM1.matchRule4.

Lemma matchRule4_sound (t1 t2 t3 t4 : Tok) (out : list Tok) (mode : Mode) (r6 : Rle) (r : side)
  (h : matchRule4 t1 t2 t3 t4 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> evalRle r6) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r6)) r.
Proof.
  destruct t1, t2, t3, t4; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZPMU.
  - apply turn_ZTTM.
  - apply turn_PTTM.
  - apply turn_MUTW.
  - apply turn_ZTTW.
  - apply turn_PTMT.
  - apply turn_ZTTT.
Qed.

Notation matchRule5 := TM1.matchRule5.

Lemma matchRule5_sound (t1 t2 t3 t4 t5 : Tok) (out : list Tok) (mode : Mode) (r7 : Rle) (r : side)
  (h : matchRule5 t1 t2 t3 t4 t5 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> tokL t5 *> evalRle r7) r -[ tm ]->*
  modeCfg mode (evalRle (pushToksLtr out r7)) r.
Proof.
  destruct t1, t2, t3, t4, t5; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMUTM.
  - apply turn_ZTTTM.
  - apply turn_PTTTW.
Qed.

Notation isEmptyRle := TM1.isEmptyRle.

Notation isEmptyRle_eq := TM1.isEmptyRle_eq.

Definition stepTurnFrom3 (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N) : StepCarryRes :=
  match matchRule3 t1 t2 t3 with
  | Some (out, mode) => finishTurn (pushToksLtr out r5) mode rStack k1
  | None =>
    match popLastTok r5 with
    | None => SCR_err
    | Some (t4, r6) =>
      match matchRule4 t1 t2 t3 t4 with
      | Some (out, mode) => finishTurn (pushToksLtr out r6) mode rStack k1
      | None =>
        match popLastTok r6 with
        | None => SCR_err
        | Some (t5, r7) =>
          match matchRule5 t1 t2 t3 t4 t5 with
          | Some (out, mode) => finishTurn (pushToksLtr out r7) mode rStack k1
          | None => SCR_err
          end
        end
      end
    end
  end.

Lemma stepTurnFrom3_sound (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom3 t1 t2 t3 r5 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom3 t1 t2 t3 r5 rStack k1).
Proof.
  unfold stepTurnFrom3 in *.
  destruct (matchRule3 t1 t2 t3) as [[out mode]|] eqn:Hm3.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule3_sound t1 t2 t3 out mode r5 _ Hm3)
      (finishTurn_sound (pushToksLtr out r5) mode rStack k1 hne)).
  - destruct (popLastTok r5) as [[t4 r6]|] eqn:Hp4; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r5 t4 r6 Hp4).
    destruct (matchRule4 t1 t2 t3 t4) as [[out mode]|] eqn:Hm4.
    + exact (stepCarryValid_of_stepStar _ _ _
        (matchRule4_sound t1 t2 t3 t4 out mode r6 _ Hm4)
        (finishTurn_sound (pushToksLtr out r6) mode rStack k1 hne)).
    + destruct (popLastTok r6) as [[t5 r7]|] eqn:Hp5; [|exfalso; apply hne; reflexivity].
      rewrite (popLastTok_sound r6 t5 r7 Hp5).
      destruct (matchRule5 t1 t2 t3 t4 t5) as [[out mode]|] eqn:Hm5; [|exfalso; apply hne; reflexivity].
      exact (stepCarryValid_of_stepStar _ _ _
        (matchRule5_sound t1 t2 t3 t4 t5 out mode r7 _ Hm5)
        (finishTurn_sound (pushToksLtr out r7) mode rStack k1 hne)).
Qed.

Definition stepTurnFrom2 (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N) : StepCarryRes :=
  match matchRule2 t1 t2 with
  | Some (out, mode) => finishTurn (pushToksLtr out r4) mode rStack k1
  | None =>
    match popLastTok r4 with
    | None => SCR_err
    | Some (t3, r5) =>
      if tokEq t1 T_tok then
        if tokEq t2 M_tok then
          if tokEq t3 U_tok then
            if isEmptyRle r5 then
              finishTurn [([Z_tok], 1%N); ([U_tok], 1%N)] R1_mode rStack k1
            else SCR_err
          else stepTurnFrom3 t1 t2 t3 r5 rStack k1
        else stepTurnFrom3 t1 t2 t3 r5 rStack k1
      else if tokEq t1 U_tok then
        if tokEq t2 T_tok then
          if tokEq t3 Z_tok then SCR_halt
          else stepTurnFrom3 t1 t2 t3 r5 rStack k1
        else stepTurnFrom3 t1 t2 t3 r5 rStack k1
      else stepTurnFrom3 t1 t2 t3 r5 rStack k1
    end
  end.

Lemma stepTurnFrom2_sound (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom2 t1 t2 r4 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> evalRle r4) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom2 t1 t2 r4 rStack k1).
Proof.
  unfold stepTurnFrom2 in *.
  destruct (matchRule2 t1 t2) as [[out mode]|] eqn:Hm2.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule2_sound t1 t2 out mode r4 _ Hm2)
      (finishTurn_sound (pushToksLtr out r4) mode rStack k1 hne)).
  - destruct (popLastTok r4) as [[t3 r5]|] eqn:Hp3; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r4 t3 r5 Hp3).
    destruct (tokEq t1 T_tok) eqn:Ht1.
    + destruct (tokEq t2 M_tok) eqn:Hm2'.
      * destruct (tokEq t3 U_tok) eqn:Hu3.
        -- destruct (isEmptyRle r5) eqn:He; [|exfalso; apply hne; reflexivity].
           apply tokEq_eq in Ht1; apply tokEq_eq in Hm2'; apply tokEq_eq in Hu3; apply isEmptyRle_eq in He.
           subst t1 t2 t3 r5.
           eapply stepCarryValid_of_stepStar; [|exact (finishTurn_sound _ R1_mode rStack k1 hne)].
           cbn [evalRle npow Pos.to_nat wordL app modeCfg].
           apply turn_UMT.
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
    + destruct (tokEq t1 U_tok) eqn:Hu1.
      * destruct (tokEq t2 T_tok) eqn:Ht2.
        -- destruct (tokEq t3 Z_tok) eqn:Hz3.
           ++ apply tokEq_eq in Hu1; apply tokEq_eq in Ht2; apply tokEq_eq in Hz3.
              subst t1 t2 t3.
              cbn [StepCarryValid].
              eexists; split; [apply turn_ZTU_halt | reflexivity].
           ++ exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
Qed.

Definition stepTurnaround (r2 rStack : Rle) (k1 : N) : StepCarryRes :=
  match popLastTok r2 with
  | None => SCR_err
  | Some (t1, r3) =>
    match popLastTok r3 with
    | None => SCR_err
    | Some (t2, r4) =>
      if tokEq t1 M_tok then
        if tokEq t2 U_tok then
          if isEmptyRle r4 then
            finishTurn [([M_tok], 1%N); ([U_tok], 1%N)] R1_mode rStack k1
          else SCR_err
        else stepTurnFrom2 t1 t2 r4 rStack k1
      else stepTurnFrom2 t1 t2 r4 rStack k1
    end
  end.

Lemma stepTurnaround_sound (r2 rStack : Rle) (k1 : N)
  (hne : stepTurnaround r2 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (stepTurnaround r2 rStack k1).
Proof.
  unfold stepTurnaround in *.
  destruct (popLastTok r2) as [[t1 r3]|] eqn:Hp1; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r2 t1 r3 Hp1).
  destruct (popLastTok r3) as [[t2 r4]|] eqn:Hp2; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r3 t2 r4 Hp2).
  destruct (tokEq t1 M_tok) eqn:Hm1.
  - destruct (tokEq t2 U_tok) eqn:Hu2.
    + destruct (isEmptyRle r4) eqn:He; [|exfalso; apply hne; reflexivity].
      apply tokEq_eq in Hm1; apply tokEq_eq in Hu2; apply isEmptyRle_eq in He.
      subst t1 t2 r4.
      eapply stepCarryValid_of_stepStar; [|exact (finishTurn_sound _ R1_mode rStack k1 hne)].
      cbn [evalRle npow Pos.to_nat wordL app modeCfg].
      apply turn_UM.
    + exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
  - exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
Qed.

Local Opaque stepTurnaround.

Lemma special_ZTM_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL M_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL M_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTM.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTM|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_PT_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL T_tok *> npow (tokL P_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL P_tok) (n + 1)%N *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_PT.
  - rewrite (npow_succ_l (tokL P_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_PT|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_P|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_P R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_P|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL P_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Lemma special_ZTW_loop : forall (n : N) (l : side) (R : N -> side),
  HasRoundtrip R -> forall (k1 : N),
  carryCfg (tokL W_tok *> tokL T_tok *> npow (tokL Z_tok) (n + 1)%N *> l) (R k1) -[ tm ]->*
  r0Cfg (npow (tokL Z_tok) (n + 1)%N *> tokL W_tok *> tokL T_tok *> l) (R (k1 + 2 * n)%N).
Proof.
  induction n as [|n ih] using N_peano_ind; intros l R hR k1.
  - replace (0 + 1)%N with 1%N by lia.
    replace (k1 + 2 * 0)%N with k1 by lia.
    rewrite !npow_1.
    apply turn_ZTW.
  - rewrite (npow_succ_l (tokL Z_tok) (n + 1)%N), Str_app_assoc.
    eapply evstep_trans; [apply turn_ZTW|].
    eapply evstep_trans; [apply (hR _ k1)|].
    eapply evstep_trans; [apply carry_Z|].
    eapply evstep_trans; [apply (ih l _ (hasRoundtrip_Z R hR) (k1 + 2)%N)|].
    eapply evstep_trans; [apply r0_Z|].
    replace (k1 + 2 + 2 * n)%N with (k1 + 2 * (n + 1))%N by lia.
    rewrite <- Str_app_assoc, <- (npow_succ_l (tokL Z_tok) (n + 1)%N).
    apply evstep_refl.
Qed.

Definition stepSpecialLoops (r2 rStack : Rle) (k1 : N) : option StepCarryRes :=
  match popLastTok r2 with
  | None => None
  | Some (t1, r2a) =>
    match t1 with
    | U_tok =>
      match popTok M_tok r2a with
      | None => None
      | Some rest =>
        let '(mVal, r3) := popTokCount 8 P_tok 0%N rest in
        if (mVal =? 0)%N then None
        else
          match popTok Z_tok r3 with
          | None => Some SCR_err
          | Some r4 =>
            let r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4)) in
            Some (finishTurn r5 R0_mode rStack k1)
          end
      end
    | M_tok =>
      match popTok T_tok r2a with
      | None => None
      | Some rest =>
        let '(b, r3) := popTokCount 8 Z_tok 0%N rest in
        if (b =? 0)%N then None
        else
          let r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3) in
          match copyRStack r3' rStack with
          | None => Some SCR_err
          | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
          end
      end
    | W_tok =>
      match popTok T_tok r2a with
      | None => None
      | Some rest =>
        let '(b, r3) := popTokCount 8 Z_tok 0%N rest in
        if (b =? 0)%N then None
        else
          let r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3) in
          match copyRStack r3' rStack with
          | None => Some SCR_err
          | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
          end
      end
    | T_tok =>
      let '(b, r3) := popTokCount 8 P_tok 0%N r2a in
      if (b =? 0)%N then None
      else
        let r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3) in
        match copyRStack r3' rStack with
        | None => Some SCR_err
        | Some r4 => Some (SCR_next r4 (k1 + 2 * b)%N)
        end
    | _ => None
    end
  end.

Lemma stepSpecialLoops_sound (r2 rStack : Rle) (k1 : N) (res : StepCarryRes)
  (h : stepSpecialLoops r2 rStack k1 = Some res) (hne : res <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res.
Proof.
  unfold stepSpecialLoops in h.
  destruct (popLastTok r2) as [[t1 r2a]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound r2 t1 r2a Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popTok M_tok r2a) as [rest|] eqn:Hpm; [|discriminate].
    rewrite (popTok_sound M_tok r2a rest Hpm).
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N rest) as [mVal r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
    apply N.eqb_neq in Hm0.
    destruct (popTok Z_tok r3) as [r4|] eqn:Hpz; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h.
    rewrite Hcnt, (popTok_sound Z_tok r3 r4 Hpz).
    eapply stepCarryValid_of_stepStar; [apply carry_MU_to_pmuCfg|].
    eapply stepCarryValid_of_stepStar; [apply (pmu_loop mVal (tokL Z_tok *> evalRle r4))|].
    replace mVal with (1 + (mVal - 1))%N at 1 by lia.
    rewrite (npow_add (tokR Z_tok) 1%N (mVal - 1)%N), npow_1, Str_app_assoc.
    eapply stepCarryValid_of_stepStar; [apply pmuCfg_Z_turn|].
    eapply stepCarryValid_of_stepStar; [apply (r0_Z_loop (mVal - 1)%N)|].
    eapply stepCarryValid_of_stepStar; [apply r0_P|].
    set (r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4))) in *.
    assert (Hr5 : tokL P_tok *> npow (tokL Z_tok) (mVal - 1)%N *> tokL M_tok *> tokL W_tok *> tokL T_tok *> evalRle r4 = evalRle r5).
    { unfold r5; rewrite evalRle_pushRlePos_one, evalRle_pushRle, evalRle_pushToksLtr.
      cbn [revWord wordL app]; rewrite app_nil_r, !Str_app_assoc; reflexivity. }
    rewrite Hr5.
    exact (finishTurn_sound r5 R0_mode rStack k1 hne).
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTM_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTW_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2a)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N r2a) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_PT_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushRlePos_one in Hcopy;
    cbn [wordL app] in Hcopy; rewrite app_nil_r in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
Qed.

Local Opaque stepSpecialLoops.

Definition stepCarry (rle : Rle) (k1 : N) : StepCarryRes :=
  let '(r2, rStack) := popCarryLoop 80 rle [] in
  if hasSpecial rStack then
    stepTurnaround r2 rStack k1
  else
    match stepSpecialLoops r2 rStack k1 with
    | None => stepTurnaround r2 rStack k1
    | Some res => res
    end.

Lemma stepCarry_sound (rle : Rle) (k1 : N) (hne : stepCarry rle k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarry rle k1).
Proof.
  pose proof (popCarryLoop_sound 80 rle [] (evalWK k1)) as Hp.
  cbn [evalRStack] in Hp.
  unfold stepCarry in *.
  destruct (popCarryLoop 80 rle []) as [r2 rStack] eqn:Hpop.
  cbn [fst snd] in Hp.
  eapply stepCarryValid_of_stepStar; [exact Hp|].
  destruct (hasSpecial rStack) eqn:Hns.
  - exact (stepTurnaround_sound r2 rStack k1 hne).
  - destruct (stepSpecialLoops r2 rStack k1) as [res|] eqn:Hsl.
    + exact (stepSpecialLoops_sound r2 rStack k1 res Hsl hne).
    + exact (stepTurnaround_sound r2 rStack k1 hne).
Qed.

Local Opaque stepCarry.

Fixpoint runCarryChunk (n : nat) (rle : Rle) (k1 : N) : StepCarryRes :=
  match n with
  | O => SCR_next rle k1
  | S n' =>
    match stepCarry rle k1 with
    | SCR_halt => SCR_halt
    | SCR_next rle' k1' => runCarryChunk n' rle' k1'
    | SCR_err => SCR_err
    end
  end.

Lemma runCarryChunk_sound : forall (n : nat) (rle : Rle) (k1 : N),
  runCarryChunk n rle k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (runCarryChunk n rle k1).
Proof.
  induction n as [|n ih]; intros rle k1 hne; cbn [runCarryChunk] in *.
  - cbn [StepCarryValid]; apply evstep_refl.
  - destruct (stepCarry rle k1) as [|rle' k1'|] eqn:Hs.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; exact Hv.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; cbn [StepCarryValid] in Hv.
      exact (stepCarryValid_of_stepStar _ _ _ Hv (ih rle' k1' hne)).
    + exfalso; apply hne; reflexivity.
Qed.

Fixpoint runCarryChunks (chunks chunkSize : nat) (rle : Rle) (k1 : N) : bool :=
  match chunks with
  | O => false
  | S chunks' =>
    match runCarryChunk chunkSize rle k1 with
    | SCR_halt => true
    | SCR_next rle' k1' => runCarryChunks chunks' chunkSize rle' k1'
    | SCR_err => false
    end
  end.

Lemma runCarryChunks_sound : forall (chunks chunkSize : nat) (rle : Rle) (k1 : N),
  runCarryChunks chunks chunkSize rle k1 = true ->
  exists cfg', (carryCfg (evalRle rle) (evalWK k1) -[ tm ]->* cfg') /\ halted tm cfg'.
Proof.
  induction chunks as [|chunks ih]; intros chunkSize rle k1 h; cbn [runCarryChunks] in h; [discriminate|].
  destruct (runCarryChunk chunkSize rle k1) as [|rle' k1'|] eqn:Hc; [| |discriminate].
  - pose proof (runCarryChunk_sound chunkSize rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv; exact Hv.
  - pose proof (runCarryChunk_sound chunkSize rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv.
    destruct (ih chunkSize rle' k1' h) as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact Hv | exact h2] | exact hhalt].
Qed.

Local Transparent pushRlePos pushRle popTokCount stepZtToCarry
  popCarrySpecial popCarryLoop stepOneBounceFuel runRightSweepStarCarry
  stepTurnaround stepSpecialLoops stepCarry.

Definition initRle : Rle :=
  pushToksLtr [U_tok; M_tok; Z_tok; Z_tok; P_tok; T_tok; M_tok; Z_tok; Z_tok] [].

Lemma init_to_carry0 :
  c0 -[ tm ]->* carryCfg (evalRle initRle) (evalWK 1%N).
Proof.
  exact (bmultiStep_sound tm 2049
    (mkCCfg A 0%sym []%sym []%sym)
    (mkCCfg D 1%sym
      [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym
      [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym)
    ltac:(vm_compute; reflexivity)).
Qed.

Lemma runCarryChunks_28_500 : runCarryChunks 28 500 initRle 1%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem halt: halts tm c0.
Proof.
  destruct (runCarryChunks_sound 28 500 initRle 1%N runCarryChunks_28_500)
    as [cfg' [Hsteps Hhalted]].
  eapply halts_evstep.
  - exact (halted_halts tm cfg' Hhalted).
  - eapply evstep_trans; [exact init_to_carry0 | exact Hsteps].
Qed.

End TM4.
Print Assumptions TM4.halt.



Module TM5.
Import BusyCoq.Individual62.

Import Bool List Streams PeanoNat Lia NArith ZArith String.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1LF_---1RA").

Notation tm521 := TM1.tm.

Open Scope list_scope.

Definition sigma_Q (q : Q) : Q :=
  match q with
  | A => B | B => C | C => A | D => E | E => D | F => F
  end.

Definition conj_dir (d : dir) : dir :=
  match d with L => R | R => L end.

Definition conj_cfg (c : Q * tape) : Q * tape :=
  let '(q, (l, s, r)) := c in
  (sigma_Q q, (r, s, l)).

Lemma table_iso (q : Q) (s : Sym) :
  tm (sigma_Q q, s) =
  match tm521 (q, s) with
  | None => None
  | Some (w, d, q') => Some (w, conj_dir d, sigma_Q q')
  end.
Proof. destruct q, s; reflexivity. Qed.

Lemma step_conj {c c' : Q * tape} (h : c -[ tm521 ]-> c') :
  conj_cfg c -[ tm ]-> conj_cfg c'.
Proof.
  inverts h as Htr.
  - pose proof (table_iso q s) as Hiso; rewrite Htr in Hiso; cbn in Hiso.
    cbn [conj_cfg move_left]; exact (step_right Hiso).
  - pose proof (table_iso q s) as Hiso; rewrite Htr in Hiso; cbn in Hiso.
    cbn [conj_cfg move_right]; exact (step_left Hiso).
Qed.

Lemma evstep_conj {c c' : Q * tape} (h : c -[ tm521 ]->* c') :
  conj_cfg c -[ tm ]->* conj_cfg c'.
Proof.
  induction h as [c | c c1 c2 Hs _ ih].
  - apply evstep_refl.
  - exact (evstep_step _ _ _ _ (step_conj Hs) ih).
Qed.

Lemma halted_conj {c : Q * tape} (h : halted tm521 c) :
  halted tm (conj_cfg c).
Proof.
  destruct c as [q [[l s] r]]. cbn [halted] in h. cbn [conj_cfg halted].
  pose proof (table_iso q s) as Hiso; rewrite h in Hiso; exact Hiso.
Qed.

Notation N_peano_ind := TM1.N_peano_ind.

Notation npow := TM1.npow.

Notation npow_0 := TM1.npow_0.

Notation npow_1 := TM1.npow_1.

Notation npow_add := TM1.npow_add.

Notation npow_2 := TM1.npow_2.

Notation npow_3 := TM1.npow_3.

Notation npow_succ_l := TM1.npow_succ_l.

Notation npow_succ_r := TM1.npow_succ_r.

Notation zero_cons_0inf := TM1.zero_cons_0inf.

Notation CCfg := TM1.CCfg.

Notation mkCCfg := TM1.mkCCfg.

Notation cc_q := TM1.cc_q.

Notation cc_cur := TM1.cc_cur.

Notation cc_l := TM1.cc_l.

Notation cc_r := TM1.cc_r.

Notation sym_eqb := TM1.sym_eqb.

Notation sym_eqb_eq := TM1.sym_eqb_eq.

Notation is_nil_sym := TM1.is_nil_sym.

Notation evalWindow := TM1.evalWindow.

Notation evalCCfg := TM1.evalCCfg.

Notation evalRCCfg := TM1.evalRCCfg.

Notation evalBCfg := TM1.evalBCfg.

Notation wstep := TM1.wstep.

Notation wstep_sound := TM1.wstep_sound.

Notation wmultiStep := TM1.wmultiStep.

Notation wmultiStep_sound := TM1.wmultiStep_sound.

Notation cstep := TM1.cstep.

Notation cstep_sound := TM1.cstep_sound.

Notation cmultiStep := TM1.cmultiStep.

Notation cmultiStep_sound := TM1.cmultiStep_sound.

Notation rcstep := TM1.rcstep.

Notation rcstep_sound := TM1.rcstep_sound.

Notation rcmultiStep := TM1.rcmultiStep.

Notation rcmultiStep_sound := TM1.rcmultiStep_sound.

Notation bstep := TM1.bstep.

Notation bstep_sound := TM1.bstep_sound.

Notation bmultiStep := TM1.bmultiStep.

Notation bmultiStep_sound := TM1.bmultiStep_sound.

Notation Tok := TM1.Tok.

Notation U_tok := TM1.U_tok.

Notation M_tok := TM1.M_tok.

Notation W_tok := TM1.W_tok.

Notation Z_tok := TM1.Z_tok.

Notation T_tok := TM1.T_tok.

Notation P_tok := TM1.P_tok.

Notation PTTTM_TAIL_tok := TM1.PTTTM_TAIL_tok.

Notation Mode := TM1.Mode.

Notation R0_mode := TM1.R0_mode.

Notation R1_mode := TM1.R1_mode.

Notation R1_ODD_mode := TM1.R1_ODD_mode.

Notation Rle := TM1.Rle.

Notation tokEq := TM1.tokEq.

Notation tokEq_eq := TM1.tokEq_eq.

Notation modeEq := TM1.modeEq.

Notation modeEq_eq := TM1.modeEq_eq.

Notation wordEq := TM1.wordEq.

Notation wordEq_eq := TM1.wordEq_eq.

Notation isZpTok := TM1.isZpTok.

Notation isZpWord := TM1.isZpWord.

Notation revWord := TM1.revWord.

Notation revWord_append := TM1.revWord_append.

Notation revWord_revWord := TM1.revWord_revWord.

Notation isZpWord_append := TM1.isZpWord_append.

Notation isZpWord_revWord := TM1.isZpWord_revWord.

Notation tokL := TM1.tokL.

Notation tokR := TM1.tokR.

Notation wordL := TM1.wordL.

Notation wordR := TM1.wordR.

Notation wordL_append := TM1.wordL_append.

Notation wordR_append := TM1.wordR_append.

Notation evalRle := TM4.evalRle.

Notation evalRStack := TM1.evalRStack.

Notation pushRlePos := TM1.pushRlePos.

Notation pushRle := TM1.pushRle.

Notation evalRle_pushRlePos := TM4.evalRle_pushRlePos.

Notation evalRle_pushRle := TM4.evalRle_pushRle.

Notation evalRle_pushRlePos_one := TM4.evalRle_pushRlePos_one.

Notation evalRStack_pushRlePos := TM1.evalRStack_pushRlePos.

Notation evalRStack_pushRle := TM1.evalRStack_pushRle.

Local Opaque pushRlePos pushRle.

Notation pushToksLtr := TM1.pushToksLtr.

Notation evalRle_pushToksLtr := TM4.evalRle_pushToksLtr.

Notation popLastTok := TM1.popLastTok.

Notation popLastTok_sound := TM4.popLastTok_sound.

Notation popTok := TM1.popTok.

Notation popTok_sound := TM4.popTok_sound.

Notation popToks := TM1.popToks.

Notation popToks_sound := TM4.popToks_sound.

Notation popTokCount := TM1.popTokCount.

Notation popTokCount_sound := TM4.popTokCount_sound.

Local Opaque popTokCount.

Notation evalWK := TM1.evalWK.

Notation cfgR := TM1.cfgR.

Notation carryCfg := TM1.carryCfg.

Notation r0Cfg := TM1.r0Cfg.

Notation r1Cfg := TM1.r1Cfg.

Notation r1OddShortCfg := TM1.r1OddShortCfg.

Notation r1OddCfg := TM1.r1OddCfg.

Notation wSweepCfg := TM1.wSweepCfg.

Notation dSweepCfg := TM1.dSweepCfg.

Notation tSweepCfg := TM1.tSweepCfg.

Notation t3Cfg := TM1.t3Cfg.

Notation pmuCfg := TM1.pmuCfg.

Ltac solve_wstep n c1 c2 l r :=
  exact (wmultiStep_sound tm521 n c1 c2 l r ltac:(vm_compute; reflexivity)).

Ltac solve_cstep n c1 c2 r :=
  exact (cmultiStep_sound tm521 n c1 c2 r ltac:(vm_compute; reflexivity)).

Ltac solve_rcstep n c1 c2 l :=
  exact (rcmultiStep_sound tm521 n c1 c2 l ltac:(vm_compute; reflexivity)).

Notation carry_Z := TM1.carry_Z.

Notation carry_P := TM1.carry_P.

Notation carry_PMUTM := TM1.carry_PMUTM.

Notation carry_PTTW := TM1.carry_PTTW.

Notation carry_PTTT := TM1.carry_PTTT.

Notation carry_PTTTM := TM1.carry_PTTTM.

Notation turn_UM := TM1.turn_UM.

Notation turn_UMT := TM1.turn_UMT.

Notation turn_ZT := TM1.turn_ZT.

Notation turn_WM := TM1.turn_WM.

Notation turn_PT := TM1.turn_PT.

Notation turn_ZM := TM1.turn_ZM.

Notation turn_PTW := TM1.turn_PTW.

Notation turn_PTM := TM1.turn_PTM.

Notation turn_PTT := TM1.turn_PTT.

Notation turn_ZMU := TM1.turn_ZMU.

Notation turn_ZTM := TM1.turn_ZTM.

Notation turn_ZTT := TM1.turn_ZTT.

Notation turn_ZTW := TM1.turn_ZTW.

Notation turn_MUTW := TM1.turn_MUTW.

Notation turn_PTTM := TM1.turn_PTTM.

Notation turn_ZTTW := TM1.turn_ZTTW.

Notation turn_ZTTM := TM1.turn_ZTTM.

Notation turn_ZPMU := TM1.turn_ZPMU.

Notation turn_ZMUTM := TM1.turn_ZMUTM.

Notation turn_PTTTW := TM1.turn_PTTTW.

Notation carry_MU_to_pmuCfg := TM1.carry_MU_to_pmuCfg.

Notation pmu_step := TM1.pmu_step.

Notation pmuCfg_Z_turn := TM1.pmuCfg_Z_turn.

Notation pmuCfg_M_to_carry := TM1.pmuCfg_M_to_carry.

Notation pmuCfg_T_to_carry := TM1.pmuCfg_T_to_carry.

Notation carry_PTU := TM1.carry_PTU.

Notation turn_PTMT := TM1.turn_PTMT.

Notation turn_ZTTT := TM1.turn_ZTTT.

Notation turn_ZTTTM := TM1.turn_ZTTTM.

Notation turn_ZTU_halt := TM1.turn_ZTU_halt.

Notation r0_Z := TM1.r0_Z.

Notation r0_P := TM1.r0_P.

Notation r0_PTTTM_TAIL := TM1.r0_PTTTM_TAIL.

Notation r1_Z := TM1.r1_Z.

Notation r1_P := TM1.r1_P.

Notation r1OddShort_Z := TM1.r1OddShort_Z.

Notation r1Odd_P := TM1.r1Odd_P.

Notation wSweep_start := TM1.wSweep_start.

Notation wSweep_step := TM1.wSweep_step.

Notation dSweep_step := TM1.dSweep_step.

Notation dSweep_end := TM1.dSweep_end.

Notation tSweep_step := TM1.tSweep_step.

Notation tSweep_end := TM1.tSweep_end.

Notation r0_to_dSweep := TM1.r0_to_dSweep.

Notation r1_to_dSweep := TM1.r1_to_dSweep.

Notation r1Odd_to_tSweep := TM1.r1Odd_to_tSweep.

Notation wSweep_Z_to_dSweep := TM1.wSweep_Z_to_dSweep.

Notation wSweep_ZT_to_dSweep := TM1.wSweep_ZT_to_dSweep.

Notation wSweep_PT_to_carry := TM1.wSweep_PT_to_carry.

Notation wSweep_ZMT_to_tSweep := TM1.wSweep_ZMT_to_tSweep.

Notation cfgR_Z_to_TW := TM1.cfgR_Z_to_TW.

Notation cfgR_TW_to_t3Cfg := TM1.cfgR_TW_to_t3Cfg.

Notation t3_step := TM1.t3_step.

Notation t3Cfg_Z_zero_to_carry := TM1.t3Cfg_Z_zero_to_carry.

Notation t3Cfg_Z_succ_to_r0 := TM1.t3Cfg_Z_succ_to_r0.

Notation t3Cfg_TZ_to_r1OddShort := TM1.t3Cfg_TZ_to_r1OddShort.

Notation r1OddShortCfg_evalWK0_to_carry := TM1.r1OddShortCfg_evalWK0_to_carry.

Notation t3Cfg_TTZ_to_r0 := TM1.t3Cfg_TTZ_to_r0.

Notation r1Odd_Z := TM1.r1Odd_Z.

Notation wSweep_loop := TM1.wSweep_loop.

Notation dSweep_loop := TM1.dSweep_loop.

Notation tSweep_loop := TM1.tSweep_loop.

Notation t3_loop := TM1.t3_loop.

Notation pmu_loop := TM1.pmu_loop.

Notation r0_Z_loop := TM1.r0_Z_loop.

Notation r0_P_loop := TM1.r0_P_loop.

Notation r1OddShort_Z_loop := TM1.r1OddShort_Z_loop.

Notation cfgR_ZW_to_TW := TM1.cfgR_ZW_to_TW.

Notation r0_end := TM1.r0_end.

Notation r1_end := TM1.r1_end.

Notation r1Odd_end := TM1.r1Odd_end.

Notation stepZtToCarry := TM4.stepZtToCarry.

Lemma stepZtToCarry_sound (rle2 : Rle) (n : N) :
  t3Cfg (npow (tokL T_tok) n *> tokL Z_tok *> evalRle rle2) (evalWK 0%N) -[ tm521 ]->*
  carryCfg (evalRle (fst (stepZtToCarry rle2 n))) (evalWK (snd (stepZtToCarry rle2 n))).
Proof.
  unfold stepZtToCarry; cbn zeta.
  pose proof (N.div_mod n 3 ltac:(discriminate)) as Hdiv.
  pose proof (N.mod_upper_bound n 3 ltac:(discriminate)) as Hmod.
  set (q := (n / 3)%N) in *.
  set (rem := (n mod 3)%N) in *.
  replace n with (3 * q + rem)%N at 1 by lia.
  rewrite (npow_add (tokL T_tok) (3 * q)%N rem), Str_app_assoc.
  eapply evstep_trans; [apply (t3_loop q (npow (tokL T_tok) rem *> tokL Z_tok *> evalRle rle2) (evalWK 0%N))|].
  assert (Hrem : rem = 0%N \/ rem = 1%N \/ rem = 2%N) by lia.
  destruct Hrem as [Hrem | [Hrem | Hrem]]; rewrite Hrem; cbn [N.eqb Pos.eqb fst snd].
  - rewrite npow_0; cbn [Str_app].
    destruct (q =? 0)%N eqn:Hq0; cbn [fst snd].
    + apply N.eqb_eq in Hq0; rewrite Hq0.
      cbn [N.mul npow Str_app].
      apply t3Cfg_Z_zero_to_carry.
    + apply N.eqb_neq in Hq0.
      replace (2 * q)%N with (1 + (2 * q - 1))%N at 1 by lia.
      rewrite (npow_add (tokR Z_tok) 1%N (2 * q - 1)%N), npow_1, Str_app_assoc.
      eapply evstep_trans; [apply t3Cfg_Z_succ_to_r0|].
      eapply evstep_trans; [apply (r0_Z_loop (2 * q - 1)%N (tokL P_tok *> evalRle rle2) (evalWK 0%N))|].
      rewrite evalRle_pushRle, evalRle_pushRlePos_one; cbn [wordL]; rewrite app_nil_r.
      apply (r0_end 0%N).
  - rewrite npow_1.
    eapply evstep_trans; [apply t3Cfg_TZ_to_r1OddShort|].
    eapply evstep_trans; [apply (r1OddShort_Z_loop (2 * q)%N (tokL M_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply r1OddShortCfg_evalWK0_to_carry.
  - rewrite npow_2, Str_app_assoc.
    eapply evstep_trans; [apply t3Cfg_TTZ_to_r0|].
    eapply evstep_trans; [apply (r0_Z_loop (2 * q)%N (tokL W_tok *> tokL T_tok *> evalRle rle2) (evalWK 0%N))|].
    rewrite evalRle_pushRle, evalRle_pushToksLtr; cbn [revWord wordL app]; rewrite !Str_app_assoc.
    apply (r0_end 0%N).
Qed.

Local Opaque stepZtToCarry.

Notation carry_word := TM1.carry_word.

Notation carry_pow := TM1.carry_pow.

Notation popCarrySpecial := TM1.popCarrySpecial.

Lemma popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : side)
  (h : popCarrySpecial rle rs = Some (rle', rs')) :
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm521 ]->*
  carryCfg (evalRle rle') (evalRStack rs' r_end).
Proof.
  unfold popCarrySpecial in h.
  destruct (popLastTok rle) as [[t1 r1]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound rle t1 r1 Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popLastTok r1) as [[t2 r2]|] eqn:Hp2; [|discriminate].
    rewrite (popLastTok_sound r1 t2 r2 Hp2).
    destruct t2; try discriminate.
    +  
      pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2)) as Hpcs.
      destruct (popTokCount 8 P_tok 0%N r2) as [mVal r3] eqn:Hpc.
      cbn [fst snd] in Hpcs; rewrite npow_0 in Hpcs; cbn [Str_app] in Hpcs.
      rewrite Hpcs.
      destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
      destruct (popLastTok r3) as [[t3 r4]|] eqn:Hp3; [|discriminate].
      rewrite (popLastTok_sound r3 t3 r4 Hp3).
      destruct t3; try discriminate; inverts h.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL M_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_M_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
      *  
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL T_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_T_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
    +  
      destruct (popTok P_tok r2) as [r3|] eqn:Hp3; [|discriminate].
      inverts h.
      rewrite (popTok_sound P_tok r2 r3 Hp3).
      rewrite evalRle_pushRlePos_one, evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite !app_nil_r.
      apply carry_PTU.
  -  
    destruct (popToks [T_tok; U_tok; M_tok; P_tok] r1) as [r5|] eqn:Hp2.
    + rewrite (popToks_sound _ r1 r5 Hp2).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PMUTM.
    + destruct (popToks [T_tok; T_tok; T_tok; P_tok] r1) as [r5|] eqn:Hp3; [|discriminate].
      rewrite (popToks_sound _ r1 r5 Hp3).
      cbn [wordL app]; rewrite ?Str_app_assoc.
      change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r5)
        with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r5).
      inverts h.
      rewrite !evalRStack_pushRlePos, npow_1.
      cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
      apply carry_PTTTM.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 2%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTW.
  -  
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 3%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos, npow_1.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTT.
Qed.

Local Opaque popCarrySpecial.

Notation popCarryLoop := TM1.popCarryLoop.

Lemma popCarryLoop_sound : forall (fuel : nat) (rle rs : Rle) (r_end : side),
  carryCfg (evalRle rle) (evalRStack rs r_end) -[ tm521 ]->*
  carryCfg (evalRle (fst (popCarryLoop fuel rle rs))) (evalRStack (snd (popCarryLoop fuel rle rs)) r_end).
Proof.
  induction fuel as [|fuel ih]; intros rle rs r_end; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  destruct rle as [|[w c] rest]; [cbn [popCarryLoop fst snd]; apply evstep_refl|].
  cbn [popCarryLoop].
  destruct (isZpWord w) eqn:Hw.
  - cbn [evalRle].
    eapply evstep_trans; [apply (carry_pow c w (evalRle rest) (evalRStack rs r_end) Hw)|].
    rewrite <- (evalRStack_pushRlePos w c rs r_end).
    apply ih.
  - destruct (popCarrySpecial ((w, c) :: rest) rs) as [[rle' rs']|] eqn:Hsp.
    + eapply evstep_trans; [apply (popCarrySpecial_sound _ _ _ _ r_end Hsp)|].
      apply ih.
    + cbn [fst snd]; apply evstep_refl.
Qed.

Local Opaque popCarryLoop.

Notation r0_word := TM1.r0_word.

Notation r0_pow := TM1.r0_pow.

Notation allZpStack := TM1.allZpStack.

Notation copyRStack := TM1.copyRStack.

Lemma copyRStack_sound : forall (rs : Rle) (rle rle' : Rle) (r_end : side),
  copyRStack rle rs = Some rle' ->
  allZpStack rs = true /\
  r0Cfg (evalRle rle) (evalRStack rs r_end) -[ tm521 ]->* r0Cfg (evalRle rle') r_end.
Proof.
  induction rs as [|[w c] rest ih]; intros rle rle' r_end h; cbn [copyRStack] in h.
  - inverts h; cbn [allZpStack evalRStack]; split; [reflexivity | apply evstep_refl].
  - destruct (isZpWord w) eqn:Hw; [|discriminate].
    destruct (ih (pushRlePos w c rle) rle' r_end h) as [Hrest Hstep].
    cbn [allZpStack]; rewrite Hw, Hrest; split; [reflexivity|].
    cbn [evalRStack].
    assert (Hrev : isZpWord (revWord w) = true) by (rewrite isZpWord_revWord; exact Hw).
    eapply evstep_trans; [apply (r0_pow c (revWord w) (evalRle rle) (evalRStack rest r_end) Hrev)|].
    rewrite revWord_revWord, <- evalRle_pushRlePos.
    exact Hstep.
Qed.

Notation HasRoundtrip := TM1.HasRoundtrip.

Notation hasRoundtrip_evalWK := TM1.hasRoundtrip_evalWK.

Notation hasRoundtrip_Z := TM1.hasRoundtrip_Z.

Notation hasRoundtrip_P := TM1.hasRoundtrip_P.

Notation hasRoundtrip_word := TM1.hasRoundtrip_word.

Notation hasRoundtrip_pow := TM1.hasRoundtrip_pow.

Notation hasRoundtrip_stack := TM1.hasRoundtrip_stack.

Notation r1PhaseCfg := TM1.r1PhaseCfg.

Notation stepR1StarWordL := TM1.stepR1StarWordL.

Notation r1_out := TM1.r1_out.

Notation r1_res := TM1.r1_res.

Notation r1_phase := TM1.r1_phase.

Notation stepR1StarWordL_phase_inv := TM1.stepR1StarWordL_phase_inv.

Notation stepR1StarWordL_sound := TM1.stepR1StarWordL_sound.

Notation stepR1Star_same_pow := TM1.stepR1Star_same_pow.

Notation stepR1Star_alt_pow := TM1.stepR1Star_alt_pow.

Notation sweepStarLoop := TM4.sweepStarLoop.

Lemma sweepStarLoop_sound : forall (rs : Rle) (rle : Rle) (phase : bool) (totalRes : N) (R : N -> side),
  allZpStack rs = true -> HasRoundtrip R ->
  forall (k1 : N),
    let res := sweepStarLoop rle phase totalRes rs in
    r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)%N)) -[ tm521 ]->*
    r1PhaseCfg (snd (fst res)) (evalRle (fst (fst res))) (R (k1 + 2 * snd res)%N).
Proof.
  induction rs as [|[item count] rest ih]; intros rle phase totalRes R hrs hR k1 res.
  - unfold res; cbn [sweepStarLoop evalRStack fst snd]; apply evstep_refl.
  - cbn [allZpStack] in hrs; apply andb_true_iff in hrs; destruct hrs as [hitem hrest].
    assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact hitem).
    pose proof (hasRoundtrip_stack rest R hrest hR) as hR_rest.
    unfold res; cbn [sweepStarLoop evalRStack].
    set (s1 := stepR1StarWordL item phase).
    destruct (Bool.eqb (r1_phase s1) phase) eqn:Hsame.
    + apply Bool.eqb_prop in Hsame.
      eapply evstep_trans.
      * apply (stepR1Star_same_pow count item phase (evalRle rle) _ hitem Hsame hR_rest (k1 + 2 * totalRes)%N).
      * fold s1.
        replace (k1 + 2 * totalRes + 2 * (count * r1_res s1))%N
          with (k1 + 2 * (totalRes + count * r1_res s1))%N by lia.
        rewrite <- evalRle_pushRlePos.
        apply (ih (pushRlePos (r1_out s1) count rle) phase (totalRes + count * r1_res s1)%N R hrest hR k1).
    + assert (Hnot : r1_phase s1 = negb phase).
      { destruct (r1_phase s1), phase; cbn in Hsame; try discriminate; reflexivity. }
      assert (Halt : r1_phase (stepR1StarWordL item (r1_phase s1)) = phase).
      { rewrite Hnot, (stepR1StarWordL_phase_inv item phase hitem).
        fold s1; rewrite Hnot, Bool.negb_involutive; reflexivity. }
      set (s2 := stepR1StarWordL item (r1_phase s1)).
      cbn zeta.
      pose proof (N.div_mod count 2 ltac:(discriminate)) as Hdiv.
      pose proof (N.mod_upper_bound count 2 ltac:(discriminate)) as Hmod.
      set (q := (count / 2)%N) in *.
      set (rem := (count mod 2)%N) in *.
      replace count with (2 * q + rem)%N at 1 by lia.
      rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
      pose proof (hasRoundtrip_pow rem (revWord item) _ Hrev hR_rest) as hR_rem.
      eapply evstep_trans.
      * apply (stepR1Star_alt_pow q item phase (evalRle rle) _ hitem Halt hR_rem (k1 + 2 * totalRes)%N).
      * fold s1; fold s2.
        rewrite <- evalRle_pushRle.
        replace (k1 + 2 * totalRes + 2 * (q * (r1_res s1 + r1_res s2)))%N
          with (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)))%N by lia.
        assert (Hrem : rem = 0%N \/ rem = 1%N) by lia.
        destruct Hrem as [Hrem | Hrem]; rewrite Hrem; cbn [N.eqb Pos.eqb].
        -- rewrite npow_0; cbn [Str_app].
           apply (ih _ phase _ R hrest hR k1).
        -- rewrite npow_1.
           eapply evstep_trans.
           ++ apply (stepR1StarWordL_sound item phase _ _ hitem hR_rest
                (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)))%N).
           ++ fold s1.
              rewrite <- evalRle_pushRlePos_one.
              replace (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2)) + 2 * r1_res s1)%N
                with (k1 + 2 * (totalRes + q * (r1_res s1 + r1_res s2) + r1_res s1))%N by lia.
              apply (ih _ (r1_phase s1) _ R hrest hR k1).
Qed.

Notation modeCfg := TM1.modeCfg.

Notation stepOneTokPure := TM1.stepOneTokPure.

Notation stepOneTokPure_sound := TM1.stepOneTokPure_sound.

Notation stepOneWordPureL := TM1.stepOneWordPureL.

Notation stepOneWordPureL_sound := TM1.stepOneWordPureL_sound.

Notation stepOneWordPureL_same_pow := TM1.stepOneWordPureL_same_pow.

Notation stepOneWordPureL_alt_pow := TM1.stepOneWordPureL_alt_pow.

Notation stepOneTokL := TM1.stepOneTokL.

Lemma stepOneTokL_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : side)
  (h : stepOneTokL rle mode t = Some (rle', mode')) :
  modeCfg mode (evalRle rle) (tokR t *> r) -[ tm521 ]->* modeCfg mode' (evalRle rle') r.
Proof.
  destruct mode, t; try discriminate; inverts h;
  cbn [modeCfg]; rewrite ?evalRle_pushToksLtr, ?evalRle_pushRlePos_one;
  cbn [revWord wordL app]; rewrite ?app_nil_r, ?Str_app_assoc.
  - apply r0_Z.
  - apply r0_P.
  - apply r0_PTTTM_TAIL.
  - apply r1_Z.
  - apply r1_P.
  - apply r1Odd_Z.
  - apply r1Odd_P.
Qed.

Notation stepOneWordL := TM1.stepOneWordL.

Lemma stepOneWordL_sound : forall (w : list Tok) (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneWordL rle mode w = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (wordR (revWord w) *> r) -[ tm521 ]->* modeCfg mode' (evalRle rle') r.
Proof.
  induction w as [|t ts ih]; intros rle rle' mode mode' r h; cbn [stepOneWordL] in h.
  - inverts h; cbn [revWord wordR Str_app]; apply evstep_refl.
  - destruct (stepOneWordL rle mode ts) as [[rle1 mode1]|] eqn:H1; [|discriminate].
    cbn [revWord]; rewrite wordR_append; cbn [wordR]; rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply (ih rle rle1 mode mode1 (tokR t *> r) H1)|].
    apply (stepOneTokL_sound rle1 rle' mode1 mode' t r h).
Qed.

Notation stepOneBounceFuel := TM4.stepOneBounceFuel.

Lemma stepOneBounceFuel_sound : forall (fuel : nat) (item : list Tok) (count : N)
  (rle rle' : Rle) (mode mode' : Mode) (r : side),
  stepOneBounceFuel fuel item count rle mode = Some (rle', mode') ->
  modeCfg mode (evalRle rle) (npow (wordR (revWord item)) count *> r) -[ tm521 ]->*
  modeCfg mode' (evalRle rle') r.
Proof.
  induction fuel as [|fuel ih]; intros item count rle rle' mode mode' r h; cbn [stepOneBounceFuel] in h.
  - destruct (count =? 0)%N eqn:Hc0; [|discriminate].
    apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
  - destruct (count =? 0)%N eqn:Hc0.
    + apply N.eqb_eq in Hc0; subst count; inverts h; cbn; apply evstep_refl.
    + apply N.eqb_neq in Hc0.
      assert (Hc_split : count = ((count - 1) + 1)%N) by lia.
      destruct (modeEq mode R0_mode) eqn:Hm0.
      * destruct (isZpWord item) eqn:Hzp.
        -- inverts h; apply modeEq_eq in Hm0; subst mode.
           cbn [modeCfg]; rewrite evalRle_pushRlePos.
           assert (Hrev : isZpWord (revWord item) = true) by (rewrite isZpWord_revWord; exact Hzp).
           pose proof (r0_pow count (revWord item) (evalRle rle) r Hrev) as Hr0.
           rewrite revWord_revWord in Hr0; exact Hr0.
        -- destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
           rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
           eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
           exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
      * destruct (stepOneWordPureL mode item) as [[out1 mode1]|] eqn:Hp1; [|discriminate].
        destruct (modeEq mode1 mode) eqn:Hm1.
        -- inverts h; apply modeEq_eq in Hm1; subst mode1.
           rewrite evalRle_pushRlePos.
           exact (stepOneWordPureL_same_pow count item out1 mode' (evalRle rle) r Hp1).
        -- destruct (2 <=? count)%N eqn:Hle2.
           ++ destruct (stepOneWordPureL mode1 item) as [[out2 mode2]|] eqn:Hp2; [|discriminate].
              destruct (modeEq mode2 mode) eqn:Hm2.
              ** apply modeEq_eq in Hm2; subst mode2.
                 cbn zeta in h.
                 pose proof (N.div_mod count 2 ltac:(discriminate)) as Hdiv.
                 set (q := (count / 2)%N) in *.
                 set (rem := (count mod 2)%N) in *.
                 replace count with (2 * q + rem)%N at 1 by lia.
                 rewrite (npow_add (wordR (revWord item)) (2 * q)%N rem), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordPureL_alt_pow q item out1 out2 mode mode1 (evalRle rle) _ Hp1 Hp2)|].
                 rewrite <- evalRle_pushRle.
                 exact (ih item rem (pushRle (out2 ++ out1) q rle) rle' mode mode' r h).
              ** destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
                 rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
                 eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
                 exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
           ++ destruct (stepOneWordL rle mode item) as [[rle1 mode1']|] eqn:Hw; [|discriminate].
              rewrite Hc_split, (npow_succ_l (wordR (revWord item)) (count - 1)%N), Str_app_assoc.
              eapply evstep_trans; [apply (stepOneWordL_sound item rle rle1 mode mode1' _ Hw)|].
              exact (ih item (count - 1)%N rle1 rle' mode1' mode' r h).
Qed.

Local Opaque stepOneBounceFuel.

Notation simpleOneBounceCarry := TM4.simpleOneBounceCarry.

Lemma simpleOneBounceCarry_sound : forall (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : N),
  simpleOneBounceCarry rle mode rs k1 = Some (rle', kOut) ->
  modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1)) -[ tm521 ]->*
  carryCfg (evalRle rle') (evalWK kOut).
Proof.
  induction rs as [|[item count] rest ih]; intros rle rle' mode k1 kOut h; cbn [simpleOneBounceCarry] in h.
  - destruct (modeEq mode R0_mode) eqn:Hm; [|discriminate].
    inverts h; apply modeEq_eq in Hm; subst mode; cbn [modeCfg evalRStack].
    apply r0_end.
  - destruct (stepOneBounceFuel 3 item count rle mode) as [[rle1 mode1]|] eqn:Hb; [|discriminate].
    cbn [evalRStack].
    eapply evstep_trans; [apply (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ Hb)|].
    exact (ih rle1 rle' mode1 k1 kOut h).
Qed.

Notation hasSpecialWord := TM1.hasSpecialWord.

Notation hasSpecial := TM1.hasSpecial.

Notation runRightSweepStarCarry := TM4.runRightSweepStarCarry.

Lemma runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : N)
  (h : runRightSweepStarCarry rle mode rStack k1 = Some (rOut, kOut)) :
  modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) -[ tm521 ]->*
  carryCfg (evalRle rOut) (evalWK kOut).
Proof.
  unfold runRightSweepStarCarry in h.
  destruct (hasSpecial rStack) eqn:Hs.
  - exact (simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h).
  - destruct (modeEq mode R0_mode) eqn:Hm0.
    + destruct (copyRStack rle rStack) as [rle'|] eqn:Hc; [|discriminate].
      inverts h; apply modeEq_eq in Hm0; subst mode; cbn [modeCfg].
      eapply evstep_trans; [exact (proj2 (copyRStack_sound rStack rle rOut (evalWK k1) Hc))|].
      apply r0_end.
    + destruct (allZpStack rStack) eqn:Hall; [|discriminate].
      set (initPhase := negb (modeEq mode R1_mode)) in *.
      assert (Hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
        r1PhaseCfg initPhase (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0)%N))).
      { replace (k1 + 2 * 0)%N with k1 by lia.
        destruct mode; cbn in Hm0; try discriminate; reflexivity. }
      rewrite Hphase.
      pose proof (sweepStarLoop_sound rStack rle initPhase 0%N evalWK Hall hasRoundtrip_evalWK k1) as Hsw.
      cbn zeta in Hsw, h.
      set (res := sweepStarLoop rle initPhase 0%N rStack) in *.
      eapply evstep_trans; [exact Hsw|].
      destruct (snd (fst res)) eqn:Hfp.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1Odd_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [Z_tok] 1%N (fst (fst res))) (k1 + 2 * snd res)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
      * inversion h as [Hzt_eq]; clear h.
        pose proof (f_equal fst Hzt_eq) as Hfst; pose proof (f_equal snd Hzt_eq) as Hsnd;
        cbn [fst snd] in Hfst, Hsnd; subst rOut kOut.
        cbn [r1PhaseCfg]; eapply evstep_trans; [apply r1_end|].
        pose proof (stepZtToCarry_sound (pushRlePos [P_tok] 1%N (fst (fst res))) (k1 + 2 * snd res + 1)%N) as Hzt.
        rewrite evalRle_pushRlePos_one in Hzt; cbn [wordL app] in Hzt; rewrite app_nil_r in Hzt.
        exact Hzt.
Qed.

Local Opaque runRightSweepStarCarry.

Notation StepCarryRes := TM1.StepCarryRes.

Notation SCR_halt := TM1.SCR_halt.

Notation SCR_next := TM1.SCR_next.

Notation SCR_err := TM1.SCR_err.

Definition StepCarryValid (cfg : Q * tape) (res : StepCarryRes) : Prop :=
  match res with
  | SCR_halt => exists cfg', (cfg -[ tm521 ]->* cfg') /\ halted tm521 cfg'
  | SCR_next rOut kOut => cfg -[ tm521 ]->* carryCfg (evalRle rOut) (evalWK kOut)
  | SCR_err => False
  end.

Lemma stepCarryValid_of_stepStar (cfg1 cfg2 : Q * tape) (res : StepCarryRes)
  (hstep : cfg1 -[ tm521 ]->* cfg2) (hval : StepCarryValid cfg2 res) :
  StepCarryValid cfg1 res.
Proof.
  destruct res; cbn [StepCarryValid] in *.
  - destruct hval as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact hstep | exact h2] | exact hhalt].
  - eapply evstep_trans; [exact hstep | exact hval].
  - exact hval.
Qed.

Notation finishTurn := TM4.finishTurn.

Lemma finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : N)
  (hne : finishTurn rle mode rStack k1 <> SCR_err) :
  StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
    (finishTurn rle mode rStack k1).
Proof.
  unfold finishTurn in *.
  destruct (runRightSweepStarCarry rle mode rStack k1) as [[rOut kOut]|] eqn:Hr.
  - cbn [StepCarryValid].
    exact (runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut Hr).
  - exfalso; apply hne; reflexivity.
Qed.

Notation matchRule2 := TM1.matchRule2.

Lemma matchRule2_sound (t1 t2 : Tok) (out : list Tok) (mode : Mode) (r4 : Rle) (r : side)
  (h : matchRule2 t1 t2 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> evalRle r4) r -[ tm521 ]->*
  modeCfg mode (evalRle (pushToksLtr out r4)) r.
Proof.
  destruct t1, t2; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_WM.
  - apply turn_ZM.
  - apply turn_ZT.
  - apply turn_PT.
Qed.

Notation matchRule3 := TM1.matchRule3.

Lemma matchRule3_sound (t1 t2 t3 : Tok) (out : list Tok) (mode : Mode) (r5 : Rle) (r : side)
  (h : matchRule3 t1 t2 t3 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) r -[ tm521 ]->*
  modeCfg mode (evalRle (pushToksLtr out r5)) r.
Proof.
  destruct t1, t2, t3; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMU.
  - apply turn_ZTM.
  - apply turn_PTM.
  - apply turn_ZTW.
  - apply turn_PTW.
  - apply turn_ZTT.
  - apply turn_PTT.
Qed.

Notation matchRule4 := TM1.matchRule4.

Lemma matchRule4_sound (t1 t2 t3 t4 : Tok) (out : list Tok) (mode : Mode) (r6 : Rle) (r : side)
  (h : matchRule4 t1 t2 t3 t4 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> evalRle r6) r -[ tm521 ]->*
  modeCfg mode (evalRle (pushToksLtr out r6)) r.
Proof.
  destruct t1, t2, t3, t4; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZPMU.
  - apply turn_ZTTM.
  - apply turn_PTTM.
  - apply turn_MUTW.
  - apply turn_ZTTW.
  - apply turn_PTMT.
  - apply turn_ZTTT.
Qed.

Notation matchRule5 := TM1.matchRule5.

Lemma matchRule5_sound (t1 t2 t3 t4 t5 : Tok) (out : list Tok) (mode : Mode) (r7 : Rle) (r : side)
  (h : matchRule5 t1 t2 t3 t4 t5 = Some (out, mode)) :
  carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> tokL t4 *> tokL t5 *> evalRle r7) r -[ tm521 ]->*
  modeCfg mode (evalRle (pushToksLtr out r7)) r.
Proof.
  destruct t1, t2, t3, t4, t5; try discriminate; inverts h;
  cbn [modeCfg]; rewrite evalRle_pushToksLtr;
  cbn [revWord wordL app]; rewrite ?Str_app_assoc.
  - apply turn_ZMUTM.
  - apply turn_ZTTTM.
  - apply turn_PTTTW.
Qed.

Notation isEmptyRle := TM1.isEmptyRle.

Notation isEmptyRle_eq := TM1.isEmptyRle_eq.

Notation stepTurnFrom3 := TM4.stepTurnFrom3.

Lemma stepTurnFrom3_sound (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom3 t1 t2 t3 r5 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> tokL t3 *> evalRle r5) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom3 t1 t2 t3 r5 rStack k1).
Proof.
  unfold stepTurnFrom3 in *.
  destruct (matchRule3 t1 t2 t3) as [[out mode]|] eqn:Hm3.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule3_sound t1 t2 t3 out mode r5 _ Hm3)
      (finishTurn_sound (pushToksLtr out r5) mode rStack k1 hne)).
  - destruct (popLastTok r5) as [[t4 r6]|] eqn:Hp4; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r5 t4 r6 Hp4).
    destruct (matchRule4 t1 t2 t3 t4) as [[out mode]|] eqn:Hm4.
    + exact (stepCarryValid_of_stepStar _ _ _
        (matchRule4_sound t1 t2 t3 t4 out mode r6 _ Hm4)
        (finishTurn_sound (pushToksLtr out r6) mode rStack k1 hne)).
    + destruct (popLastTok r6) as [[t5 r7]|] eqn:Hp5; [|exfalso; apply hne; reflexivity].
      rewrite (popLastTok_sound r6 t5 r7 Hp5).
      destruct (matchRule5 t1 t2 t3 t4 t5) as [[out mode]|] eqn:Hm5; [|exfalso; apply hne; reflexivity].
      exact (stepCarryValid_of_stepStar _ _ _
        (matchRule5_sound t1 t2 t3 t4 t5 out mode r7 _ Hm5)
        (finishTurn_sound (pushToksLtr out r7) mode rStack k1 hne)).
Qed.

Notation stepTurnFrom2 := TM4.stepTurnFrom2.

Lemma stepTurnFrom2_sound (t1 t2 : Tok) (r4 rStack : Rle) (k1 : N)
  (hne : stepTurnFrom2 t1 t2 r4 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (tokL t1 *> tokL t2 *> evalRle r4) (evalRStack rStack (evalWK k1)))
    (stepTurnFrom2 t1 t2 r4 rStack k1).
Proof.
  unfold stepTurnFrom2 in *.
  destruct (matchRule2 t1 t2) as [[out mode]|] eqn:Hm2.
  - exact (stepCarryValid_of_stepStar _ _ _
      (matchRule2_sound t1 t2 out mode r4 _ Hm2)
      (finishTurn_sound (pushToksLtr out r4) mode rStack k1 hne)).
  - destruct (popLastTok r4) as [[t3 r5]|] eqn:Hp3; [|exfalso; apply hne; reflexivity].
    rewrite (popLastTok_sound r4 t3 r5 Hp3).
    destruct (tokEq t1 T_tok) eqn:Ht1.
    + destruct (tokEq t2 M_tok) eqn:Hm2'.
      * destruct (tokEq t3 U_tok) eqn:Hu3.
        -- destruct (isEmptyRle r5) eqn:He; [|exfalso; apply hne; reflexivity].
           apply tokEq_eq in Ht1; apply tokEq_eq in Hm2'; apply tokEq_eq in Hu3; apply isEmptyRle_eq in He.
           subst t1 t2 t3 r5.
           eapply stepCarryValid_of_stepStar; [|exact (finishTurn_sound _ R1_mode rStack k1 hne)].
           cbn [evalRle npow Pos.to_nat wordL app modeCfg].
           apply turn_UMT.
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
    + destruct (tokEq t1 U_tok) eqn:Hu1.
      * destruct (tokEq t2 T_tok) eqn:Ht2.
        -- destruct (tokEq t3 Z_tok) eqn:Hz3.
           ++ apply tokEq_eq in Hu1; apply tokEq_eq in Ht2; apply tokEq_eq in Hz3.
              subst t1 t2 t3.
              cbn [StepCarryValid].
              eexists; split; [apply turn_ZTU_halt | reflexivity].
           ++ exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
        -- exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
      * exact (stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne).
Qed.

Notation stepTurnaround := TM4.stepTurnaround.

Lemma stepTurnaround_sound (r2 rStack : Rle) (k1 : N)
  (hne : stepTurnaround r2 rStack k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
    (stepTurnaround r2 rStack k1).
Proof.
  unfold stepTurnaround in *.
  destruct (popLastTok r2) as [[t1 r3]|] eqn:Hp1; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r2 t1 r3 Hp1).
  destruct (popLastTok r3) as [[t2 r4]|] eqn:Hp2; [|exfalso; apply hne; reflexivity].
  rewrite (popLastTok_sound r3 t2 r4 Hp2).
  destruct (tokEq t1 M_tok) eqn:Hm1.
  - destruct (tokEq t2 U_tok) eqn:Hu2.
    + destruct (isEmptyRle r4) eqn:He; [|exfalso; apply hne; reflexivity].
      apply tokEq_eq in Hm1; apply tokEq_eq in Hu2; apply isEmptyRle_eq in He.
      subst t1 t2 r4.
      eapply stepCarryValid_of_stepStar; [|exact (finishTurn_sound _ R1_mode rStack k1 hne)].
      cbn [evalRle npow Pos.to_nat wordL app modeCfg].
      apply turn_UM.
    + exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
  - exact (stepTurnFrom2_sound t1 t2 r4 rStack k1 hne).
Qed.

Local Opaque stepTurnaround.

Notation special_ZTM_loop := TM1.special_ZTM_loop.

Notation special_PT_loop := TM1.special_PT_loop.

Notation special_ZTW_loop := TM1.special_ZTW_loop.

Notation stepSpecialLoops := TM4.stepSpecialLoops.

Lemma stepSpecialLoops_sound (r2 rStack : Rle) (k1 : N) (res : StepCarryRes)
  (h : stepSpecialLoops r2 rStack k1 = Some res) (hne : res <> SCR_err) :
  StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res.
Proof.
  unfold stepSpecialLoops in h.
  destruct (popLastTok r2) as [[t1 r2a]|] eqn:Hp1; [|discriminate].
  rewrite (popLastTok_sound r2 t1 r2a Hp1).
  destruct t1; try discriminate.
  -  
    destruct (popTok M_tok r2a) as [rest|] eqn:Hpm; [|discriminate].
    rewrite (popTok_sound M_tok r2a rest Hpm).
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N rest) as [mVal r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
    apply N.eqb_neq in Hm0.
    destruct (popTok Z_tok r3) as [r4|] eqn:Hpz; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h.
    rewrite Hcnt, (popTok_sound Z_tok r3 r4 Hpz).
    eapply stepCarryValid_of_stepStar; [apply carry_MU_to_pmuCfg|].
    eapply stepCarryValid_of_stepStar; [apply (pmu_loop mVal (tokL Z_tok *> evalRle r4))|].
    replace mVal with (1 + (mVal - 1))%N at 1 by lia.
    rewrite (npow_add (tokR Z_tok) 1%N (mVal - 1)%N), npow_1, Str_app_assoc.
    eapply stepCarryValid_of_stepStar; [apply pmuCfg_Z_turn|].
    eapply stepCarryValid_of_stepStar; [apply (r0_Z_loop (mVal - 1)%N)|].
    eapply stepCarryValid_of_stepStar; [apply r0_P|].
    set (r5 := pushRlePos [P_tok] 1%N (pushRle [Z_tok] (mVal - 1)%N (pushToksLtr [T_tok; W_tok; M_tok] r4))) in *.
    assert (Hr5 : tokL P_tok *> npow (tokL Z_tok) (mVal - 1)%N *> tokL M_tok *> tokL W_tok *> tokL T_tok *> evalRle r4 = evalRle r5).
    { unfold r5; rewrite evalRle_pushRlePos_one, evalRle_pushRle, evalRle_pushToksLtr.
      cbn [revWord wordL app]; rewrite app_nil_r, !Str_app_assoc; reflexivity. }
    rewrite Hr5.
    exact (finishTurn_sound r5 R0_mode rStack k1 hne).
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushToksLtr [T_tok; M_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTM_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    destruct (popTok T_tok r2a) as [rest|] eqn:Hpt; [|discriminate].
    rewrite (popTok_sound T_tok r2a rest Hpt).
    pose proof (proj2 (popTokCount_sound 8 Z_tok 0%N rest)) as Hcnt.
    destruct (popTokCount 8 Z_tok 0%N rest) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [Z_tok] b (pushToksLtr [T_tok; W_tok] r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_ZTW_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushToksLtr in Hcopy;
    cbn [revWord wordL app] in Hcopy; rewrite ?app_nil_r, !Str_app_assoc in Hcopy; cbn [Str_app] in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
  -  
    pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2a)) as Hcnt.
    destruct (popTokCount 8 P_tok 0%N r2a) as [b r3] eqn:Hpc.
    cbn [fst snd] in Hcnt; rewrite npow_0 in Hcnt; cbn [Str_app] in Hcnt.
    destruct (b =? 0)%N eqn:Hb0; [discriminate|].
    apply N.eqb_neq in Hb0.
    set (r3' := pushRlePos [P_tok] b (pushRlePos [T_tok] 1%N r3)) in *.
    destruct (copyRStack r3' rStack) as [r4|] eqn:Hc; [|inverts h; exfalso; apply hne; reflexivity].
    inversion h; subst res; clear h; cbn [StepCarryValid].
    destruct (copyRStack_sound rStack r3' r4 (evalWK (k1 + 2 * (b - 1))%N) Hc) as [Hrs Hcopy].
    pose proof (hasRoundtrip_stack rStack _ Hrs hasRoundtrip_evalWK) as hR.
    rewrite Hcnt.
    replace b with ((b - 1) + 1)%N at 1 by lia.
    eapply evstep_trans; [apply (special_PT_loop (b - 1)%N (evalRle r3) _ hR k1)|].
    replace (b - 1 + 1)%N with b by lia.
    unfold r3' in Hcopy; rewrite evalRle_pushRlePos, evalRle_pushRlePos_one in Hcopy;
    cbn [wordL app] in Hcopy; rewrite app_nil_r in Hcopy.
    eapply evstep_trans; [exact Hcopy|].
    pose proof (r0_end (k1 + 2 * (b - 1))%N (evalRle r4)) as Hr0.
    replace (k1 + 2 * (b - 1) + 2)%N with (k1 + 2 * b)%N in Hr0 by lia.
    exact Hr0.
Qed.

Local Opaque stepSpecialLoops.

Notation stepCarry := TM4.stepCarry.

Lemma stepCarry_sound (rle : Rle) (k1 : N) (hne : stepCarry rle k1 <> SCR_err) :
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarry rle k1).
Proof.
  pose proof (popCarryLoop_sound 80 rle [] (evalWK k1)) as Hp.
  cbn [evalRStack] in Hp.
  unfold stepCarry in *.
  destruct (popCarryLoop 80 rle []) as [r2 rStack] eqn:Hpop.
  cbn [fst snd] in Hp.
  eapply stepCarryValid_of_stepStar; [exact Hp|].
  destruct (hasSpecial rStack) eqn:Hns.
  - exact (stepTurnaround_sound r2 rStack k1 hne).
  - destruct (stepSpecialLoops r2 rStack k1) as [res|] eqn:Hsl.
    + exact (stepSpecialLoops_sound r2 rStack k1 res Hsl hne).
    + exact (stepTurnaround_sound r2 rStack k1 hne).
Qed.

Local Opaque stepCarry.

Notation runCarryChunk := TM4.runCarryChunk.

Lemma runCarryChunk_sound : forall (n : nat) (rle : Rle) (k1 : N),
  runCarryChunk n rle k1 <> SCR_err ->
  StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (runCarryChunk n rle k1).
Proof.
  induction n as [|n ih]; intros rle k1 hne; cbn [runCarryChunk] in *.
  - cbn [StepCarryValid]; apply evstep_refl.
  - destruct (stepCarry rle k1) as [|rle' k1'|] eqn:Hs.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; exact Hv.
    + pose proof (stepCarry_sound rle k1 ltac:(rewrite Hs; discriminate)) as Hv.
      rewrite Hs in Hv; cbn [StepCarryValid] in Hv.
      exact (stepCarryValid_of_stepStar _ _ _ Hv (ih rle' k1' hne)).
    + exfalso; apply hne; reflexivity.
Qed.

Notation runCarryChunks := TM4.runCarryChunks.

Lemma runCarryChunks_sound : forall (chunks chunkSize : nat) (rle : Rle) (k1 : N),
  runCarryChunks chunks chunkSize rle k1 = true ->
  exists cfg', (carryCfg (evalRle rle) (evalWK k1) -[ tm521 ]->* cfg') /\ halted tm521 cfg'.
Proof.
  induction chunks as [|chunks ih]; intros chunkSize rle k1 h; cbn [runCarryChunks] in h; [discriminate|].
  destruct (runCarryChunk chunkSize rle k1) as [|rle' k1'|] eqn:Hc; [| |discriminate].
  - pose proof (runCarryChunk_sound chunkSize rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv; exact Hv.
  - pose proof (runCarryChunk_sound chunkSize rle k1 ltac:(rewrite Hc; discriminate)) as Hv.
    rewrite Hc in Hv; cbn [StepCarryValid] in Hv.
    destruct (ih chunkSize rle' k1' h) as [cfg' [h2 hhalt]].
    exists cfg'; split; [eapply evstep_trans; [exact Hv | exact h2] | exact hhalt].
Qed.

Local Transparent pushRlePos pushRle popTokCount stepZtToCarry
  popCarrySpecial popCarryLoop stepOneBounceFuel runRightSweepStarCarry
  stepTurnaround stepSpecialLoops stepCarry.

Notation initRle := TM4.initRle.

Lemma init_to_initRle144 :
  c0 -[ tm ]->* conj_cfg (carryCfg (evalRle initRle) (evalWK 1%N)).
Proof.
  exact (bmultiStep_sound tm 1901
    (mkCCfg A 0%sym []%sym []%sym)
    (mkCCfg C 1%sym
      [0; 1; 0; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1]%sym
      [0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 0; 1]%sym)
    ltac:(vm_compute; reflexivity)).
Qed.

Notation runCarryChunks_28_500 := TM4.runCarryChunks_28_500.

Theorem halt: halts tm c0.
Proof.
  destruct (runCarryChunks_sound 28 500 initRle 1%N runCarryChunks_28_500)
    as [cfg' [Hsteps Hhalted]].
  eapply halts_evstep.
  - exact (halted_halts tm (conj_cfg cfg') (halted_conj Hhalted)).
  - eapply evstep_trans; [exact init_to_initRle144 | exact (evstep_conj Hsteps)].
Qed.

End TM5.
Print Assumptions TM5.halt.
