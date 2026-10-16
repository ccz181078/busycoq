(** * Halting certificate for 1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.List Lists.Streams PeanoNat Lia NArith ZArith String.
Import ListNotations.

Set Default Goal Selector "!".

Definition tm : TM := Eval compute in (TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC").

Open Scope list_scope.

(* ---------- Binary N helpers and npow ---------- *)

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

(* ---------- Four Concrete Window Steppers ---------- *)

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

(* ---------- RLE Tokens, Modes, and Combinators ---------- *)

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


(* ========================================================================== *)
(* Section 6.4: Named Configurations & Verified Micro-Step Lemmas             *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(* Section 6.5: Loop & Suffix Transition Lemmas                               *)
(* ========================================================================== *)

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


(* ========================================================================== *)
(* Section 6.6: RLE Combinators & Sweep Soundness Lemmas                      *)
(* ========================================================================== *)

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
  - (* U_tok *)
    destruct (popLastTok r1) as [[t2 r2]|] eqn:Hp2; [|discriminate].
    rewrite (popLastTok_sound r1 t2 r2 Hp2).
    destruct t2; try discriminate.
    + (* M_tok *)
      pose proof (proj2 (popTokCount_sound 8 P_tok 0%N r2)) as Hpcs.
      destruct (popTokCount 8 P_tok 0%N r2) as [mVal r3] eqn:Hpc.
      cbn [fst snd] in Hpcs; rewrite npow_0 in Hpcs; cbn [Str_app] in Hpcs.
      rewrite Hpcs.
      destruct (mVal =? 0)%N eqn:Hm0; [discriminate|].
      destruct (popLastTok r3) as [[t3 r4]|] eqn:Hp3; [|discriminate].
      rewrite (popLastTok_sound r3 t3 r4 Hp3).
      destruct t3; try discriminate; inverts h.
      * (* M_tok *)
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL M_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_M_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
      * (* T_tok *)
        eapply evstep_trans; [apply carry_MU_to_pmuCfg|].
        eapply evstep_trans; [apply (pmu_loop mVal (tokL T_tok *> evalRle r4))|].
        eapply evstep_trans; [apply pmuCfg_T_to_carry|].
        rewrite evalRle_pushRlePos_one, !evalRStack_pushRlePos, npow_1.
        cbn [wordL revWord wordR app]; rewrite !app_nil_r.
        apply evstep_refl.
    + (* T_tok *)
      destruct (popTok P_tok r2) as [r3|] eqn:Hp3; [|discriminate].
      inverts h.
      rewrite (popTok_sound P_tok r2 r3 Hp3).
      rewrite evalRle_pushRlePos_one, evalRStack_pushRlePos, npow_1.
      cbn [wordL revWord wordR app]; rewrite !app_nil_r.
      apply carry_PTU.
  - (* M_tok *)
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
  - (* W_tok *)
    destruct (popToks [T_tok; T_tok; P_tok] r1) as [r4|] eqn:Hp2; [|discriminate].
    rewrite (popToks_sound _ r1 r4 Hp2).
    cbn [wordL app]; rewrite ?Str_app_assoc.
    change (tokL T_tok *> tokL T_tok *> tokL P_tok *> evalRle r4)
      with (npow (tokL T_tok) 2%N *> tokL P_tok *> evalRle r4).
    inverts h.
    rewrite !evalRStack_pushRlePos.
    cbn [revWord wordR app]; rewrite ?app_nil_r, ?Str_app_assoc.
    apply carry_PTTW.
  - (* T_tok *)
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
    + (* Z_tok, p1 = true *)
      apply r1Odd_Z.
    + (* Z_tok, p1 = false *)
      eapply evstep_trans; [apply r1_Z|].
      eapply evstep_trans; [apply (hR (tokL M_tok *> tokL Z_tok *> wordL out *> l) (k1 + 2 * res)%N)|].
      replace (k1 + 2 * res + 2)%N with (k1 + 2 * (res + 1))%N by lia.
      apply turn_ZM.
    + (* P_tok, p1 = true *)
      apply r1Odd_P.
    + (* P_tok, p1 = false *)
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


(* ========================================================================== *)
(* Section 6.7: Turnaround, Special Loops, and Macro-Step Soundness           *)
(* ========================================================================== *)

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
  - (* U_tok *)
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
  - (* M_tok *)
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
  - (* W_tok *)
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
  - (* T_tok *)
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


(* ========================================================================== *)
(* Section 7: Final Halting Theorem                                           *)
(* ========================================================================== *)

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

Lemma halt : halts tm c0.
Proof.
  destruct (runCarrySchedule_sound carry_sched 30%nat ckptRle_0 1%N 0inf runCarrySchedule_ok)
    as [cfg' [Hsteps Hhalted]].
  eapply halts_evstep.
  - exact (halted_halts tm cfg' Hhalted).
  - eapply evstep_trans; [exact init_to_ckpt0 | exact Hsteps].
Qed.

Print Assumptions halt.
