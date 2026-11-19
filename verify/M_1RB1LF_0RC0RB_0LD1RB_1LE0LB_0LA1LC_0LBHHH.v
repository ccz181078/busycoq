(** * Busy Beaver BB(6) Machine 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- *)

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Lists.Streams.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From BusyCoq Require Import Individual62.
Import ListNotations.

Local Open Scope string_scope.

Definition tm : TM := TM_from_str "1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---".

Local Close Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Module M284.

(* ========================================================================= *)
(* Section 1: Window Soundness & Macro Stepper (step284)                     *)
(* ========================================================================= *)

Definition WinState : Type := Q * bool * list Sym * list Sym.

Definition evalWin (l r : side) (q : Q) (dR : bool) (ls rs : list Sym) : Q * tape :=
  if dR then (ls *> l) {{ q }}> (rs *> r) else (ls *> l) <{{ q }} (rs *> r).

Definition stepWin (bL bR : bool) (st : WinState) : option WinState :=
  let '(q, dR, ls, rs) := st in
  if dR then
    match rs with
    | a :: rs0 =>
        match tm (q, a) with
        | Some (w, R, q') => Some (q', true, w :: ls, rs0)
        | Some (w, L, q') => Some (q', false, ls, w :: rs0)
        | None => None
        end
    | [] =>
        if bR then
          match tm (q, S0) with
          | Some (w, R, q') => Some (q', true, w :: ls, [])
          | Some (w, L, q') => Some (q', false, ls, [w])
          | None => None
          end
        else None
    end
  else
    match ls with
    | a :: ls0 =>
        match tm (q, a) with
        | Some (w, R, q') => Some (q', true, w :: ls0, rs)
        | Some (w, L, q') => Some (q', false, ls0, w :: rs)
        | None => None
        end
    | [] =>
        if bL then
          match tm (q, S0) with
          | Some (w, R, q') => Some (q', true, [w], rs)
          | Some (w, L, q') => Some (q', false, [], w :: rs)
          | None => None
          end
        else None
    end.

Fixpoint multiStepWin (bL bR : bool) (n : nat) (st : WinState) : option WinState :=
  match n with
  | 0 => Some st
  | S n' =>
      match stepWin bL bR st with
      | Some st' => multiStepWin bL bR n' st'
      | None => None
      end
  end.

Lemma stepWin_exec (l r : side) (q q' : Q) (dR dR' : bool) (ls rs ls' rs' : list Sym)
    (x : Sym) (ls0 rs0 : list Sym) :
  evalWin l r q dR ls rs = (q, (ls0 *> l, x, rs0 *> r)) ->
  (match tm (q, x) with
   | Some (w, R, q1) => Some (q1, true, w :: ls0, rs0)
   | Some (w, L, q1) => Some (q1, false, ls0, w :: rs0)
   | None => None
   end) = Some (q', dR', ls', rs') ->
  evalWin l r q dR ls rs -[ tm ]-> evalWin l r q' dR' ls' rs'.
Proof.
  intros Hev Hm.
  rewrite Hev.
  destruct (tm (q, x)) as [[[w dir] q1] |] eqn:Htm; [| discriminate].
  destruct dir.
  - inversion Hm; subst.
    cbn [evalWin Str_app].
    exact (step_left Htm).
  - inversion Hm; subst.
    cbn [evalWin Str_app].
    exact (step_right Htm).
Qed.

Lemma stepWin_sound (bL bR : bool) (l r : side)
    (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0)
    (q q' : Q) (dR dR' : bool) (ls rs ls' rs' : list Sym) :
  stepWin bL bR (q, dR, ls, rs) = Some (q', dR', ls', rs') ->
  evalWin l r q dR ls rs -[ tm ]-> evalWin l r q' dR' ls' rs'.
Proof.
  unfold stepWin.
  destruct dR.
  - destruct rs as [| a rs0].
    + destruct bR eqn:HbR; [| intros; discriminate].
      intros Hs.
      specialize (hR eq_refl); subst r.
      exact (stepWin_exec l (const S0) q q' true dR' ls [] ls' rs' S0 ls [] eq_refl Hs).
    + intros Hs.
      exact (stepWin_exec l r q q' true dR' ls (a :: rs0) ls' rs' a ls rs0 eq_refl Hs).
  - destruct ls as [| a ls0].
    + destruct bL eqn:HbL; [| intros; discriminate].
      intros Hs.
      specialize (hL eq_refl); subst l.
      exact (stepWin_exec (const S0) r q q' false dR' [] rs ls' rs' S0 [] rs eq_refl Hs).
    + intros Hs.
      exact (stepWin_exec l r q q' false dR' (a :: ls0) rs ls' rs' a ls0 rs eq_refl Hs).
Qed.

Lemma multiStepWin_sound (bL bR : bool) (l r : side)
    (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0) :
  forall (n : nat) (q q' : Q) (dR dR' : bool) (ls rs ls' rs' : list Sym),
    multiStepWin bL bR n (q, dR, ls, rs) = Some (q', dR', ls', rs') ->
    evalWin l r q dR ls rs -[ tm ]->> n / evalWin l r q' dR' ls' rs'.
Proof.
  induction n as [| n IH]; intros q q' dR dR' ls rs ls' rs' H.
  - cbn in H. inversion H; subst. apply multistep_0.
  - cbn [multiStepWin] in H.
    destruct (stepWin bL bR (q, dR, ls, rs)) as [[[[q1 dR1] ls1] rs1] |] eqn:Hsw;
      [| discriminate].
    eapply multistep_S.
    + exact (stepWin_sound bL bR l r hL hR q q1 dR dR1 ls rs ls1 rs1 Hsw).
    + exact (IH q1 q' dR1 dR' ls1 rs1 ls' rs' H).
Qed.

Lemma runWinPlus (bL bR : bool) (l r : side) (c1 c2 : Q * tape)
    (n : nat) (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0)
    (q : Q) (dR : bool) (ls rs : list Sym)
    (q' : Q) (dR' : bool) (ls' rs' : list Sym)
    (H1 : c1 = evalWin l r q dR ls rs)
    (H2 : c2 = evalWin l r q' dR' ls' rs')
    (Hw : multiStepWin bL bR (S n) (q, dR, ls, rs) = Some (q', dR', ls', rs')) :
  c1 -[ tm ]->+ c2.
Proof.
  subst c1 c2.
  eapply multistep_progress.
  exact (multiStepWin_sound bL bR l r hL hR (S n) q q' dR dR' ls rs ls' rs' Hw).
Qed.

Inductive Ones : Type := o1 | o2 | o3.
Inductive RSym : Type := r0 | r1 | r2.
Inductive Mode : Type := br | br1 | dl.

Definition State : Type := Mode * list (nat * Ones) * list RSym.

Fixpoint consZeros (n : nat) (s : side) : side :=
  match n with
  | 0 => s
  | S n' => S0 >> consZeros n' s
  end.

Definition encOnes (o : Ones) (s : side) : side :=
  match o with
  | o1 => S1 >> s
  | o2 => S1 >> S1 >> s
  | o3 => S1 >> S1 >> S1 >> s
  end.

Fixpoint encL (ls : list (nat * Ones)) : side :=
  match ls with
  | [] => const S0
  | (a, o) :: ls' => consZeros (S a) (encOnes o (encL ls'))
  end.

Fixpoint encR (rs : list RSym) : side :=
  match rs with
  | [] => const S0
  | r0 :: rs' => S0 >> S1 >> encR rs'
  | r1 :: rs' => S0 >> S1 >> S1 >> encR rs'
  | r2 :: rs' => S0 >> S0 >> S1 >> S1 >> encR rs'
  end.

Definition evalCfg (st : State) : Q * tape :=
  let '(m, ls, rs) := st in
  match m with
  | br => (encL ls) {{ B }}> (encR rs)
  | br1 => (S1 >> encL ls) {{ B }}> (encR rs)
  | dl => (encL ls) <{{ D }} (encR rs)
  end.

Definition addZ (ls : list (nat * Ones)) : list (nat * Ones) :=
  match ls with
  | [] => []
  | (a, o) :: ls' => (S a, o) :: ls'
  end.

Lemma zero_cons_encL (ls : list (nat * Ones)) :
  S0 >> encL ls = encL (addZ ls).
Proof.
  destruct ls as [| [a o] ls'].
  - cbn. symmetry. apply const_unfold.
  - reflexivity.
Qed.

Definition step284 (st : State) : option State :=
  let '(m, ls, rs) := st in
  match m with
  | br =>
      match rs with
      | [] => Some (dl, addZ ls, [])
      | r0 :: rs' => Some (br1, addZ ls, rs')
      | r1 :: rs' => Some (br, (0, o1) :: addZ ls, rs')
      | r2 :: rs' => Some (dl, addZ ls, r1 :: rs')
      end
  | br1 =>
      match rs with
      | [] => Some (dl, (0, o1) :: ls, [])
      | r0 :: rs' => Some (br1, (0, o1) :: ls, rs')
      | r1 :: rs' => Some (br, (0, o1) :: (0, o1) :: ls, rs')
      | r2 :: rs' => Some (dl, (0, o1) :: ls, r1 :: rs')
      end
  | dl =>
      match ls with
      | [] => Some (br1, [], r0 :: rs)
      | (0, o1) :: [] => Some (dl, [], r1 :: rs)
      | (0, o1) :: (0, o1) :: ls'' => Some (dl, ls'', r2 :: rs)
      | (0, o1) :: (0, o2) :: ls'' => Some (br, addZ ls'', r2 :: rs)
      | (0, o1) :: (0, o3) :: ls'' => Some (br, (0, o1) :: ls'', r2 :: rs)
      | (0, o1) :: (S a2, o') :: ls'' => Some (dl, (a2, o') :: ls'', r1 :: rs)
      | (0, o2) :: ls' => Some (br, (1, o1) :: ls', rs)
      | (0, o3) :: ls' => Some (br, (1, o2) :: ls', rs)
      | (1, o1) :: [] => Some (dl, [], r0 :: r0 :: rs)
      | (1, o1) :: (0, o1) :: ls'' => Some (br, addZ ls'', r0 :: r0 :: rs)
      | (1, o1) :: (0, o2) :: ls'' => Some (br, (0, o1) :: ls'', r0 :: r0 :: rs)
      | (1, o1) :: (0, o3) :: ls'' => Some (br, (0, o2) :: ls'', r0 :: r0 :: rs)
      | (1, o1) :: (S a2, o') :: ls'' => Some (dl, (a2, o') :: ls'', r0 :: r0 :: rs)
      | (1, o2) :: _ => None
      | (1, o3) :: _ => None
      | (2, o1) :: ls' => Some (br1, (0, o2) :: ls', rs)
      | (2, o2) :: ls' => Some (br1, (0, o3) :: ls', rs)
      | (2, o3) :: _ => None
      | (S (S (S a)), o) :: ls' => Some (br1, (a, o) :: ls', r0 :: rs)
      end
  end.

Lemma false_eq_true_elim {P : Prop} : false = true -> P.
Proof. intros H. discriminate H. Qed.

Lemma step284_sound (s1 s2 : State) :
  step284 s1 = Some s2 -> evalCfg s1 -[ tm ]->+ evalCfg s2.
Proof.
  destruct s1 as [[m ls] rs].
  destruct m.
  - (* br *)
    destruct rs as [| r rs'].
    + intros H; inversion H; subst.
      refine (runWinPlus false true (encL ls) (const S0) _ _ 1
        false_eq_true_elim (fun _ => eq_refl) B true [] [] D false [S0] [S0] eq_refl _ eq_refl).
      cbn [evalCfg evalWin Str_app encR].
      rewrite zero_cons_encL, <- const_unfold. reflexivity.
    + destruct r; intros H; inversion H; subst.
      * refine (runWinPlus false false (encL ls) (encR rs') _ _ 1
          false_eq_true_elim false_eq_true_elim B true [] [S0; S1] B true [S1; S0] [] eq_refl _ eq_refl).
        cbn [evalCfg evalWin Str_app]. rewrite zero_cons_encL. reflexivity.
      * refine (runWinPlus false false (encL ls) (encR rs') _ _ 2
          false_eq_true_elim false_eq_true_elim B true [] [S0; S1; S1] B true [S0; S1; S0] [] eq_refl _ eq_refl).
        cbn [evalCfg evalWin Str_app encL consZeros encOnes]. rewrite zero_cons_encL. reflexivity.
      * refine (runWinPlus false false (encL ls) (S1 >> S1 >> encR rs') _ _ 1
          false_eq_true_elim false_eq_true_elim B true [] [S0; S0] D false [S0] [S0] eq_refl _ eq_refl).
        cbn [evalCfg evalWin Str_app encR]. rewrite zero_cons_encL. reflexivity.
  - (* br1 *)
    destruct rs as [| r rs'].
    + intros H; inversion H; subst.
      refine (runWinPlus false true (encL ls) (const S0) _ _ 1
        false_eq_true_elim (fun _ => eq_refl) B true [S1] [] D false [S0; S1] [S0] eq_refl _ eq_refl).
      cbn [evalCfg evalWin Str_app encL consZeros encOnes encR].
      rewrite <- const_unfold. reflexivity.
    + destruct r; intros H; inversion H; subst.
      * exact (runWinPlus false false (encL ls) (encR rs') _ _ 1
          false_eq_true_elim false_eq_true_elim B true [S1] [S0; S1] B true [S1; S0; S1] [] eq_refl eq_refl eq_refl).
      * exact (runWinPlus false false (encL ls) (encR rs') _ _ 2
          false_eq_true_elim false_eq_true_elim B true [S1] [S0; S1; S1] B true [S0; S1; S0; S1] [] eq_refl eq_refl eq_refl).
      * exact (runWinPlus false false (encL ls) (S1 >> S1 >> encR rs') _ _ 1
          false_eq_true_elim false_eq_true_elim B true [S1] [S0; S0] D false [S0; S1] [S0] eq_refl eq_refl eq_refl).
  - (* dl *)
    destruct ls as [| [a o] ls'].
    + intros H; inversion H; subst.
      exact (runWinPlus true false (const S0) (encR rs) _ _ 2
        (fun _ => eq_refl) false_eq_true_elim D false [] [] B true [S1] [S0; S1] eq_refl eq_refl eq_refl).
    + destruct a as [| [| [| a]]].
      * (* a = 0 *)
        destruct o.
        -- (* o1 *)
           destruct ls' as [| [a2 o'] ls''].
           ++ intros H; inversion H; subst.
              exact (runWinPlus true false (const S0) (encR rs) _ _ 2
                (fun _ => eq_refl) false_eq_true_elim D false [S0; S1] [] D false [] [S0; S1; S1] eq_refl eq_refl eq_refl).
           ++ destruct a2 as [| a2'].
              ** destruct o'; intros H; inversion H; subst.
                 --- destruct ls'' as [| [a3 o3] ls3].
                     +++ refine (runWinPlus false false (const S0) (encR rs) _ _ 5
                           false_eq_true_elim false_eq_true_elim
                           D false [S0; S1; S0; S1; S0] [] D false [S0] [S0; S0; S1; S1] _ eq_refl eq_refl).
                         cbn. rewrite <- const_unfold. reflexivity.
                     +++ exact (runWinPlus false false (tl (encL ((a3, o3) :: ls3))) (encR rs) _ _ 5
                           false_eq_true_elim false_eq_true_elim
                           D false [S0; S1; S0; S1; S0] [] D false [S0] [S0; S0; S1; S1] eq_refl eq_refl eq_refl).
                 --- refine (runWinPlus false false (encL ls'') (encR rs) _ _ 4
                       false_eq_true_elim false_eq_true_elim
                       D false [S0; S1; S0; S1; S1] [] B true [S0] [S0; S0; S1; S1] eq_refl _ eq_refl).
                     cbn [evalCfg evalWin Str_app encR]. rewrite zero_cons_encL. reflexivity.
                 --- exact (runWinPlus false false (encL ls'') (encR rs) _ _ 4
                       false_eq_true_elim false_eq_true_elim
                       D false [S0; S1; S0; S1; S1; S1] [] B true [S0; S1] [S0; S0; S1; S1] eq_refl eq_refl eq_refl).
              ** intros H; inversion H; subst.
                 exact (runWinPlus false false (encL ((a2', o') :: ls'')) (encR rs) _ _ 2
                   false_eq_true_elim false_eq_true_elim
                   D false [S0; S1; S0] [] D false [] [S0; S1; S1] eq_refl eq_refl eq_refl).
        -- (* o2 *)
           intros H; inversion H; subst.
           exact (runWinPlus false false (encL ls') (encR rs) _ _ 4
             false_eq_true_elim false_eq_true_elim
             D false [S0; S1; S1] [] B true [S0; S0; S1] [] eq_refl eq_refl eq_refl).
        -- (* o3 *)
           intros H; inversion H; subst.
           exact (runWinPlus false false (encL ls') (encR rs) _ _ 4
             false_eq_true_elim false_eq_true_elim
             D false [S0; S1; S1; S1] [] B true [S0; S0; S1; S1] [] eq_refl eq_refl eq_refl).
      * (* a = 1 *)
        destruct o; [| intros H; discriminate | intros H; discriminate].
        destruct ls' as [| [a2 o'] ls''].
        -- intros H; inversion H; subst.
           refine (runWinPlus true false (const S0) (encR rs) _ _ 5
             (fun _ => eq_refl) false_eq_true_elim
             D false [S0; S0; S1] [] D false [S0] [S0; S1; S0; S1] eq_refl _ eq_refl).
           cbn [evalCfg evalWin Str_app encL encR]. rewrite <- const_unfold. reflexivity.
        -- destruct a2 as [| a2'].
           ++ destruct o'; intros H; inversion H; subst.
              ** refine (runWinPlus false false (encL ls'') (encR rs) _ _ 4
                   false_eq_true_elim false_eq_true_elim
                   D false [S0; S0; S1; S0; S1] [] B true [S0] [S0; S1; S0; S1] eq_refl _ eq_refl).
                 cbn [evalCfg evalWin Str_app encR]. rewrite zero_cons_encL. reflexivity.
              ** exact (runWinPlus false false (encL ls'') (encR rs) _ _ 4
                   false_eq_true_elim false_eq_true_elim
                   D false [S0; S0; S1; S0; S1; S1] [] B true [S0; S1] [S0; S1; S0; S1] eq_refl eq_refl eq_refl).
              ** exact (runWinPlus false false (encL ls'') (encR rs) _ _ 4
                   false_eq_true_elim false_eq_true_elim
                   D false [S0; S0; S1; S0; S1; S1; S1] [] B true [S0; S1; S1] [S0; S1; S0; S1] eq_refl eq_refl eq_refl).
           ++ intros H; inversion H; subst.
              exact (runWinPlus false false (tl (encL ((a2', o') :: ls''))) (encR rs) _ _ 5
                false_eq_true_elim false_eq_true_elim
                D false [S0; S0; S1; S0; S0] [] D false [S0] [S0; S1; S0; S1] eq_refl eq_refl eq_refl).
      * (* a = 2 *)
        destruct o; [| | intros H; discriminate]; intros H; inversion H; subst.
        -- exact (runWinPlus false false (encL ls') (encR rs) _ _ 4
             false_eq_true_elim false_eq_true_elim
             D false [S0; S0; S0; S1] [] B true [S1; S0; S1; S1] [] eq_refl eq_refl eq_refl).
        -- exact (runWinPlus false false (encL ls') (encR rs) _ _ 4
             false_eq_true_elim false_eq_true_elim
             D false [S0; S0; S0; S1; S1] [] B true [S1; S0; S1; S1; S1] [] eq_refl eq_refl eq_refl).
      * (* a >= 3 *)
        intros H; inversion H; subst.
        exact (runWinPlus false false (encL ((a, o) :: ls')) (encR rs) _ _ 2
          false_eq_true_elim false_eq_true_elim
          D false [S0; S0; S0] [] B true [S1] [S0; S1] eq_refl eq_refl eq_refl).
Qed.

Fixpoint steps284 (n : nat) (s : State) : option State :=
  match n with
  | 0 => Some s
  | S n' =>
      match step284 s with
      | Some s' => steps284 n' s'
      | None => None
      end
  end.

Lemma steps284_add (m n : nat) (s : State) :
  steps284 (m + n) s =
  match steps284 m s with
  | Some s' => steps284 n s'
  | None => None
  end.
Proof.
  revert s. induction m as [| m IH]; intros s.
  - reflexivity.
  - cbn [Nat.add steps284].
    destruct (step284 s) as [s' |].
    + exact (IH s').
    + reflexivity.
Qed.

Definition MStar (s1 s2 : State) : Prop := exists n, steps284 n s1 = Some s2.
Definition MPlus (s1 s2 : State) : Prop := exists n, 0 < n /\ steps284 n s1 = Some s2.

Lemma mstar_refl (s : State) : MStar s s.
Proof. exists 0. reflexivity. Qed.

Lemma mstar_of_plus {s1 s2 : State} (h : MPlus s1 s2) : MStar s1 s2.
Proof. destruct h as [n [_ hn]]. exists n. exact hn. Qed.

Lemma mstar_trans {s1 s2 s3 : State} (h1 : MStar s1 s2) (h2 : MStar s2 s3) : MStar s1 s3.
Proof.
  destruct h1 as [m hm], h2 as [n hn].
  exists (m + n). rewrite steps284_add, hm. exact hn.
Qed.

Lemma mplus_trans {s1 s2 s3 : State} (h1 : MPlus s1 s2) (h2 : MPlus s2 s3) : MPlus s1 s3.
Proof.
  destruct h1 as [m [hmpos hm]], h2 as [n [_ hn]].
  exists (m + n). split; [lia |].
  rewrite steps284_add, hm. exact hn.
Qed.

Lemma mplus_star {s1 s2 s3 : State} (h1 : MPlus s1 s2) (h2 : MStar s2 s3) : MPlus s1 s3.
Proof.
  destruct h1 as [m [hmpos hm]], h2 as [n hn].
  exists (m + n). split; [lia |].
  rewrite steps284_add, hm. exact hn.
Qed.

Lemma mstar_plus {s1 s2 s3 : State} (h1 : MStar s1 s2) (h2 : MPlus s2 s3) : MPlus s1 s3.
Proof.
  destruct h1 as [m hm], h2 as [n [hnpos hn]].
  exists (m + n). split; [lia |].
  rewrite steps284_add, hm. exact hn.
Qed.

Lemma steps284_sound :
  forall (n : nat) (s1 s2 : State),
    0 < n -> steps284 n s1 = Some s2 -> evalCfg s1 -[ tm ]->+ evalCfg s2.
Proof.
  induction n as [| n IH]; intros s1 s2 Hpos H.
  - lia.
  - destruct n as [| n'].
    + cbn in H. destruct (step284 s1) as [s' |] eqn:Hs; [| discriminate].
      inversion H; subst. exact (step284_sound s1 s2 Hs).
    + cbn [steps284] in H.
      destruct (step284 s1) as [s' |] eqn:Hs; [| discriminate].
      eapply progress_trans.
      * exact (step284_sound s1 s' Hs).
      * apply IH; [lia | exact H].
Qed.

Lemma mplus_sound {s1 s2 : State} (h : MPlus s1 s2) :
  evalCfg s1 -[ tm ]->+ evalCfg s2.
Proof.
  destruct h as [n [Hpos Hn]].
  exact (steps284_sound n s1 s2 Hpos Hn).
Qed.

Lemma init_to_br1 : c0 -[ tm ]->+ evalCfg (br1, [], []).
Proof.
  exact (runWinPlus true true (const S0) (const S0) _ _ 0
    (fun _ => eq_refl) (fun _ => eq_refl) A true [] [] B true [S1] [] eq_refl eq_refl eq_refl).
Qed.

Definition cp682 : State :=
  (br, [(0, o1); (1, o1); (1, o1); (1, o1); (1, o1); (1, o1);
        (0, o1); (0, o1); (0, o1); (1, o1); (0, o1); (0, o1);
        (1, o1); (0, o1); (0, o1); (2, o1); (2, o1); (0, o1);
        (0, o1); (2, o1); (0, o1); (0, o1)], []).

Lemma br1_to_cp682 : MPlus (br1, [], []) cp682.
Proof.
  exists 682. split; [lia | vm_compute; reflexivity].
Qed.

(* ========================================================================= *)
(* Section 2: Bijective Base-2 Algebra & Repetition Builders                 *)
(* ========================================================================= *)

Fixpoint rep1 (k : nat) (u : list (nat * Ones)) : list (nat * Ones) :=
  match k with
  | 0 => u
  | S k' => (1, o1) :: rep1 k' u
  end.

Fixpoint repBlk (k : nat) (u : list (nat * Ones)) : list (nat * Ones) :=
  match k with
  | 0 => u
  | S k' => (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k' u
  end.

Fixpoint repL0 (k : nat) (u : list (nat * Ones)) : list (nat * Ones) :=
  match k with
  | 0 => u
  | S k' => (0, o1) :: repL0 k' u
  end.

Fixpoint repL00 (k : nat) (u : list (nat * Ones)) : list (nat * Ones) :=
  match k with
  | 0 => u
  | S k' => (0, o1) :: (0, o1) :: repL00 k' u
  end.

Fixpoint repL2 (k : nat) (u : list (nat * Ones)) : list (nat * Ones) :=
  match k with
  | 0 => u
  | S k' => (2, o1) :: repL2 k' u
  end.

Fixpoint repR0 (k : nat) (rs : list RSym) : list RSym :=
  match k with
  | 0 => rs
  | S k' => r0 :: repR0 k' rs
  end.

Fixpoint repR00 (k : nat) (rs : list RSym) : list RSym :=
  match k with
  | 0 => rs
  | S k' => r0 :: r0 :: repR00 k' rs
  end.

Fixpoint repR1 (k : nat) (rs : list RSym) : list RSym :=
  match k with
  | 0 => rs
  | S k' => r1 :: repR1 k' rs
  end.

Fixpoint repR2 (k : nat) (rs : list RSym) : list RSym :=
  match k with
  | 0 => rs
  | S k' => r2 :: repR2 k' rs
  end.

Fixpoint repR1001 (k : nat) (rs : list RSym) : list RSym :=
  match k with
  | 0 => rs
  | S k' => r1 :: r0 :: r0 :: r1 :: repR1001 k' rs
  end.

Lemma repBlk_snoc (k : nat) (u : list (nat * Ones)) :
  repBlk k ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u) = repBlk (S k) u.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma repL0_snoc (k : nat) (u : list (nat * Ones)) :
  repL0 k ((0, o1) :: u) = (0, o1) :: repL0 k u.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma repL0_add (m n : nat) (u : list (nat * Ones)) :
  repL0 (m + n) u = repL0 m (repL0 n u).
Proof.
  induction m as [| m IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma repL0_double (k : nat) (u : list (nat * Ones)) :
  repL0 (2 * k) u = repL00 k u.
Proof.
  induction k as [| k IH]; [reflexivity |].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [repL0 repL00]. rewrite IH. reflexivity.
Qed.

Lemma repR0_double (k : nat) (rs : list RSym) :
  repR0 (2 * k) rs = repR00 k rs.
Proof.
  induction k as [| k IH]; [reflexivity |].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [repR0 repR00]. rewrite IH. reflexivity.
Qed.

Lemma repR1_snoc (k : nat) (rs : list RSym) :
  repR1 k (r1 :: rs) = r1 :: repR1 k rs.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma repR2_snoc (k : nat) (rs : list RSym) :
  repR2 k (r2 :: rs) = r2 :: repR2 k rs.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma repL2_snoc (k : nat) (u : list (nat * Ones)) :
  repL2 k ((2, o1) :: u) = (2, o1) :: repL2 k u.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Fixpoint encB (u : list bool) : list (nat * Ones) :=
  match u with
  | [] => []
  | false :: u' => (0, o1) :: (0, o1) :: encB u'
  | true :: u' => (2, o1) :: encB u'
  end.

Fixpoint valB (u : list bool) : nat :=
  match u with
  | [] => 0
  | false :: u' => 1 + 2 * valB u'
  | true :: u' => 2 + 2 * valB u'
  end.

Fixpoint valW (u : list bool) : nat :=
  match u with
  | [] => 0
  | false :: u' => 2 * valW u'
  | true :: u' => 1 + 2 * valW u'
  end.

Fixpoint incB (u : list bool) : list bool :=
  match u with
  | [] => [false]
  | false :: u' => true :: u'
  | true :: u' => false :: incB u'
  end.

Fixpoint addB (k : nat) (u : list bool) : list bool :=
  match k with
  | 0 => u
  | S k' => addB k' (incB u)
  end.

Lemma pow2_ge_1 (k : nat) : 1 <= 2 ^ k.
Proof.
  induction k as [| k IH]; cbn; lia.
Qed.

Lemma pow2_S_eq (k : nat) : 2 ^ (S k) = 2 * 2 ^ k.
Proof.
  cbn [Nat.pow]. lia.
Qed.

Lemma valB_incB (u : list bool) : valB (incB u) = valB u + 1.
Proof.
  induction u as [| b u IH]; [reflexivity |].
  destruct b; cbn [incB valB]; lia.
Qed.

Lemma valB_addB (k : nat) (u : list bool) : valB (addB k u) = valB u + k.
Proof.
  revert u. induction k as [| k IH]; intros u.
  - cbn [addB]. lia.
  - cbn [addB]. rewrite IH, valB_incB. lia.
Qed.

Lemma valB_eq_pow_add_valW (u : list bool) :
  valB u + 1 = 2 ^ (length u) + valW u.
Proof.
  induction u as [| b u IH]; [reflexivity |].
  destruct b; cbn [valB valW length]; rewrite pow2_S_eq; lia.
Qed.

Lemma need_le_valB (u : list bool) :
  2 ^ (length u) + 2 * valW u <= 2 * valB u + 1.
Proof.
  pose proof (valB_eq_pow_add_valW u) as H1.
  pose proof (pow2_ge_1 (length u)) as H2.
  lia.
Qed.

Lemma encB_rep_true (k : nat) (u : list bool) :
  encB (repeat true k ++ u) = repL2 k (encB u).
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma encB_rep_false (k : nat) (u : list bool) :
  encB (repeat false k ++ u) = repL00 k (encB u).
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma valB_rep_true (k : nat) (u : list bool) :
  valB (repeat true k ++ u) + 2 = 2 ^ k * (valB u + 2).
Proof.
  induction k as [| k IH]; [cbn; lia |].
  cbn [repeat app valB]. rewrite pow2_S_eq. nia.
Qed.

Lemma valB_rep_false (k : nat) (u : list bool) :
  valB (repeat false k ++ u) + 1 = 2 ^ k * (valB u + 1).
Proof.
  induction k as [| k IH]; [cbn; lia |].
  cbn [repeat app valB]. rewrite pow2_S_eq. nia.
Qed.

Inductive BitDecomp : Type :=
  | allTrue (a : nat)
  | allFalse (a : nat)
  | trueThenFalse (a : nat) (t : list bool)
  | falseThenTrue (a : nat) (t : list bool).

Definition evalDecomp (d : BitDecomp) : list bool :=
  match d with
  | allTrue a => repeat true a
  | allFalse a => repeat false (S a)
  | trueThenFalse a t => repeat true (S a) ++ false :: t
  | falseThenTrue a t => repeat false (S a) ++ true :: t
  end.

Lemma decomp_complete (s : list bool) : exists d : BitDecomp, s = evalDecomp d.
Proof.
  induction s as [| b s' [d Hd]]; [exists (allTrue 0); reflexivity |].
  subst s'.
  destruct b.
  - destruct d as [a | a | a t | a t].
    + exists (allTrue (S a)). reflexivity.
    + exists (trueThenFalse 0 (repeat false a)). reflexivity.
    + exists (trueThenFalse (S a) t). reflexivity.
    + exists (trueThenFalse 0 (repeat false a ++ true :: t)). reflexivity.
  - destruct d as [a | a | a t | a t].
    + destruct a as [| a'].
      * exists (allFalse 0). reflexivity.
      * exists (falseThenTrue 0 (repeat true a')). reflexivity.
    + exists (allFalse (S a)). reflexivity.
    + exists (falseThenTrue 0 (repeat true a ++ false :: t)). reflexivity.
    + exists (falseThenTrue (S a) t). reflexivity.
Qed.

Ltac msteps k := exists k; split; [lia | vm_compute; reflexivity].

(* ========================================================================= *)
(* Section 3: Call1, Call0, Call1N, Call0N & Defect Erasure                  *)
(* ========================================================================= *)

Definition Call1 (u u' : list (nat * Ones)) : Prop :=
  forall rs : list RSym, MPlus (dl, (1, o1) :: u, rs) (br1, (0, o1) :: u', rs).

Definition Call0 (u u' : list (nat * Ones)) : Prop :=
  forall rs : list RSym,
    MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, rs)
          (br, (0, o1) :: (0, o1) :: (0, o1) :: u', rs).

Fixpoint Call1N (k : nat) (u u' : list (nat * Ones)) : Prop :=
  match k with
  | 0 => u = u'
  | S k' => exists v, Call1 u v /\ Call1N k' v u'
  end.

Fixpoint Call0N (k : nat) (u u' : list (nat * Ones)) : Prop :=
  match k with
  | 0 => u = u'
  | S k' => exists v, Call0 u v /\ Call0N k' v u'
  end.

Lemma call1N_add {m n : nat} {u v w : list (nat * Ones)}
    (h1 : Call1N m u v) (h2 : Call1N n v w) : Call1N (m + n) u w.
Proof.
  revert u h1. induction m as [| m IH]; intros u h1.
  - cbn in h1. subst v. exact h2.
  - destruct h1 as [x [hstep hrest]].
    cbn [Nat.add Call1N].
    exists x. split; [exact hstep | exact (IH x hrest)].
Qed.

Lemma call1_nil : Call1 [] [(0, o1); (0, o1)].
Proof. intros rs. msteps 5. Qed.

Lemma call1_erase_end : Call1 [(0, o1)] [].
Proof. intros rs. msteps 3. Qed.

Lemma call1_00 (u : list (nat * Ones)) :
  Call1 ((0, o1) :: (0, o1) :: u) ((2, o1) :: u).
Proof. intros rs. msteps 3. Qed.

Lemma call1_02 (u : list (nat * Ones)) :
  Call1 ((0, o1) :: (2, o1) :: u) ((4, o1) :: u).
Proof. intros rs. msteps 3. Qed.

Lemma call1_4 (u : list (nat * Ones)) :
  Call1 ((4, o1) :: u) ((0, o1) :: (0, o1) :: (0, o1) :: u).
Proof. intros rs. msteps 5. Qed.

Lemma call1_M1 (u : list (nat * Ones)) :
  Call1 ((1, o1) :: (0, o1) :: (0, o2) :: u)
        ((1, o1) :: (0, o1) :: (0, o2) :: u).
Proof. intros rs. msteps 8. Qed.

Lemma call1_2 {u u' : list (nat * Ones)} (h : Call1 u u') :
  Call1 ((2, o1) :: u) ((0, o1) :: (0, o1) :: u').
Proof.
  intros rs.
  assert (h1 : MPlus (dl, (1, o1) :: (2, o1) :: u, rs)
                     (dl, (1, o1) :: u, r0 :: r0 :: rs)) by msteps 1.
  pose proof (h (r0 :: r0 :: rs)) as h2.
  assert (h3 : MPlus (br1, (0, o1) :: u', r0 :: r0 :: rs)
                     (br1, (0, o1) :: (0, o1) :: (0, o1) :: u', rs)) by msteps 2.
  exact (mplus_trans h1 (mplus_trans h2 h3)).
Qed.

Lemma call1_100 {u u' : list (nat * Ones)} (h : Call0 u u') :
  Call1 ((1, o1) :: (0, o1) :: (0, o1) :: u)
        ((1, o1) :: (0, o1) :: (0, o1) :: u').
Proof.
  intros rs.
  assert (h1 : MPlus (dl, (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u, rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, r0 :: r0 :: rs)) by msteps 1.
  pose proof (h (r0 :: r0 :: rs)) as h2.
  assert (h3 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u', r0 :: r0 :: rs)
                     (br1, (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u', rs)) by msteps 2.
  exact (mplus_trans h1 (mplus_trans h2 h3)).
Qed.

Lemma call0_M11 (u : list (nat * Ones)) :
  Call0 ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: u)
        ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: u).
Proof. intros rs. msteps 22. Qed.

Lemma call0_2 {u u' : list (nat * Ones)} (h : Call1 u u') :
  Call0 ((2, o1) :: u) ((2, o1) :: u').
Proof.
  intros rs.
  assert (h1 : MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: u, rs)
                     (dl, (1, o1) :: u, r1 :: r2 :: rs)) by msteps 2.
  pose proof (h (r1 :: r2 :: rs)) as h2.
  assert (h3 : MPlus (br1, (0, o1) :: u', r1 :: r2 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: u', rs)) by msteps 6.
  exact (mplus_trans h1 (mplus_trans h2 h3)).
Qed.

Lemma call0_100 {u u1 u2 : list (nat * Ones)} (h1 : Call0 u u1) (h2 : Call0 u1 u2) :
  Call0 ((1, o1) :: (0, o1) :: (0, o1) :: u)
        ((1, o1) :: (0, o1) :: (0, o1) :: u2).
Proof.
  intros rs.
  assert (s1 : MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u, rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, r1 :: r2 :: rs)) by msteps 2.
  pose proof (h1 (r1 :: r2 :: rs)) as s2.
  assert (s3 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u1, r1 :: r2 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: u1, r0 :: r0 :: r1 :: rs)) by msteps 3.
  pose proof (h2 (r0 :: r0 :: r1 :: rs)) as s4.
  assert (s5 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u2, r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u2, rs)) by msteps 3.
  exact (mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 s5)))).
Qed.

Lemma call0_1100 {u u1 u2 : list (nat * Ones)} (h1 : Call0 u u1) (h2 : Call0 u1 u2) :
  Call0 ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u)
        ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u2).
Proof.
  intros rs.
  assert (s1 : MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u, rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, r1 :: r1 :: r2 :: rs)) by msteps 3.
  pose proof (h1 (r1 :: r1 :: r2 :: rs)) as s2.
  assert (s3 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u1, r1 :: r1 :: r2 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: u1, r1 :: r0 :: r0 :: r1 :: rs)) by msteps 5.
  pose proof (h2 (r1 :: r0 :: r0 :: r1 :: rs)) as s4.
  assert (s5 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u2, r1 :: r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u2, rs)) by msteps 4.
  exact (mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 s5)))).
Qed.

Lemma call0N_2 {m : nat} {u u' : list (nat * Ones)} (h : Call1N m u u') :
  Call0N m ((2, o1) :: u) ((2, o1) :: u').
Proof.
  revert u h. induction m as [| m IH]; intros u h.
  - cbn in h; subst u'; reflexivity.
  - destruct h as [v [hv hrest]].
    exists ((2, o1) :: v). split; [exact (call0_2 hv) | exact (IH v hrest)].
Qed.

Lemma call0N_100 {m : nat} {u u' : list (nat * Ones)} (h : Call0N (2 * m) u u') :
  Call0N m ((1, o1) :: (0, o1) :: (0, o1) :: u)
           ((1, o1) :: (0, o1) :: (0, o1) :: u').
Proof.
  revert u h. induction m as [| m IH]; intros u h.
  - cbn in h; subst u'; reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) in h by lia.
    destruct h as [v1 [h1 [v2 [h2 hrest]]]].
    exists ((1, o1) :: (0, o1) :: (0, o1) :: v2).
    split; [exact (call0_100 h1 h2) | exact (IH v2 hrest)].
Qed.

Lemma call0N_1100 {m : nat} {u u' : list (nat * Ones)} (h : Call0N (2 * m) u u') :
  Call0N m ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u)
           ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u').
Proof.
  revert u h. induction m as [| m IH]; intros u h.
  - cbn in h; subst u'; reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) in h by lia.
    destruct h as [v1 [h1 [v2 [h2 hrest]]]].
    exists ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: v2).
    split; [exact (call0_1100 h1 h2) | exact (IH v2 hrest)].
Qed.

Lemma call0N_repBlk (k m : nat) {u u' : list (nat * Ones)} (h : Call0N (m * 2 ^ k) u u') :
  Call0N m (repBlk k u) (repBlk k u').
Proof.
  revert m u h. induction k as [| k IH]; intros m u h.
  - cbn [repBlk]. replace m with (m * 2 ^ 0) by (cbn; lia). exact h.
  - cbn [repBlk]. apply call0N_1100. apply IH.
    replace (2 * m * 2 ^ k) with (m * 2 ^ (S k)) by (rewrite pow2_S_eq; nia).
    exact h.
Qed.

Lemma call0N_M11 (m : nat) (u : list (nat * Ones)) :
  Call0N m ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: u)
           ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: u).
Proof.
  induction m as [| m IH]; [reflexivity |].
  eexists. split; [exact (call0_M11 u) | exact IH].
Qed.

Lemma call1N_M1 (m : nat) (u : list (nat * Ones)) :
  Call1N m ((1, o1) :: (0, o1) :: (0, o2) :: u)
           ((1, o1) :: (0, o1) :: (0, o2) :: u).
Proof.
  induction m as [| m IH]; [reflexivity |].
  eexists. split; [exact (call1_M1 u) | exact IH].
Qed.

Lemma call1N_100 {m : nat} {u u' : list (nat * Ones)} (h : Call0N m u u') :
  Call1N m ((1, o1) :: (0, o1) :: (0, o1) :: u)
           ((1, o1) :: (0, o1) :: (0, o1) :: u').
Proof.
  revert u h. induction m as [| m IH]; intros u h.
  - cbn in h; subst u'; reflexivity.
  - destruct h as [v [hv hrest]].
    exists ((1, o1) :: (0, o1) :: (0, o1) :: v).
    split; [exact (call1_100 hv) | exact (IH v hrest)].
Qed.

Lemma call1_encB (u : list bool) : Call1 (encB u) (encB (incB u)).
Proof.
  induction u as [| b u IH]; [exact call1_nil |].
  destruct b; [exact (call1_2 IH) | exact (call1_00 (encB u))].
Qed.

Lemma call1N_encB (m : nat) (u : list bool) : Call1N m (encB u) (encB (addB m u)).
Proof.
  revert u. induction m as [| m IH]; intros u; [reflexivity |].
  exists (encB (incB u)). split; [exact (call1_encB u) | exact (IH (incB u))].
Qed.

Lemma call1N_00_even {q : nat} {x x' : list (nat * Ones)} (h : Call1N q x x') :
  Call1N (2 * q) ((0, o1) :: (0, o1) :: x) ((0, o1) :: (0, o1) :: x').
Proof.
  revert x h. induction q as [| q IH]; intros x h.
  - cbn in h; subst x'; reflexivity.
  - destruct h as [v [hv hrest]].
    replace (2 * S q) with (S (S (2 * q))) by lia.
    exists ((2, o1) :: x). split; [exact (call1_00 x) |].
    exists ((0, o1) :: (0, o1) :: v). split; [exact (call1_2 hv) | exact (IH v hrest)].
Qed.

Lemma call1N_00_odd {q : nat} {x x' : list (nat * Ones)} (h : Call1N q x x') :
  Call1N (2 * q + 1) ((0, o1) :: (0, o1) :: x) ((2, o1) :: x').
Proof.
  pose proof (call1N_00_even h) as h1.
  assert (h2 : Call1N 1 ((0, o1) :: (0, o1) :: x') ((2, o1) :: x')).
  { exists ((2, o1) :: x'). split; [exact (call1_00 x') | reflexivity]. }
  exact (call1N_add h1 h2).
Qed.

Lemma call1N_2_even {q : nat} {x x' : list (nat * Ones)} (h : Call1N q x x') :
  Call1N (2 * q) ((2, o1) :: x) ((2, o1) :: x').
Proof.
  revert x h. induction q as [| q IH]; intros x h.
  - cbn in h; subst x'; reflexivity.
  - destruct h as [v [hv hrest]].
    replace (2 * S q) with (S (S (2 * q))) by lia.
    exists ((0, o1) :: (0, o1) :: v). split; [exact (call1_2 hv) |].
    exists ((2, o1) :: v). split; [exact (call1_00 v) | exact (IH v hrest)].
Qed.

Lemma call1N_erase_0 (u : list bool) :
  forall m : nat, 2 ^ (length u) + 2 * valW u <= m ->
    exists v : list bool, Call1N m ((0, o1) :: encB u) (encB v) /\ valB v + 1 + 2 * valW u = m.
Proof.
  induction u as [| b r IH]; intros m hm.
  - destruct m as [| m']; [cbn in hm; lia |].
    exists (addB m' []). split.
    + exists ([] : list (nat * Ones)). split; [exact call1_erase_end | exact (call1N_encB m' [])].
    + rewrite valB_addB. cbn [valB valW]. lia.
  - destruct b.
    + (* b = true *)
      cbn [length valW] in hm. rewrite pow2_S_eq in hm.
      pose proof (pow2_ge_1 (length r)) as hp.
      assert (hm2 : 2 <= m) by lia.
      set (m2 := m - 2).
      pose proof (Nat.div_mod m2 2 ltac:(lia)) as hdm.
      pose proof (Nat.mod_upper_bound m2 2 ltac:(lia)) as hmu.
      assert (hq : 2 ^ (length r) + 2 * valW r <= m2 / 2) by lia.
      destruct (IH (m2 / 2) hq) as [v [hv_call hv_val]].
      assert (hpre : Call1N 2 ((0, o1) :: (2, o1) :: encB r)
                              ((0, o1) :: (0, o1) :: (0, o1) :: encB r)).
      { exists ((4, o1) :: encB r). split; [exact (call1_02 (encB r)) |].
        exists ((0, o1) :: (0, o1) :: (0, o1) :: encB r).
        split; [exact (call1_4 (encB r)) | reflexivity]. }
      destruct (Nat.eq_dec (m2 mod 2) 0) as [h0 | h1].
      * exists (false :: v). split.
        -- replace m with (2 + 2 * (m2 / 2)) by lia.
           exact (call1N_add hpre (call1N_00_even hv_call)).
        -- cbn [valB valW]. lia.
      * exists (true :: v). split.
        -- replace m with (2 + (2 * (m2 / 2) + 1)) by lia.
           exact (call1N_add hpre (call1N_00_odd hv_call)).
        -- cbn [valB valW]. lia.
    + (* b = false *)
      cbn [length valW] in hm. rewrite pow2_S_eq in hm.
      pose proof (Nat.div_mod m 2 ltac:(lia)) as hdm.
      pose proof (Nat.mod_upper_bound m 2 ltac:(lia)) as hmu.
      assert (hq : 2 ^ (length r) + 2 * valW r <= m / 2) by lia.
      destruct (IH (m / 2) hq) as [v [hv_call hv_val]].
      destruct (Nat.eq_dec (m mod 2) 0) as [h0 | h1].
      * exists (false :: v). split.
        -- replace m with (2 * (m / 2)) by lia.
           exact (call1N_00_even hv_call).
        -- cbn [valB valW]. lia.
      * exists (true :: v). split.
        -- replace m with (2 * (m / 2) + 1) by lia.
           exact (call1N_00_odd hv_call).
        -- cbn [valB valW]. lia.
Qed.

Lemma call0N_erase_2_0 (u : list bool) (C : nat) (hC : 2 ^ (length u) + 2 * valW u <= C) :
  exists v : list bool,
    Call0N C ((2, o1) :: (0, o1) :: encB u) (encB (true :: v)) /\
    valB (true :: v) + 4 * valW u = 2 * C.
Proof.
  destruct (call1N_erase_0 u C hC) as [v [hv hval]].
  exists v. split; [exact (call0N_2 hv) | cbn [valB]; lia].
Qed.

Lemma call0N_erase_2_2_0 (u : list bool) (q : nat) (hq : 2 ^ (length u) + 2 * valW u <= q) :
  exists v : list bool,
    Call0N (2 * q) ((2, o1) :: (2, o1) :: (0, o1) :: encB u) (encB (true :: true :: v)) /\
    valB (true :: true :: v) + 8 * valW u = 4 * q + 2.
Proof.
  destruct (call1N_erase_0 u q hq) as [v [hv hval]].
  exists v. split; [exact (call0N_2 (call1N_2_even hv)) | cbn [valB]; lia].
Qed.

Lemma call0N_erase_2_4 (u : list bool) (q : nat) (hq : 1 + (2 ^ (length u) + 2 * valW u) <= q) :
  exists v : list bool,
    Call0N (2 * q) ((2, o1) :: (4, o1) :: encB u) (encB (true :: true :: v)) /\
    valB (true :: true :: v) + 8 * valW u + 2 = 4 * q.
Proof.
  assert (hq1 : 2 ^ (length u) + 2 * valW u <= q - 1) by lia.
  destruct (call1N_erase_0 u (q - 1) hq1) as [v [hv hval]].
  assert (h1 : Call1N 1 ((4, o1) :: encB u) ((0, o1) :: (0, o1) :: (0, o1) :: encB u)).
  { exists ((0, o1) :: (0, o1) :: (0, o1) :: encB u). split; [exact (call1_4 (encB u)) | reflexivity]. }
  pose proof (call1N_add h1 (call1N_00_odd hv)) as htot.
  replace (1 + (2 * (q - 1) + 1)) with (2 * q) in htot by lia.
  exists v. split; [exact (call0N_2 htot) | cbn [valB]; lia].
Qed.

(* ========================================================================= *)
(* Section 4: BR1 Prefix, BR Prefix (IN/OUT), F_core, and BR Body Exits      *)
(* ========================================================================= *)

Lemma dl_0_1_sweep (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (dl, (0, o1) :: rep1 a u, rs) (dl, (0, o1) :: u, repR1 a rs).
Proof.
  revert rs. induction a as [| a IH]; intros rs; [apply mstar_refl |].
  cbn [rep1].
  assert (h1 : MPlus (dl, (0, o1) :: (1, o1) :: rep1 a u, rs)
                     (dl, (0, o1) :: rep1 a u, r1 :: rs)) by msteps 1.
  pose proof (IH (r1 :: rs)) as h2.
  rewrite repR1_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma br_r1_sweep (a b : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (br, (0, o1) :: rep1 b ((0, o1) :: u), repR1 a rs)
        (br, (0, o1) :: rep1 (a + b) ((0, o1) :: u), rs).
Proof.
  revert b. induction a as [| a IH]; intros b; [apply mstar_refl |].
  cbn [repR1].
  assert (h1 : MPlus (br, (0, o1) :: rep1 b ((0, o1) :: u), r1 :: repR1 a rs)
                     (br, (0, o1) :: (1, o1) :: rep1 b ((0, o1) :: u), repR1 a rs)) by msteps 1.
  pose proof (IH (S b)) as h2.
  replace (a + S b) with (S a + b) in h2 by lia.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma br1_loop_step (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u, repR1 (S a) (r0 :: r0 :: r2 :: rs))
        (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, repR1 a (r0 :: r0 :: r2 :: r1 :: rs)).
Proof.
  pose proof (br_r1_sweep (S a) 0 ((0, o1) :: u) (r0 :: r0 :: r2 :: rs)) as h1.
  rewrite Nat.add_0_r in h1.
  assert (hmid : MPlus (br, (0, o1) :: (1, o1) :: rep1 a ((0, o1) :: (0, o1) :: u), r0 :: r0 :: r2 :: rs)
                       (dl, (0, o1) :: rep1 a ((0, o1) :: (0, o1) :: u), r0 :: r0 :: r2 :: r1 :: rs)) by msteps 5.
  pose proof (dl_0_1_sweep a ((0, o1) :: (0, o1) :: u) (r0 :: r0 :: r2 :: r1 :: rs)) as h2.
  exact (mstar_plus h1 (mplus_star hmid h2)).
Qed.

Lemma br1_call0_loop (a b : nat) (u u' : list (nat * Ones)) (h : Call0N (S a) u u') :
  MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: u, repR1 a (r0 :: r0 :: r2 :: repR1 b []))
        (br, (0, o1) :: (0, o1) :: (0, o1) :: u', r0 :: r0 :: r2 :: repR1 (a + b) []).
Proof.
  revert b u h. induction a as [| a IH]; intros b u h.
  - destruct h as [v [hv hv']]. cbn in hv'; subst v.
    exact (hv (r0 :: r0 :: r2 :: repR1 b [])).
  - destruct h as [v [hv hrest]].
    pose proof (hv (repR1 (S a) (r0 :: r0 :: r2 :: repR1 b []))) as h1.
    pose proof (br1_loop_step a v (repR1 b [])) as h2.
    pose proof (IH (S b) v hrest) as h3.
    replace (a + S b) with (S a + b) in h3 by lia.
    exact (mplus_trans h1 (mplus_trans h2 h3)).
Qed.

Lemma br1_prefix_step (n : nat) {body body' : list (nat * Ones)}
    (hcall : Call0N (S n) ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body)
                          ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body')) :
  MPlus (br1, (0, o1) :: rep1 (2 + n) ((0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body), [])
        (br,  (0, o1) :: rep1 (3 + n) ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body'), []).
Proof.
  assert (h1 : MPlus (br1, (0, o1) :: (1, o1) :: (1, o1) :: rep1 n ((0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body), [])
                     (dl,  (0, o1) :: rep1 n ((0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body), [r0; r0; r2])) by msteps 3.
  pose proof (dl_0_1_sweep n ((0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body) [r0; r0; r2]) as h2.
  pose proof (br1_call0_loop n 0 ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body)
                                 ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body') hcall) as h3.
  rewrite Nat.add_0_r in h3.
  assert (h4 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body',
                          r0 :: r0 :: r2 :: repR1 n [])
                     (br1, (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body',
                          r1 :: r1 :: r1 :: r1 :: repR1 n [])) by msteps 15.
  assert (h5 : MPlus (br1, (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body',
                          r1 :: r1 :: r1 :: r1 :: repR1 n [])
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body',
                          repR1 (3 + n) [])) by msteps 1.
  pose proof (br_r1_sweep (3 + n) 0 ((0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: body') []) as h6.
  rewrite Nat.add_0_r in h6.
  exact (mplus_star (mplus_trans (mplus_star h1 h2) (mplus_trans h3 (mplus_trans h4 h5))) h6).
Qed.

Lemma br1_run (n k : nat) {body body' : list (nat * Ones)}
    (hcall : Call0N ((S n) * 2 ^ (S k)) body body') :
  MPlus (br1, (0, o1) :: rep1 (2 + n) ((0, o1) :: (0, o1) :: repBlk (S k) body), [])
        (br,  (0, o1) :: rep1 (3 + n) ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body'), []).
Proof.
  apply br1_prefix_step.
  exact (call0N_repBlk (S k) (S n) hcall).
Qed.

Lemma repR1001_snoc (k : nat) (rs : list RSym) :
  repR1001 k (r1 :: r0 :: r0 :: r1 :: rs) = repR1001 (S k) rs.
Proof.
  induction k as [| k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma br_in_peel (k : nat) (body : list (nat * Ones)) (rs : list RSym) :
  MStar (dl, (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body, r2 :: r2 :: rs)
        (dl, (1, o1) :: (0, o1) :: (0, o1) :: body, r2 :: r2 :: repR1001 k rs).
Proof.
  revert rs. induction k as [| k IH]; intros rs; [apply mstar_refl |].
  cbn [repBlk].
  assert (h1 : MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body,
                          r2 :: r2 :: rs)
                     (dl, (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body,
                          r2 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)) by msteps 19.
  pose proof (IH (r1 :: r0 :: r0 :: r1 :: rs)) as h2.
  rewrite repR1001_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma br_in (n k : nat) (body : list (nat * Ones)) :
  MPlus (br, (0, o1) :: rep1 (S n) ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body), [])
        (dl, (1, o1) :: (0, o1) :: (0, o1) :: body, r2 :: r2 :: repR1001 k (repR1 n [r0; r0])).
Proof.
  assert (h1 : MPlus (br, (0, o1) :: (1, o1) :: rep1 n ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body), [])
                     (dl, (0, o1) :: rep1 n ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body), [r0; r0])) by msteps 2.
  pose proof (dl_0_1_sweep n ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body) [r0; r0]) as h2.
  assert (h3 : MPlus (dl, (0, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body, repR1 n [r0; r0])
                     (dl, (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body, r2 :: r2 :: repR1 n [r0; r0])) by msteps 2.
  pose proof (br_in_peel k body (repR1 n [r0; r0])) as h4.
  exact (mplus_star (mplus_trans (mplus_star h1 h2) h3) h4).
Qed.

Lemma br_out_1001 (k : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (br, (0, o1) :: (0, o1) :: (0, o1) :: u, repR1001 k rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: repBlk k u, rs).
Proof.
  revert u. induction k as [| k IH]; intros u; [apply mstar_refl |].
  cbn [repR1001].
  assert (h1 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u, r1 :: r0 :: r0 :: r1 :: repR1001 k rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u, repR1001 k rs)) by msteps 4.
  pose proof (IH ((1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: u)) as h2.
  rewrite repBlk_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma br_out (n k : nat) (u : list (nat * Ones)) :
  MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u, repR1001 k (repR1 n [r0; r0]))
        (br1, (0, o1) :: rep1 (S n) ((0, o1) :: (0, o1) :: repBlk k u), []).
Proof.
  pose proof (br_out_1001 k u (repR1 n [r0; r0])) as h1.
  pose proof (br_r1_sweep n 0 ((0, o1) :: repBlk k u) [r0; r0]) as h2.
  rewrite Nat.add_0_r in h2.
  assert (h3 : MPlus (br, (0, o1) :: rep1 n ((0, o1) :: (0, o1) :: repBlk k u), [r0; r0])
                     (br1, (0, o1) :: (1, o1) :: rep1 n ((0, o1) :: (0, o1) :: repBlk k u), [])).
  { destruct n as [| n']; msteps 2. }
  exact (mstar_plus (mstar_trans h1 h2) h3).
Qed.

Lemma br_wrap (n k : nat) {body out : list (nat * Ones)}
    (hmid : forall rs : list RSym,
      MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: body, r2 :: r2 :: rs)
            (br, (0, o1) :: (0, o1) :: (0, o1) :: out, rs)) :
  MPlus (br,  (0, o1) :: rep1 (S n) ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk k body), [])
        (br1, (0, o1) :: rep1 (S n) ((0, o1) :: (0, o1) :: repBlk k out), []).
Proof.
  exact (mplus_trans (br_in n k body) (mplus_trans (hmid _) (br_out n k out))).
Qed.

(* ------------------------------------------------------------------------- *)
(* F_core Helpers & 4-Case Reducer                                           *)
(* ------------------------------------------------------------------------- *)

Lemma br_out_2_step (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: u, r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: u, rs).
Proof. msteps 5. Qed.

Lemma br_out_2_sweep (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (br, (0, o1) :: (0, o1) :: (0, o1) :: u, repR2 a rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: repL2 a u, rs).
Proof.
  revert u. induction a as [| a IH]; intros u; [apply mstar_refl |].
  cbn [repR2].
  pose proof (br_out_2_step u (repR2 a rs)) as h1.
  pose proof (IH ((2, o1) :: u)) as h2.
  rewrite repL2_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma repR00_snoc (a : nat) (rs : list RSym) :
  repR00 a (r0 :: r0 :: rs) = repR00 (S a) rs.
Proof.
  induction a as [| a IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma dl_1_2_sweep (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (dl, (1, o1) :: repL2 a u, rs)
        (dl, (1, o1) :: u, repR00 a rs).
Proof.
  revert rs. induction a as [| a IH]; intros rs; [apply mstar_refl |].
  cbn [repL2].
  assert (h1 : MPlus (dl, (1, o1) :: (2, o1) :: repL2 a u, rs)
                     (dl, (1, o1) :: repL2 a u, r0 :: r0 :: rs)) by msteps 1.
  pose proof (IH (r0 :: r0 :: rs)) as h2.
  rewrite repR00_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma dl_00_sweep (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (dl, repL00 a u, rs) (dl, u, repR2 a rs).
Proof.
  revert rs. induction a as [| a IH]; intros rs; [apply mstar_refl |].
  cbn [repL00].
  assert (h1 : MPlus (dl, (0, o1) :: (0, o1) :: repL00 a u, rs)
                     (dl, repL00 a u, r2 :: rs)) by msteps 1.
  pose proof (IH (r2 :: rs)) as h2.
  rewrite repR2_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma br1_r0_sweep (k : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MStar (br1, u, repR0 k rs) (br1, repL0 k u, rs).
Proof.
  revert u. induction k as [| k IH]; intros u; [apply mstar_refl |].
  cbn [repR0].
  assert (h1 : MPlus (br1, u, r0 :: repR0 k rs) (br1, (0, o1) :: u, repR0 k rs)) by msteps 1.
  pose proof (IH ((0, o1) :: u)) as h2.
  rewrite repL0_snoc in h2.
  exact (mstar_trans (mstar_of_plus h1) h2).
Qed.

Lemma dl_0_2_to_1 (a : nat) (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (0, o1) :: repL2 (S a) u, rs)
        (dl, (1, o1) :: u, repR00 a (r1 :: rs)).
Proof.
  assert (h1 : MPlus (dl, (0, o1) :: (2, o1) :: repL2 a u, rs)
                     (dl, (1, o1) :: repL2 a u, r1 :: rs)) by msteps 1.
  exact (mplus_star h1 (dl_1_2_sweep a u (r1 :: rs))).
Qed.

Lemma f_core_allTrue (a : nat) (rs : list RSym) :
  MPlus (dl, (0, o1) :: repL2 a [], r1 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) [], rs).
Proof.
  destruct a as [| a']; [msteps 20 |].
  pose proof (dl_0_2_to_1 a' [] (r1 :: r2 :: rs)) as h1.
  assert (h2 : MPlus (dl, [(1, o1)], repR00 a' (r1 :: r1 :: r2 :: rs))
                     (br1, [], r0 :: r0 :: r0 :: repR00 a' (r1 :: r1 :: r2 :: rs))) by msteps 2.
  pose proof (br1_r0_sweep (3 + 2 * a') [] (r1 :: r1 :: r2 :: rs)) as h3.
  cbn [Nat.add repR0] in h3. rewrite repR0_double in h3.
  assert (h4 : MPlus (br1, repL0 (3 + 2 * a') [], r1 :: r1 :: r2 :: rs)
                     (dl, (0, o1) :: (0, o1) :: repL0 (3 + 2 * a') [], r0 :: r0 :: r1 :: rs)) by msteps 4.
  assert (h4eq : (0, o1) :: (0, o1) :: repL0 (3 + 2 * a') [] = repL00 (2 + a') [(0, o1)]).
  { rewrite <- repL0_double.
    change ((0, o1) :: (0, o1) :: repL0 (3 + 2 * a') []) with (repL0 (5 + 2 * a') []).
    replace (5 + 2 * a') with (2 * (2 + a') + 1) by lia.
    rewrite repL0_add. reflexivity. }
  pose proof (dl_00_sweep (2 + a') [(0, o1)] (r0 :: r0 :: r1 :: rs)) as h5.
  rewrite <- h4eq in h5.
  assert (h6 : MPlus (dl, [(0, o1)], repR2 (2 + a') (r0 :: r0 :: r1 :: rs))
                     (br, [(0, o1); (0, o1); (0, o1)], repR2 (2 + a') (r0 :: r0 :: r1 :: rs))) by msteps 4.
  pose proof (br_out_2_sweep (2 + a') [] (r0 :: r0 :: r1 :: rs)) as h7.
  assert (h8 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: repL2 (2 + a') [], r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repL2 (2 + a') [], rs)) by msteps 3.
  exact (mplus_trans h1 (mplus_trans (mplus_star h2 h3) (mplus_trans (mplus_star h4 h5) (mplus_trans (mplus_star h6 h7) h8)))).
Qed.

Lemma f_core_allFalse (a : nat) (rs : list RSym) :
  MPlus (dl, (0, o1) :: repL00 (S a) [], r1 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: repL00 (S a) [], rs).
Proof.
  pose proof (dl_00_sweep (S a) [(0, o1)] (r1 :: r2 :: rs)) as h1.
  assert (h1l : (0, o1) :: repL00 (S a) [] = repL00 (S a) [(0, o1)]).
  { rewrite <- !repL0_double. symmetry. apply repL0_snoc. }
  rewrite <- h1l in h1.
  assert (h2 : MPlus (dl, [(0, o1)], repR2 (S a) (r1 :: r2 :: rs))
                     (br, [(0, o1); (0, o1); (0, o1)], repR2 (S a) (r1 :: r2 :: rs))) by msteps 4.
  pose proof (br_out_2_sweep (S a) [] (r1 :: r2 :: rs)) as h3.
  assert (h4 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) [], r1 :: r2 :: rs)
                     (dl, (0, o1) :: repL2 (S a) [], r2 :: r0 :: r0 :: r1 :: rs)) by msteps 4.
  pose proof (dl_0_2_to_1 a [] (r2 :: r0 :: r0 :: r1 :: rs)) as h5.
  assert (h6 : MPlus (dl, [(1, o1)], repR00 a (r1 :: r2 :: r0 :: r0 :: r1 :: rs))
                     (br1, [], r0 :: r0 :: r0 :: repR00 a (r1 :: r2 :: r0 :: r0 :: r1 :: rs))) by msteps 2.
  pose proof (br1_r0_sweep (3 + 2 * a) [] (r1 :: r2 :: r0 :: r0 :: r1 :: rs)) as h7.
  cbn [Nat.add repR0] in h7. rewrite repR0_double in h7.
  assert (h8 : MPlus (br1, repL0 (3 + 2 * a) [], r1 :: r2 :: r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: repL0 (3 + 2 * a) [], r2 :: r0 :: r0 :: r1 :: rs)) by msteps 1.
  assert (h8l : (0, o1) :: (0, o1) :: repL0 (3 + 2 * a) [] =
                (0, o1) :: (0, o1) :: (0, o1) :: repL00 (S a) []).
  { rewrite <- repL0_double. replace (2 * S a) with (2 + 2 * a) by lia. reflexivity. }
  rewrite h8l in h8.
  assert (h9 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: repL00 (S a) [], r2 :: r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: repL00 (S a) [], rs)) by msteps 8.
  exact (mstar_plus h1 (mplus_trans (mplus_star h2 h3) (mplus_trans h4 (mplus_trans h5 (mplus_trans (mplus_star h6 h7) (mplus_trans h8 h9)))))).
Qed.

Lemma f_core_trueThenFalse (a : nat) (t : list bool) (rs : list RSym) :
  MPlus (dl, (0, o1) :: repL2 (S a) ((0, o1) :: (0, o1) :: encB t), r1 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) (encB (incB t)), rs).
Proof.
  pose proof (dl_0_2_to_1 a ((0, o1) :: (0, o1) :: encB t) (r1 :: r2 :: rs)) as h1.
  assert (h2 : MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: encB t, repR00 a (r1 :: r1 :: r2 :: rs))
                     (br, (1, o1) :: encB t, r0 :: r0 :: repR00 a (r1 :: r1 :: r2 :: rs))) by msteps 1.
  assert (h3 : MPlus (br, (1, o1) :: encB t, r0 :: r0 :: repR00 a (r1 :: r1 :: r2 :: rs))
                     (br1, (2, o1) :: encB t, r0 :: repR00 a (r1 :: r1 :: r2 :: rs))) by msteps 1.
  pose proof (br1_r0_sweep (1 + 2 * a) ((2, o1) :: encB t) (r1 :: r1 :: r2 :: rs)) as h4.
  cbn [Nat.add repR0] in h4. rewrite repR0_double in h4.
  assert (h5 : MPlus (br1, repL0 (1 + 2 * a) ((2, o1) :: encB t), r1 :: r1 :: r2 :: rs)
                     (dl, (0, o1) :: (0, o1) :: repL0 (1 + 2 * a) ((2, o1) :: encB t), r0 :: r0 :: r1 :: rs)) by msteps 4.
  assert (h5l : (0, o1) :: (0, o1) :: repL0 (1 + 2 * a) ((2, o1) :: encB t) =
                repL00 (S a) ((0, o1) :: (2, o1) :: encB t)).
  { rewrite <- repL0_double. replace (2 * S a) with (2 + 2 * a) by lia.
    cbn [Nat.add repL0]. rewrite repL0_snoc. reflexivity. }
  rewrite h5l in h5.
  pose proof (dl_00_sweep (S a) ((0, o1) :: (2, o1) :: encB t) (r0 :: r0 :: r1 :: rs)) as h6.
  assert (h7 : MPlus (dl, (0, o1) :: (2, o1) :: encB t, repR2 (S a) (r0 :: r0 :: r1 :: rs))
                     (dl, (1, o1) :: encB t, r1 :: repR2 (S a) (r0 :: r0 :: r1 :: rs))) by msteps 1.
  pose proof (call1_encB t (r1 :: repR2 (S a) (r0 :: r0 :: r1 :: rs))) as h8.
  assert (h9 : MPlus (br1, (0, o1) :: encB (incB t), r1 :: repR2 (S a) (r0 :: r0 :: r1 :: rs))
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: encB (incB t), repR2 (S a) (r0 :: r0 :: r1 :: rs))) by msteps 1.
  pose proof (br_out_2_sweep (S a) (encB (incB t)) (r0 :: r0 :: r1 :: rs)) as h10.
  assert (h11 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) (encB (incB t)), r0 :: r0 :: r1 :: rs)
                      (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) (encB (incB t)), rs)) by msteps 3.
  exact (mplus_trans h1 (mplus_trans h2 (mplus_trans (mplus_star h3 h4) (mplus_trans (mplus_star h5 h6) (mplus_trans h7 (mplus_trans h8 (mplus_trans (mplus_star h9 h10) h11))))))).
Qed.

Lemma f_core_falseThenTrue (a : nat) (t : list bool) (rs : list RSym) :
  MPlus (dl, (0, o1) :: repL00 (S a) ((2, o1) :: encB t), r1 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: repL00 a (encB (incB (incB t))), rs).
Proof.
  pose proof (dl_00_sweep (S a) ((0, o1) :: (2, o1) :: encB t) (r1 :: r2 :: rs)) as h1.
  assert (h1l : (0, o1) :: repL00 (S a) ((2, o1) :: encB t) =
                repL00 (S a) ((0, o1) :: (2, o1) :: encB t)).
  { rewrite <- !repL0_double. symmetry. apply repL0_snoc. }
  rewrite <- h1l in h1.
  assert (h2 : MPlus (dl, (0, o1) :: (2, o1) :: encB t, repR2 (S a) (r1 :: r2 :: rs))
                     (dl, (1, o1) :: encB t, r1 :: repR2 (S a) (r1 :: r2 :: rs))) by msteps 1.
  pose proof (call1_encB t (r1 :: repR2 (S a) (r1 :: r2 :: rs))) as h3.
  assert (h4 : MPlus (br1, (0, o1) :: encB (incB t), r1 :: repR2 (S a) (r1 :: r2 :: rs))
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: encB (incB t), repR2 (S a) (r1 :: r2 :: rs))) by msteps 1.
  pose proof (br_out_2_sweep (S a) (encB (incB t)) (r1 :: r2 :: rs)) as h5.
  assert (h6 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: repL2 (S a) (encB (incB t)), r1 :: r2 :: rs)
                     (dl, (1, o1) :: repL2 a (encB (incB t)), r1 :: r2 :: r0 :: r0 :: r1 :: rs)) by msteps 5.
  pose proof (dl_1_2_sweep a (encB (incB t)) (r1 :: r2 :: r0 :: r0 :: r1 :: rs)) as h7.
  pose proof (call1_encB (incB t) (repR00 a (r1 :: r2 :: r0 :: r0 :: r1 :: rs))) as h8.
  pose proof (br1_r0_sweep (2 * a) ((0, o1) :: encB (incB (incB t))) (r1 :: r2 :: r0 :: r0 :: r1 :: rs)) as h9.
  rewrite repR0_double, repL0_snoc, repL0_double in h9.
  assert (h10 : MPlus (br1, (0, o1) :: repL00 a (encB (incB (incB t))), r1 :: r2 :: r0 :: r0 :: r1 :: rs)
                      (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: repL00 a (encB (incB (incB t))), rs)) by msteps 9.
  exact (mstar_plus h1 (mplus_trans h2 (mplus_trans h3 (mplus_trans (mplus_star h4 h5) (mplus_trans (mplus_star h6 h7) (mplus_trans (mplus_star h8 h9) h10)))))).
Qed.

Lemma f_core_ex (s : list bool) :
  exists t : list bool,
    valB (true :: t) <= 2 + 2 * valB s /\
    forall rs : list RSym,
      MPlus (dl, (0, o1) :: encB s, r1 :: r2 :: rs)
            (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: encB (true :: t), rs).
Proof.
  destruct (decomp_complete s) as [d hd]; subst s.
  destruct d as [a | a | a t0 | a t0].
  - exists (repeat true a). split.
    + cbn [evalDecomp valB]. lia.
    + intros rs.
      pose proof (f_core_allTrue a rs) as h.
      assert (he : encB (repeat true a) = repL2 a []).
      { rewrite <- (app_nil_r (repeat true a)), encB_rep_true. reflexivity. }
      cbn [evalDecomp encB repL2] in *. rewrite he. exact h.
  - exists (repeat false (S a)). split.
    + cbn [evalDecomp valB]. lia.
    + intros rs.
      pose proof (f_core_allFalse a rs) as h.
      assert (he : encB (repeat false (S a)) = repL00 (S a) []).
      { rewrite <- (app_nil_r (repeat false (S a))), encB_rep_false. reflexivity. }
      cbn [evalDecomp encB]. rewrite he in *. exact h.
  - exists (repeat true a ++ incB t0). split.
    + pose proof (valB_rep_true (S a) (incB t0)) as h1.
      pose proof (valB_rep_true (S a) (false :: t0)) as h2.
      rewrite valB_incB in h1.
      cbn [evalDecomp repeat app valB] in *.
      nia.
    + intros rs.
      pose proof (f_core_trueThenFalse a t0 rs) as h.
      cbn [evalDecomp].
      change (true :: (repeat true a ++ incB t0)) with (repeat true (S a) ++ incB t0).
      rewrite !encB_rep_true. cbn [encB]. exact h.
  - exists (repeat false a ++ incB (incB t0)). split.
    + pose proof (valB_rep_false a (incB (incB t0))) as h1.
      pose proof (valB_rep_false (S a) (true :: t0)) as h2.
      rewrite !valB_incB in h1.
      rewrite pow2_S_eq in h2.
      cbn [evalDecomp valB] in *.
      nia.
    + intros rs.
      pose proof (f_core_falseThenTrue a t0 rs) as h.
      cbn [evalDecomp encB].
      rewrite !encB_rep_false. cbn [encB]. exact h.
Qed.

(* ------------------------------------------------------------------------- *)
(* Exact BR Body Exit Lemmas                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma body_2_100100 (u0 : list bool) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u0, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB (addB 4 u0), rs).
Proof.
  set (u1 := incB u0).
  set (u2 := incB u1).
  set (u3 := incB u2).
  set (u4 := incB u3).
  pose proof (call0_2 (call1_encB u0)) as hc1; fold u1 in hc1.
  pose proof (call0_2 (call1_encB u1)) as hc2; fold u2 in hc2.
  pose proof (call0_2 (call1_encB u2)) as hc3; fold u3 in hc3.
  pose proof (call0_2 (call1_encB u3)) as hc4; fold u4 in hc4.
  assert (s1 : MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u0, r2 :: r2 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u0, r1 :: r2 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)) by msteps 22.
  pose proof (hc1 (r1 :: r2 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)) as s2.
  assert (s3 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u1, r1 :: r2 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u1, r0 :: r0 :: r1 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)) by msteps 3.
  pose proof (hc2 (r0 :: r0 :: r1 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)) as s4.
  assert (s5 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u2, r0 :: r0 :: r1 :: r1 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u2, r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)) by msteps 10.
  pose proof (hc3 (r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)) as s6.
  assert (s7 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u3, r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)
                     (dl, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u3, r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)) by msteps 3.
  pose proof (hc4 (r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)) as s8.
  assert (s9 : MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u4, r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: r1 :: r0 :: r0 :: r1 :: rs)
                     (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: encB u4, rs)) by msteps 11.
  exact (mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 (mplus_trans s5 (mplus_trans s6 (mplus_trans s7 (mplus_trans s8 s9)))))))).
Qed.

Lemma body_m2_000 (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: u, rs).
Proof. msteps 43. Qed.

Lemma body_m2_0 (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: u, rs).
Proof. msteps 43. Qed.

Lemma body_m11_000_false (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (2, o1) :: (0, o1) :: u, rs).
Proof. msteps 56. Qed.

Lemma body_m11_000_true (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (4, o1) :: u, rs).
Proof. msteps 56. Qed.

Lemma body_m11_0 (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (2, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (0, o1) :: u, rs).
Proof. msteps 55. Qed.

Lemma body_100_000 (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: (0, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: u, rs).
Proof. msteps 46. Qed.

Lemma body_100_0 (u : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: u, r2 :: r2 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (2, o1) :: u, rs).
Proof. msteps 46. Qed.

Lemma body_100_22_in (s : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (2, o1) :: s, r2 :: r2 :: rs)
        (dl, (0, o1) :: s, r1 :: r2 :: r0 :: r0 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs).
Proof. msteps 32. Qed.

Lemma body_100_22_out (s : list (nat * Ones)) (rs : list RSym) :
  MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: s, r0 :: r0 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: s, rs).
Proof. msteps 12. Qed.

Lemma body_plain_in (s : list (nat * Ones)) (rs : list RSym) :
  MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: (2, o1) :: s, r2 :: r2 :: rs)
        (dl, (0, o1) :: s, r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs).
Proof. msteps 19. Qed.

Lemma body_plain_out (s : list (nat * Ones)) (rs : list RSym) :
  MPlus (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: s, r1 :: r0 :: r0 :: r1 :: rs)
        (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: s, rs).
Proof. msteps 4. Qed.

(* ========================================================================= *)
(* Section 5: The 16-Constructor Closed Invariant Inv284                     *)
(* ========================================================================= *)

Definition mkBR1 (ones blocks : nat) (body : list (nat * Ones)) : State :=
  (br1, (0, o1) :: rep1 ones ((0, o1) :: (0, o1) :: repBlk blocks body), []).

Definition mkBR (ones blocks : nat) (body : list (nat * Ones)) : State :=
  (br, (0, o1) :: rep1 ones ((0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: repBlk blocks body), []).

Lemma br_wrap_add1 (n k : nat) {body out : list (nat * Ones)}
    (hmid : forall rs : list RSym,
      MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: body, r2 :: r2 :: rs)
            (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: out, rs)) :
  MPlus (mkBR (S n) k body) (mkBR1 (S n) (S k) out).
Proof.
  unfold mkBR, mkBR1.
  rewrite <- (repBlk_snoc k out).
  exact (br_wrap n k hmid).
Qed.

Lemma br_wrap_add2 (n k : nat) {body out : list (nat * Ones)}
    (hmid : forall rs : list RSym,
      MPlus (dl, (1, o1) :: (0, o1) :: (0, o1) :: body, r2 :: r2 :: rs)
            (br, (0, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) ::
                 (1, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: out, rs)) :
  MPlus (mkBR (S n) k body) (mkBR1 (S n) (S (S k)) out).
Proof.
  unfold mkBR, mkBR1.
  rewrite <- (repBlk_snoc (S k) out), <- (repBlk_snoc k _).
  exact (br_wrap n k hmid).
Qed.

Inductive Inv284 : State -> Prop :=
  | br1_100 (m k : nat) (u : list bool)
      (hb : valB (true :: u) <= 4 * (4 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (5 + m) (S k) ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u)))
  | br_100 (m k : nat) (u : list bool)
      (hlo : 16 <= valB (true :: u))
      (hhi : valB (true :: u) <= 16 * (3 + m) * 2 ^ k) :
      Inv284 (mkBR (5 + m) k ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u)))
  | br1_2_100100 (m k : nat) (u : list bool)
      (hb : valB (true :: u) <= 4 * (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u)))
  | br_2_100100 (m k : nat) (u : list bool)
      (hb : valB (true :: u) + 8 * 2 ^ k <= 16 * (5 + m) * 2 ^ k) :
      Inv284 (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u)))
  | br1_m2_0 (m k : nat) (u : list bool)
      (hb : valB (true :: u) + 1 <= 2 * (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u)))
  | br_m2_0 (m k : nat) (u : list bool)
      (hb : valB (true :: u) + 1 <= 4 * (3 + m) * 2 ^ k) :
      Inv284 (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u)))
  | br1_m11_0 (m k : nat) (u : list bool)
      (hb : valB (true :: u) + 1 <= 2 * (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (6 + m) (S k) ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u)))
  | br_m11_0 (m k : nat) (u : list bool)
      (hb : valB (true :: u) + 1 <= 4 * (3 + m) * 2 ^ k) :
      Inv284 (mkBR (7 + m) k ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u)))
  | br1_2_0 (m k : nat) (u : list bool)
      (hb : 2 * valB u + 3 <= (3 + m) * 2 ^ (S (S k))) :
      Inv284 (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (0, o1) :: encB u))
  | br1_m2_000 (m k : nat) (u : list bool)
      (hlo : 1 <= valB u)
      (hb : valB u + 1 <= (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u))
  | br_m2_000 (m k : nat) (u : list bool)
      (hlo : 1 <= valB u)
      (hb : valB u + 1 <= 2 * (3 + m) * 2 ^ k) :
      Inv284 (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u))
  | br1_m11_000 (m k : nat) (u : list bool)
      (hlo : 1 <= valB u)
      (hb : valB u + 1 <= (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (6 + m) (S k) ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u))
  | br_m11_000 (m k : nat) (u : list bool)
      (hlo : 1 <= valB u)
      (hb : valB u + 1 <= 2 * (3 + m) * 2 ^ k) :
      Inv284 (mkBR (7 + m) k ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u))
  | br1_2_2_0 (m k : nat) (u : list bool)
      (hb : 2 * valB u + 2 <= (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (2, o1) :: (0, o1) :: encB u))
  | br1_2_4 (m k : nat) (u : list bool)
      (hb : 2 * valB u + 3 <= (3 + m) * 2 ^ (S k)) :
      Inv284 (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (4, o1) :: encB u))
  | br_plain (m k : nat) (u : list bool)
      (hb : valB (true :: u) <= 4 * (6 + m) * 2 ^ (S k) + 2) :
      Inv284 (mkBR (8 + m) (S k) (encB (true :: u))).

Lemma inv284_cp682 : Inv284 cp682.
Proof.
  change cp682 with (mkBR (5 + 0) 0 ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: [true; false; true; false]))).
  apply (br_100 0 0 [true; false; true; false]); cbn; lia.
Qed.

Lemma inv284_step {s : State} (hs : Inv284 s) : exists s', MPlus s s' /\ Inv284 s'.
Proof.
  destruct hs as
    [ m k u hb
    | m k u hlo hhi
    | m k u hb
    | m k u hb
    | m k u hb
    | m k u hb
    | m k u hb
    | m k u hb
    | m k u hb
    | m k u hlo hb
    | m k u hlo hb
    | m k u hlo hb
    | m k u hlo hb
    | m k u hb
    | m k u hb
    | m k u hb ].
  - (* br1_100 *)
    set (C := (4 + m) * 2 ^ (S k)).
    set (u' := addB (2 * C) u).
    exists (mkBR (5 + S m) k ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u'))).
    split.
    + exact (br1_run (3 + m) k (call0N_100 (call0N_2 (call1N_encB (2 * C) u)))).
    + apply (br_100 (S m) k u').
      * subst u' C. cbn [valB]. rewrite valB_addB, pow2_S_eq.
        pose proof (pow2_ge_1 k). nia.
      * subst u' C. cbn [valB] in hb |- *. rewrite valB_addB.
        rewrite pow2_S_eq in hb |- *. nia.
  - (* br_100 *)
    destruct u as [| b1 u1]; [cbn [valB] in hlo; lia |].
    destruct b1.
    + destruct (f_core_ex u1) as [t [ht_le ht_run]].
      exists (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: encB (true :: t))).
      split.
      * refine (br_wrap_add1 (4 + m) k (fun rs =>
          mplus_trans (body_100_22_in (encB u1) rs)
            (mplus_trans (ht_run (r0 :: r0 :: r1 :: r2 :: r1 :: r0 :: r0 :: r1 :: rs))
              (body_100_22_out (encB (true :: t)) rs)))).
      * apply (br1_2_100100 m k t).
        rewrite pow2_S_eq. cbn [valB] in hhi. nia.
    + destruct u1 as [| b2 u2]; [cbn [valB] in hlo; lia |].
      destruct b2.
      * exists (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u2))).
        split.
        -- exact (br_wrap_add1 (4 + m) k (body_100_0 (encB u2))).
        -- apply (br1_m2_0 m k u2).
           rewrite pow2_S_eq. cbn [valB] in hhi |- *. nia.
      * exists (mkBR1 (5 + m) (S k) ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u2)).
        split.
        -- exact (br_wrap_add1 (4 + m) k (body_100_000 (encB u2))).
        -- apply (br1_m2_000 m k u2).
           ++ cbn [valB] in hlo. lia.
           ++ rewrite pow2_S_eq. cbn [valB] in hhi. nia.
  - (* br1_2_100100 *)
    set (C := (4 + m) * 2 ^ (S k)).
    set (u' := addB (2 * C) u).
    exists (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: (1, o1) :: (0, o1) :: (0, o1) :: encB (true :: u'))).
    split.
    + exact (br1_run (3 + m) k (call0N_2 (call1N_100 (call0N_100 (call0N_2 (call1N_encB (2 * C) u)))))).
    + apply (br_2_100100 m k u').
      subst u' C. cbn [valB] in hb |- *. rewrite valB_addB.
      rewrite pow2_S_eq in hb |- *. nia.
  - (* br_2_100100 *)
    exists (mkBR1 (5 + S m) (S (S k)) ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: addB 4 u))).
    split.
    + exact (br_wrap_add2 (5 + m) k (body_2_100100 u)).
    + apply (br1_100 (S m) (S k) (addB 4 u)).
      cbn [valB] in hb |- *. rewrite valB_addB, !pow2_S_eq.
      pose proof (pow2_ge_1 k). nia.
  - (* br1_m2_0 *)
    exists (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u))).
    split.
    + exact (br1_run (3 + m) k (call0N_2 (call1N_M1 _ ((0, o1) :: encB (true :: u))))).
    + apply (br_m2_0 m k u). rewrite pow2_S_eq in hb. nia.
  - (* br_m2_0 *)
    exists (mkBR1 (6 + m) (S k) ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u))).
    split.
    + exact (br_wrap_add1 (5 + m) k (body_m2_0 (encB (true :: u)))).
    + apply (br1_m11_0 m k u). rewrite pow2_S_eq. nia.
  - (* br1_m11_0 *)
    exists (mkBR (7 + m) k ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: encB (true :: u))).
    split.
    + exact (br1_run (4 + m) k (call0N_M11 _ ((0, o1) :: encB (true :: u)))).
    + apply (br_m11_0 m k u). rewrite pow2_S_eq in hb. nia.
  - (* br_m11_0 *)
    exists (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (0, o1) :: encB u)).
    split.
    + exact (br_wrap_add2 (6 + m) k (body_m11_0 (encB u))).
    + apply (br1_2_0 m k u). rewrite !pow2_S_eq. cbn [valB] in hb. nia.
  - (* br1_2_0 *)
    set (C := (6 + m) * 2 ^ (S (S k))).
    assert (hneed : 2 ^ (length u) + 2 * valW u <= C).
    { pose proof (need_le_valB u). pose proof (pow2_ge_1 (S (S k))). subst C. nia. }
    destruct (call0N_erase_2_0 u C hneed) as [v [hv_call hv_val]].
    exists (mkBR (8 + m) (S k) (encB (true :: v))).
    split.
    + exact (br1_run (5 + m) (S k) hv_call).
    + apply (br_plain m k v).
      subst C. rewrite (pow2_S_eq (S k)) in hv_val. nia.
  - (* br1_m2_000 *)
    exists (mkBR (6 + m) k ((2, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u)).
    split.
    + exact (br1_run (3 + m) k (call0N_2 (call1N_M1 _ ((0, o1) :: (0, o1) :: (0, o1) :: encB u)))).
    + apply (br_m2_000 m k u hlo). rewrite pow2_S_eq in hb. nia.
  - (* br_m2_000 *)
    exists (mkBR1 (6 + m) (S k) ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u)).
    split.
    + exact (br_wrap_add1 (5 + m) k (body_m2_000 (encB u))).
    + apply (br1_m11_000 m k u hlo). rewrite pow2_S_eq. nia.
  - (* br1_m11_000 *)
    exists (mkBR (7 + m) k ((1, o1) :: (1, o1) :: (0, o1) :: (0, o2) :: (0, o1) :: (0, o1) :: (0, o1) :: encB u)).
    split.
    + exact (br1_run (4 + m) k (call0N_M11 _ ((0, o1) :: (0, o1) :: (0, o1) :: encB u))).
    + apply (br_m11_000 m k u hlo). rewrite pow2_S_eq in hb. nia.
  - (* br_m11_000 *)
    destruct u as [| b r]; [cbn [valB] in hlo; lia |].
    destruct b.
    + exists (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (4, o1) :: encB r)).
      split.
      * exact (br_wrap_add2 (6 + m) k (body_m11_000_true (encB r))).
      * apply (br1_2_4 m k r). rewrite pow2_S_eq. cbn [valB] in hb. nia.
    + exists (mkBR1 (7 + m) (S (S k)) ((2, o1) :: (2, o1) :: (0, o1) :: encB r)).
      split.
      * exact (br_wrap_add2 (6 + m) k (body_m11_000_false (encB r))).
      * apply (br1_2_2_0 m k r). rewrite pow2_S_eq. cbn [valB] in hb. nia.
  - (* br1_2_2_0 *)
    set (q := (6 + m) * 2 ^ (S k)).
    assert (hneed : 2 ^ (length u) + 2 * valW u <= q).
    { pose proof (need_le_valB u). pose proof (pow2_ge_1 (S k)). subst q. nia. }
    destruct (call0N_erase_2_2_0 u q hneed) as [v [hv_call hv_val]].
    replace (2 * q) with ((S (5 + m)) * 2 ^ (S (S k))) in hv_call
      by (subst q; rewrite (pow2_S_eq (S k)); nia).
    exists (mkBR (8 + m) (S k) (encB (true :: true :: v))).
    split.
    + exact (br1_run (5 + m) (S k) hv_call).
    + apply (br_plain m k (true :: v)).
      subst q. nia.
  - (* br1_2_4 *)
    set (q := (6 + m) * 2 ^ (S k)).
    assert (hneed : 1 + (2 ^ (length u) + 2 * valW u) <= q).
    { pose proof (need_le_valB u). pose proof (pow2_ge_1 (S k)). subst q. nia. }
    destruct (call0N_erase_2_4 u q hneed) as [v [hv_call hv_val]].
    replace (2 * q) with ((S (5 + m)) * 2 ^ (S (S k))) in hv_call
      by (subst q; rewrite (pow2_S_eq (S k)); nia).
    exists (mkBR (8 + m) (S k) (encB (true :: true :: v))).
    split.
    + exact (br1_run (5 + m) (S k) hv_call).
    + apply (br_plain m k (true :: v)).
      subst q. nia.
  - (* br_plain *)
    destruct (f_core_ex u) as [t [ht_le ht_run]].
    exists (mkBR1 (5 + (3 + m)) (S (S k)) ((1, o1) :: (0, o1) :: (0, o1) :: encB (true :: t))).
    split.
    + refine (br_wrap_add1 (7 + m) (S k) (fun rs =>
        mplus_trans (body_plain_in (encB u) rs)
          (mplus_trans (ht_run (r1 :: r0 :: r0 :: r1 :: rs))
            (body_plain_out (encB (true :: t)) rs)))).
    + apply (br1_100 (3 + m) (S k) t).
      rewrite (pow2_S_eq (S k)). pose proof (pow2_ge_1 (S k)).
      cbn [valB] in hb. nia.
Qed.

End M284.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep.
    eapply progress_trans.
    + exact M284.init_to_br1.
    + exact (M284.mplus_sound M284.br1_to_cp682).
  - apply (progress_nonhalt_cond tm M284.State M284.cp682 M284.evalCfg M284.Inv284).
    + intros s hs.
      destruct (M284.inv284_step hs) as [s' [hstep hs']].
      exists s'. split; [exact (M284.mplus_sound hstep) | exact hs'].
    + exact M284.inv284_cp682.
Qed.
