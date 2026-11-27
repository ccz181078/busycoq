(* BB(6) holdout 608:#273 / 797:#362: 1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Strings.String Lists.List PeanoNat NArith PArith ZArith ZifyN Lia.

Local Open Scope string_scope.

Definition tm : TM := TM_from_str "1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC".

Module Internal.

Import ListNotations.
Local Unset Default Goal Selector.
Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

(* ========================================================================= *)
(* Section 1: TM Reachability, N Repetition & Window Simulator               *)
(* ========================================================================= *)

Lemma rs_refl (c : Q * tape) : c -[ tm ]->* c.
Proof. apply evstep_refl. Qed.

Lemma rs_trans {c1 c2 c3 : Q * tape} (h1 : c1 -[ tm ]->* c2) (h2 : c2 -[ tm ]->* c3) :
  c1 -[ tm ]->* c3.
Proof. eapply evstep_trans; [exact h1 | exact h2]. Qed.

Lemma evstep_to_halts {c ch : Q * tape} (hev : c -[ tm ]->* ch) (hh : halted tm ch) :
  halts tm c.
Proof.
  induction hev as [c | c c' c'' hstep _ IH].
  - exists 0%nat, c. split; [apply multistep_0 | exact hh].
  - destruct (IH hh) as [n [ch' [hm hch]]].
    exists (S n), ch'. split; [eapply multistep_S; [exact hstep | exact hm] | exact hch].
Qed.

Lemma zero_cons_def : S0 >> const S0 = const S0.
Proof. symmetry; apply const_unfold. Qed.

Definition opt_bind {T U : Type} (x : option T) (f : T -> option U) : option U :=
  match x with
  | Some a => f a
  | None => None
  end.

Definition repBlock {T : Type} (u : list T) (n : N) : list T :=
  N.iter n (fun acc => u ++ acc) [].

Lemma repBlock_0 {T : Type} (u : list T) : repBlock u 0 = [].
Proof. reflexivity. Qed.

Lemma repBlock_1 {T : Type} (u : list T) : repBlock u 1 = u.
Proof. unfold repBlock; cbn; apply app_nil_r. Qed.

Lemma repBlock_succ_left {T : Type} (u : list T) (k : N) :
  repBlock u (k + 1) = u ++ repBlock u k.
Proof.
  unfold repBlock.
  replace (k + 1) with (N.succ k) by lia.
  rewrite N.iter_succ. reflexivity.
Qed.

Lemma repBlock_add {T : Type} (u : list T) (m n : N) :
  repBlock u (m + n) = repBlock u m ++ repBlock u n.
Proof.
  pattern m; apply N.peano_ind; [reflexivity |].
  intros k IH.
  replace (N.succ k + n) with ((k + n) + 1) by lia.
  replace (N.succ k) with (k + 1) by lia.
  rewrite !repBlock_succ_left, IH, app_assoc. reflexivity.
Qed.

Lemma repBlock_succ_right {T : Type} (u : list T) (k : N) :
  repBlock u (k + 1) = repBlock u k ++ u.
Proof.
  rewrite repBlock_add, repBlock_1. reflexivity.
Qed.

Definition evalWin (l r : side) (q : Q) (dR : bool) (ls rs : list Sym) : Q * tape :=
  if dR then (ls *> l) {{q}}> (rs *> r) else (ls *> l) <{{q}} (rs *> r).

Definition stepWin (bL bR : bool) (st : Q * bool * list Sym * list Sym) :
  option (Q * bool * list Sym * list Sym) :=
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

Fixpoint multiStepWin (bL bR : bool) (n : nat) (st : Q * bool * list Sym * list Sym) :
  option (Q * bool * list Sym * list Sym) :=
  match n with
  | O => Some st
  | S n' => opt_bind (stepWin bL bR st) (multiStepWin bL bR n')
  end.

Fixpoint list_sym_eqb (xs ys : list Sym) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sym_eqb x y && list_sym_eqb xs' ys'
  | _, _ => false
  end.

Lemma list_sym_eqb_eq : forall xs ys, list_sym_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs IH]; intros [| y ys] H; try discriminate.
  - reflexivity.
  - cbn in H. apply andb_prop in H. destruct H as [Hx Hxs].
    destruct x, y; try discriminate; f_equal; exact (IH ys Hxs).
Qed.

Definition winState_eqb (x y : Q * bool * list Sym * list Sym) : bool :=
  let '(q1, d1, ls1, rs1) := x in
  let '(q2, d2, ls2, rs2) := y in
  q_eqb q1 q2 && Bool.eqb d1 d2 && list_sym_eqb ls1 ls2 && list_sym_eqb rs1 rs2.

Lemma winState_eqb_eq : forall x y, winState_eqb x y = true -> x = y.
Proof.
  intros [[[q1 d1] ls1] rs1] [[[q2 d2] ls2] rs2] H.
  unfold winState_eqb in H.
  apply andb_prop in H. destruct H as [H hrs].
  apply andb_prop in H. destruct H as [H hls].
  apply andb_prop in H. destruct H as [hq hd].
  destruct (q_eqb_spec q1 q2); [| discriminate].
  apply Bool.eqb_prop in hd.
  apply list_sym_eqb_eq in hls.
  apply list_sym_eqb_eq in hrs.
  congruence.
Qed.

Definition checkWin (bL bR : bool) (n : nat) (q : Q) (dR : bool) (ls rs : list Sym)
  (q' : Q) (dR' : bool) (ls' rs' : list Sym) : bool :=
  match multiStepWin bL bR n (q, dR, ls, rs) with
  | Some st' => winState_eqb st' (q', dR', ls', rs')
  | None => false
  end.

Lemma stepWin_exec (l r : side) (q q' : Q) (dR dR' : bool) (ls rs ls' rs' : list Sym)
  (x : Sym) (ls0 rs0 : list Sym)
  (hev : evalWin l r q dR ls rs = (q, (ls0 *> l, x, rs0 *> r)))
  (hm : (match tm (q, x) with
         | Some (w, R, q1) => Some (q1, true, w :: ls0, rs0)
         | Some (w, L, q1) => Some (q1, false, ls0, w :: rs0)
         | None => None
         end) = Some (q', dR', ls', rs')) :
  evalWin l r q dR ls rs -[ tm ]-> evalWin l r q' dR' ls' rs'.
Proof.
  rewrite hev.
  destruct (tm (q, x)) as [[[w dir] q1] |] eqn:htm; [| discriminate].
  destruct dir; inversion hm; subst; [exact (step_left htm) | exact (step_right htm)].
Qed.

Lemma stepWin_sound {bL bR : bool} {l r : side}
  (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0)
  {q q' : Q} {dR dR' : bool} {ls rs ls' rs' : list Sym}
  (hs : stepWin bL bR (q, dR, ls, rs) = Some (q', dR', ls', rs')) :
  evalWin l r q dR ls rs -[ tm ]-> evalWin l r q' dR' ls' rs'.
Proof.
  unfold stepWin in hs.
  destruct dR.
  - destruct rs as [| a rs0].
    + destruct bR eqn:hbR; [| discriminate].
      specialize (hR eq_refl); subst r.
      exact (stepWin_exec l (const S0) q q' true dR' ls [] ls' rs' S0 ls [] eq_refl hs).
    + exact (stepWin_exec l r q q' true dR' ls (a :: rs0) ls' rs' a ls rs0 eq_refl hs).
  - destruct ls as [| a ls0].
    + destruct bL eqn:hbL; [| discriminate].
      specialize (hL eq_refl); subst l.
      exact (stepWin_exec (const S0) r q q' false dR' [] rs ls' rs' S0 [] rs eq_refl hs).
    + exact (stepWin_exec l r q q' false dR' (a :: ls0) rs ls' rs' a ls0 rs eq_refl hs).
Qed.

Lemma checkWin_sound {bL bR : bool} {l r : side}
  (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0) :
  forall (n : nat) (q : Q) (dR : bool) (ls rs : list Sym)
    (q' : Q) (dR' : bool) (ls' rs' : list Sym),
    checkWin bL bR n q dR ls rs q' dR' ls' rs' = true ->
    evalWin l r q dR ls rs -[ tm ]->* evalWin l r q' dR' ls' rs'.
Proof.
  induction n as [| n IH]; intros q dR ls rs q' dR' ls' rs' h.
  - unfold checkWin, multiStepWin in h.
    apply winState_eqb_eq in h. inversion h; subst. apply rs_refl.
  - unfold checkWin in h. cbn [multiStepWin] in h.
    destruct (stepWin bL bR (q, dR, ls, rs)) as [[[[q1 dR1] ls1] rs1] |] eqn:hsw;
      [| discriminate].
    cbn [opt_bind] in h.
    eapply evstep_step; [exact (stepWin_sound hL hR hsw) |].
    exact (IH q1 dR1 ls1 rs1 q' dR' ls' rs' h).
Qed.

Lemma chkWin_eq {c1 c2 : Q * tape} (bL bR : bool) (n : nat)
  (q : Q) (dR : bool) (ls rs : list Sym)
  (q' : Q) (dR' : bool) (ls' rs' : list Sym)
  (l r : side)
  (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0)
  (h1 : c1 = evalWin l r q dR ls rs)
  (h2 : c2 = evalWin l r q' dR' ls' rs')
  (hc : checkWin bL bR n q dR ls rs q' dR' ls' rs' = true) :
  c1 -[ tm ]->* c2.
Proof.
  subst c1 c2. exact (checkWin_sound hL hR n q dR ls rs q' dR' ls' rs' hc).
Qed.

Lemma no_false {P : Prop} (h : false = true) : P.
Proof. discriminate h. Qed.

Lemma walkWordRight (s : nat) (q : Q) (dR : bool) (pL u pR v : list Sym)
  (hbody : checkWin false false s q dR pL (pR ++ v) q dR (pL ++ u) pR = true) :
  forall (k : N) (l r : side),
    evalWin l (repBlock v k *> r) q dR pL pR -[ tm ]->*
    evalWin (repBlock u k *> l) r q dR pL pR.
Proof.
  intro k; pattern k; apply N.peano_ind; [intros l r; apply rs_refl |].
  intros m IH l r.
  replace (N.succ m) with (m + 1) by lia.
  assert (hstart : evalWin l (repBlock v (m + 1) *> r) q dR pL pR =
                   evalWin l (repBlock v m *> r) q dR pL (pR ++ v)).
  { unfold evalWin. rewrite repBlock_succ_left, !Str_app_assoc. reflexivity. }
  assert (hmid : evalWin l (repBlock v m *> r) q dR (pL ++ u) pR =
                 evalWin (u *> l) (repBlock v m *> r) q dR pL pR).
  { unfold evalWin. rewrite Str_app_assoc. reflexivity. }
  assert (hend : evalWin (repBlock u m *> (u *> l)) r q dR pL pR =
                 evalWin (repBlock u (m + 1) *> l) r q dR pL pR).
  { rewrite <- Str_app_assoc, <- repBlock_succ_right. reflexivity. }
  rewrite hstart, <- hend.
  pose proof (@checkWin_sound false false l (repBlock v m *> r) (@no_false _) (@no_false _) s q dR pL (pR ++ v) q dR (pL ++ u) pR hbody) as h1.
  rewrite hmid in h1.
  exact (rs_trans h1 (IH (u *> l) r)).
Qed.

Lemma walkWordLeft (s : nat) (q : Q) (dR : bool) (pL u pR v : list Sym)
  (hbody : checkWin false false s q dR (pL ++ u) pR q dR pL (pR ++ v) = true) :
  forall (k : N) (l r : side),
    evalWin (repBlock u k *> l) r q dR pL pR -[ tm ]->*
    evalWin l (repBlock v k *> r) q dR pL pR.
Proof.
  intro k; pattern k; apply N.peano_ind; [intros l r; apply rs_refl |].
  intros m IH l r.
  replace (N.succ m) with (m + 1) by lia.
  assert (hstart : evalWin (repBlock u (m + 1) *> l) r q dR pL pR =
                   evalWin (repBlock u m *> l) r q dR (pL ++ u) pR).
  { unfold evalWin. rewrite repBlock_succ_left, !Str_app_assoc. reflexivity. }
  assert (hmid : evalWin (repBlock u m *> l) r q dR pL (pR ++ v) =
                 evalWin (repBlock u m *> l) (v *> r) q dR pL pR).
  { unfold evalWin. rewrite Str_app_assoc. reflexivity. }
  assert (hend : evalWin l (repBlock v m *> (v *> r)) q dR pL pR =
                 evalWin l (repBlock v (m + 1) *> r) q dR pL pR).
  { rewrite <- Str_app_assoc, <- repBlock_succ_right. reflexivity. }
  rewrite hstart, <- hend.
  pose proof (@checkWin_sound false false (repBlock u m *> l) r (@no_false _) (@no_false _) s q dR (pL ++ u) pR q dR pL (pR ++ v) hbody) as h1.
  rewrite hmid in h1.
  exact (rs_trans h1 (IH l (v *> r))).
Qed.

(* ========================================================================= *)
(* Section 2: Compressed Motif Stack Tokens & Canonical State                *)
(* ========================================================================= *)

Inductive Mode := MB0 | MDL.

Inductive LTok :=
| L0 (k : N)
| LD (v : N)
| LD1 (k : N)
| ML8 (k : N)
| M2L (k : N)
| M3L (k : N)
| M4L (k : N).

Inductive RTok :=
| R0 (d : N)
| R1 (d : N)
| R02 (k : N)
| MR11 (k : N)
| M2R (k : N).

Inductive LHead :=
| LHL0 (k : N)
| LHLD (v : N).

Inductive RHead :=
| RHR0 (d : N)
| RHR1 (d : N).

Inductive BaseState :=
| Init0
| Core (m : Mode) (l : list LTok) (r : list RTok)
| Halt (r : list RTok).

Definition wL0 : list Sym := [S1; S0].
Definition wLD1 : list Sym := [S1; S1; S1; S0].
Definition ld3Bits : list Sym := [S1; S1; S1; S1; S1; S0].
Definition ld5Bits : list Sym := [S1; S1; S1; S1; S1; S1; S1; S0].
Definition ld7Bits : list Sym := [S1; S1; S1; S1; S1; S1; S1; S1; S1; S0].
Definition ones4 : list Sym := [S1; S1; S1; S1].
Definition mid42 : list Sym :=
  [S1; S1; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S1; S1; S1; S1; S0;
   S1; S0; S1; S0; S1; S1; S1; S1; S1; S1; S1; S0; S1; S1; S1; S1; S1; S1; S1; S0].
Definition uM : list Sym := mid42 ++ ld7Bits.
Definition wM : list Sym := ld3Bits ++ (mid42 ++ ones4).
Definition vMTail : list Sym :=
  [S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0;
   S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0].
Definition vM : list Sym := S1 :: vMTail.

Definition mid66_2 : list Sym :=
  ld7Bits ++ ld3Bits ++
  [S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0] ++
  [S1; S1; S1; S0] ++
  [S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0].
Definition uM2 : list Sym := mid66_2 ++ ld5Bits.
Definition wM2Prefix34 : list Sym :=
  [S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0] ++ ld5Bits.
Definition wM2Mid40 : list Sym :=
  ld7Bits ++ ld3Bits ++
  [S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0].
Definition wM2 : list Sym := wM2Prefix34 ++ (wM2Mid40 ++ [S1; S1]).

Definition vM2Tail : list Sym :=
  [S1; S1; S0;
   S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0;
   S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0;
   S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0].
Definition vM2 : list Sym := S1 :: vM2Tail.

Definition wM3 : list Sym :=
  [S1; S1; S1; S1; S1; S1; S1; S0;
   S1; S1; S1; S0;
   S1; S0; S1; S0; S1; S0;
   S1; S1; S1; S0;
   S1; S0;
   S1; S1; S1; S1; S1; S1; S1; S0;
   S1; S1; S1; S1; S1; S0;
   S1; S0; S1; S0; S1; S0; S1; S0;
   S1; S1; S1; S0;
   S1; S0;
   S1; S1; S1; S0;
   S1; S1; S1; S1; S1; S1; S1; S1; S1; S0;
   S1; S1; S1; S1; S1; S1; S1; S1; S1; S0].

Definition wM4 : list Sym :=
  [S1; S0; S1; S0; S1; S0; S1; S0;
   S1; S1; S1; S1; S1; S0;
   S1; S0;
   S1; S1; S1; S1; S1; S0;
   S1; S0;
   S1; S1; S1; S0].

Fixpoint eL (xs : list LTok) : side :=
  match xs with
  | [] => const S0
  | L0 k :: tl => repBlock wL0 (k + 1) *> eL tl
  | LD v :: tl => repBlock [S1] (v + 2) *> ([S0] *> eL tl)
  | LD1 k :: tl => repBlock wLD1 (k + 1) *> eL tl
  | ML8 k :: tl => repBlock uM (k + 1) *> eL tl
  | M2L k :: tl => repBlock uM2 (k + 1) *> eL tl
  | M3L k :: tl => repBlock wM3 (k + 1) *> eL tl
  | M4L k :: tl => repBlock wM4 (k + 1) *> eL tl
  end.

Fixpoint eR (xs : list RTok) : side :=
  match xs with
  | [] => const S0
  | R0 d :: tl => repBlock [S1] (d + 1) *> ([S0] *> eR tl)
  | R1 d :: tl => repBlock [S1] (d + 1) *> ([S0; S0] *> eR tl)
  | R02 k :: tl => repBlock wLD1 (k + 1) *> eR tl
  | MR11 k :: tl => repBlock vM (k + 1) *> eR tl
  | M2R k :: tl => repBlock vM2 (k + 1) *> eR tl
  end.

Definition encodeCore (m : Mode) (l : list LTok) (r : list RTok) : Q * tape :=
  match m with
  | MB0 => evalWin (eL l) (eR r) B true [] [S0]
  | MDL => evalWin (eL l) (eR r) D false [] []
  end.

Definition encodeBase (bs : BaseState) : Q * tape :=
  match bs with
  | Init0 => c0
  | Core m l r => encodeCore m l r
  | Halt r => (E, (const S0, S0, S1 >> eR r))
  end.

(* ========================================================================= *)
(* Section 3: Stack Operations & Shallow Recognizers                         *)
(* ========================================================================= *)

Definition popL0Eq (v : N) (l : list LTok) : option (list LTok) :=
  match l with
  | L0 k :: rest => if k =? v then Some rest else None
  | _ => None
  end.

Definition popLDEq (v : N) (l : list LTok) : option (list LTok) :=
  match l with
  | LD k :: rest => if k =? v then Some rest else None
  | _ => None
  end.

Definition popLD1Eq (v : N) (l : list LTok) : option (list LTok) :=
  match l with
  | LD1 k :: rest => if k =? v then Some rest else None
  | _ => None
  end.

Definition popLD1 (l : list LTok) : option (N * list LTok) :=
  match l with
  | LD1 k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popLD1Ge4 (l : list LTok) : option (N * list LTok) :=
  match l with
  | LD1 m :: rest => if 4 <=? m then Some (m - 4, rest) else None
  | _ => None
  end.

Definition popML8 (l : list LTok) : option (N * list LTok) :=
  match l with
  | ML8 k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popM2L (l : list LTok) : option (N * list LTok) :=
  match l with
  | M2L k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popM3L (l : list LTok) : option (N * list LTok) :=
  match l with
  | M3L k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popM4L (l : list LTok) : option (N * list LTok) :=
  match l with
  | M4L k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popR0Eq (v : N) (r : list RTok) : option (list RTok) :=
  match r with
  | R0 d :: rest => if d =? v then Some rest else None
  | _ => None
  end.

Definition popR1Eq (v : N) (r : list RTok) : option (list RTok) :=
  match r with
  | R1 d :: rest => if d =? v then Some rest else None
  | _ => None
  end.

Definition popR02Eq (v : N) (r : list RTok) : option (list RTok) :=
  match r with
  | R02 k :: rest => if k =? v then Some rest else None
  | _ => None
  end.

Definition popR02 (r : list RTok) : option (N * list RTok) :=
  match r with
  | R02 k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popMR11 (r : list RTok) : option (N * list RTok) :=
  match r with
  | MR11 k :: rest => Some (k, rest)
  | _ => None
  end.

Definition popM2R (r : list RTok) : option (N * list RTok) :=
  match r with
  | M2R k :: rest => Some (k, rest)
  | _ => None
  end.

Definition matchU1 (l : list LTok) : option (list LTok) :=
  opt_bind (popLDEq 3 l) (fun l1 =>
  opt_bind (popLD1Eq 1 l1) (fun l2 =>
  opt_bind (popLDEq 5 l2) (fun l3 =>
  opt_bind (popL0Eq 1 l3) (fun l4 =>
  opt_bind (popLDEq 5 l4) (fun l5 =>
  opt_bind (popLDEq 5 l5) (fun l6 =>
  popLDEq 7 l6)))))).

Definition matchU2 (l : list LTok) : option (list LTok) :=
  opt_bind (popLDEq 7 l) (fun l1 =>
  opt_bind (popLDEq 3 l1) (fun l2 =>
  opt_bind (popLD1Eq 12 l2) (fun l3 =>
  popLDEq 5 l3))).

Definition matchW3 (l : list LTok) : option (list LTok) :=
  opt_bind (popLDEq 2 l) (fun l1 =>
  opt_bind (popL0Eq 1 l1) (fun l2 =>
  opt_bind (popLDEq 5 l2) (fun l3 =>
  opt_bind (popLD1Eq 0 l3) (fun l4 =>
  opt_bind (popL0Eq 2 l4) (fun l5 =>
  opt_bind (popLD1Eq 0 l5) (fun l6 =>
  opt_bind (popL0Eq 0 l6) (fun l7 =>
  opt_bind (popLDEq 5 l7) (fun l8 =>
  opt_bind (popLDEq 3 l8) (fun l9 =>
  opt_bind (popL0Eq 3 l9) (fun l10 =>
  opt_bind (popLD1Eq 0 l10) (fun l11 =>
  opt_bind (popL0Eq 0 l11) (fun l12 =>
  opt_bind (popLD1Eq 0 l12) (fun l13 =>
  opt_bind (popLDEq 7 l13) (fun l14 =>
  popLDEq 7 l14)))))))))))))).

Definition matchCapTail (r : list RTok) : bool :=
  match popR02Eq 0 r with
  | None => false
  | Some r1 =>
    match popR1Eq 3 r1 with
    | None => false
    | Some r2 =>
      match popR02Eq 0 r2 with
      | Some [] => true
      | _ => false
      end
    end
  end.

Definition peelLD1 (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else LD1 (k - 1) :: xs.

Definition peelML8 (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else ML8 (k - 1) :: xs.

Definition peelM2L (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else M2L (k - 1) :: xs.

Definition peelM3L (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else M3L (k - 1) :: xs.

Definition peelM4L (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else M4L (k - 1) :: xs.

Definition peelR02 (k : N) (xs : list RTok) : list RTok :=
  if k =? 0 then xs else R02 (k - 1) :: xs.

Definition peelMR11 (k : N) (xs : list RTok) : list RTok :=
  if k =? 0 then xs else MR11 (k - 1) :: xs.

Definition peelM2R (k : N) (xs : list RTok) : list RTok :=
  if k =? 0 then xs else M2R (k - 1) :: xs.

Definition pushM4L (k : N) (xs : list LTok) : list LTok :=
  match xs with
  | M4L m :: rest => M4L (k + 1 + m) :: rest
  | _ => M4L k :: xs
  end.

Definition foldWM4 (xs : list LTok) : list LTok :=
  match popL0Eq 3 xs with
  | None => xs
  | Some l1 =>
    match popLDEq 3 l1 with
    | None => xs
    | Some l2 =>
      match popL0Eq 0 l2 with
      | None => xs
      | Some l3 =>
        match popLDEq 3 l3 with
        | None => xs
        | Some l4 =>
          match popL0Eq 0 l4 with
          | None => xs
          | Some l5 =>
            match popLD1 l5 with
            | None => xs
            | Some (rem, rest) => pushM4L 0 (peelLD1 rem rest)
            end
          end
        end
      end
    end
  end.

Definition peelL0 (k : N) (xs : list LTok) : list LTok :=
  if k =? 0 then xs else foldWM4 (L0 (k - 1) :: xs).

Definition luTail (k : N) (rest : list LTok) : list LTok :=
  LD1 1 :: LD 5 :: L0 1 :: LD 5 :: LD 5 :: LD 7 :: peelML8 k rest.

Definition lu2Tail (k : N) (rest : list LTok) : list LTok :=
  LD 3 :: LD1 12 :: LD 5 :: peelM2L k rest.

Definition lw3Tail (k : N) (rest : list LTok) : list LTok :=
  LD1 0 :: L0 2 :: LD1 0 :: L0 0 :: LD 5 :: LD 3 :: L0 3 ::
    LD1 0 :: L0 0 :: LD1 0 :: LD 7 :: LD 7 :: peelM3L k rest.

Definition lw4Tail (k : N) (rest : list LTok) : list LTok :=
  LD 3 :: L0 0 :: LD 3 :: L0 0 :: LD1 0 :: peelM4L k rest.

Definition ruTail (k : N) (rest : list RTok) : list RTok :=
  R1 3 :: R02 1 :: R1 3 :: R1 3 :: R02 3 :: R1 3 :: peelMR11 k rest.

Definition ru2Tail (k : N) (rest : list RTok) : list RTok :=
  R02 6 :: R1 3 :: R02 0 :: R1 3 :: R02 6 :: peelM2R k rest.

Definition unconsL (l : list LTok) : option (LHead * list LTok) :=
  match l with
  | [] => None
  | L0 k :: rest => Some (LHL0 k, rest)
  | LD v :: rest => Some (LHLD v, rest)
  | LD1 k :: rest => Some (LHLD 1, peelLD1 k rest)
  | ML8 k :: rest => Some (LHLD 3, luTail k rest)
  | M2L k :: rest => Some (LHLD 7, lu2Tail k rest)
  | M3L k :: rest => Some (LHLD 5, lw3Tail k rest)
  | M4L k :: rest => Some (LHL0 3, lw4Tail k rest)
  end.

Definition unconsR (r : list RTok) : option (RHead * list RTok) :=
  match r with
  | [] => None
  | R0 d :: rest => Some (RHR0 d, rest)
  | R1 d :: rest => Some (RHR1 d, rest)
  | R02 k :: rest => Some (RHR0 2, peelR02 k rest)
  | MR11 k :: rest => Some (RHR0 2, ruTail k rest)
  | M2R k :: rest => Some (RHR0 2, ru2Tail k rest)
  end.

Definition pushLD1 (k : N) (xs : list LTok) : list LTok :=
  match xs with
  | LD1 m :: rest => LD1 (k + 1 + m) :: rest
  | _ => LD1 k :: xs
  end.

Definition pushLD (v : N) (xs : list LTok) : list LTok :=
  if v =? 1 then pushLD1 0 xs else LD v :: xs.

Definition pushML8 (k : N) (xs : list LTok) : list LTok :=
  match xs with
  | ML8 m :: rest => ML8 (k + 1 + m) :: rest
  | _ => ML8 k :: xs
  end.

Definition pushM2LRaw (k : N) (xs : list LTok) : list LTok :=
  match xs with
  | M2L m :: rest => M2L (k + 1 + m) :: rest
  | _ => M2L k :: xs
  end.

Definition pushM2L (k : N) (xs : list LTok) : list LTok :=
  match matchU2 xs with
  | Some rest => pushM2LRaw (k + 1) rest
  | None => pushM2LRaw k xs
  end.

Definition pushM3L (k : N) (xs : list LTok) : list LTok :=
  match xs with
  | M3L m :: rest => M3L (k + 1 + m) :: rest
  | _ => M3L k :: xs
  end.

Definition pushL0Raw (k : N) (xs : list LTok) : list LTok :=
  match unconsL xs with
  | Some (LHL0 m, rest) => L0 (k + 1 + m) :: rest
  | _ => L0 k :: xs
  end.

Definition pushL0 (k : N) (xs : list LTok) : list LTok :=
  foldWM4 (pushL0Raw k xs).

Definition pushZeros (q : N) (xs : list LTok) : list LTok :=
  if q =? 0 then xs else pushL0 (q - 1) xs.

Definition bumpL (xs : list LTok) : list LTok :=
  match unconsL xs with
  | None => [L0 0]
  | Some (LHL0 v, rest) => pushLD 0 (peelL0 v rest)
  | Some (LHLD v, rest) => pushLD (v + 1) rest
  end.

Definition pushR02 (k : N) (xs : list RTok) : list RTok :=
  match xs with
  | R02 m :: rest => R02 (k + 1 + m) :: rest
  | _ => R02 k :: xs
  end.

Definition pushR0 (d : N) (xs : list RTok) : list RTok :=
  if d =? 2 then pushR02 0 xs else R0 d :: xs.

Definition pushMR11 (k : N) (xs : list RTok) : list RTok :=
  match xs with
  | MR11 m :: rest => MR11 (k + 1 + m) :: rest
  | _ => MR11 k :: xs
  end.

Definition pushM2R (k : N) (xs : list RTok) : list RTok :=
  match xs with
  | M2R m :: rest => M2R (k + 1 + m) :: rest
  | _ => M2R k :: xs
  end.

Definition addR (m : N) (xs : list RTok) : list RTok :=
  match unconsR xs with
  | None => pushR0 m []
  | Some (RHR0 d, rest) => pushR0 (d + m + 1) rest
  | Some (RHR1 d, rest) => R1 (d + m + 1) :: rest
  end.

Definition pushWM1 (k : N) (l : list LTok) : list LTok :=
  let l4 := bumpL (bumpL (bumpL (bumpL l))) in
  let lMid := LD 3 :: LD1 1 :: LD 5 :: L0 1 :: LD 5 :: LD 5 :: l4 in
  if k =? 0 then LD 3 :: lMid else LD 3 :: pushML8 (k - 1) lMid.

Definition pushWM2 (k : N) (l : list LTok) : list LTok :=
  let l2 := bumpL (bumpL l) in
  let lMid := LD 7 :: LD 3 :: pushLD1 5 l2 in
  let lBody := if k =? 0 then lMid else pushM2L (k - 1) lMid in
  L0 0 :: LD1 5 :: LD 5 :: lBody.

Definition normB0W3 (m : Mode) (l : list LTok) (r : list RTok) : list LTok :=
  match m with
  | MDL => l
  | MB0 =>
    match popR0Eq 4 r with
    | None => l
    | Some r1 =>
      match popMR11 r1 with
      | None => l
      | Some _ =>
        match matchW3 l with
        | Some rest => LD 2 :: L0 1 :: pushM3L 0 rest
        | None => l
        end
      end
    end
  end.

Definition beqLTok (x y : LTok) : bool :=
  match x, y with
  | L0 a, L0 b => a =? b
  | LD a, LD b => a =? b
  | LD1 a, LD1 b => a =? b
  | ML8 a, ML8 b => a =? b
  | M2L a, M2L b => a =? b
  | M3L a, M3L b => a =? b
  | M4L a, M4L b => a =? b
  | _, _ => false
  end.

Fixpoint stripLPrefix (pfx xs : list LTok) : option (list LTok) :=
  match pfx, xs with
  | [], _ => Some xs
  | p :: ps, x :: xs' => if beqLTok p x then stripLPrefix ps xs' else None
  | _ :: _, [] => None
  end.

Definition beqRTok (x y : RTok) : bool :=
  match x, y with
  | R0 a, R0 b => a =? b
  | R1 a, R1 b => a =? b
  | R02 a, R02 b => a =? b
  | MR11 a, MR11 b => a =? b
  | M2R a, M2R b => a =? b
  | _, _ => false
  end.

Fixpoint stripRPrefix (pfx xs : list RTok) : option (list RTok) :=
  match pfx, xs with
  | [], _ => Some xs
  | p :: ps, x :: xs' => if beqRTok p x then stripRPrefix ps xs' else None
  | _ :: _, [] => None
  end.

Fixpoint beqRList (xs ys : list RTok) : bool :=
  match xs, ys with
  | [], [] => true
  | a :: as_, b :: bs => beqRTok a b && beqRList as_ bs
  | _, _ => false
  end.

(* ========================================================================= *)
(* Section 4: Soundness of Stack Operations & Recognizers                    *)
(* ========================================================================= *)

Lemma evalWin_b0_flip (l r : side) (rs : list Sym) :
  evalWin l r B false [S0] rs = evalWin l r B true [] (S0 :: rs).
Proof. reflexivity. Qed.

Lemma evalWin_b0_def (r : side) :
  evalWin (const S0) r B false [] [] = evalWin (const S0) r B true [] [S0].
Proof. reflexivity. Qed.

Lemma encodeBase_core_congr (m : Mode) {l1 l2 : list LTok} {r1 r2 : list RTok}
  (hl : eL l1 = eL l2) (hr : eR r1 = eR r2) :
  encodeBase (Core m l1 r1) = encodeBase (Core m l2 r2).
Proof. destruct m; cbn [encodeBase encodeCore]; rewrite hl, hr; reflexivity. Qed.

Lemma popL0Eq_some {v : N} {l rest : list LTok} (h : popL0Eq v l = Some rest) :
  l = L0 v :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  unfold popL0Eq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popLDEq_some {v : N} {l rest : list LTok} (h : popLDEq v l = Some rest) :
  l = LD v :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  unfold popLDEq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popLD1Eq_some {v : N} {l rest : list LTok} (h : popLD1Eq v l = Some rest) :
  l = LD1 v :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  unfold popLD1Eq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popLD1_some {k : N} {l rest : list LTok} (h : popLD1 l = Some (k, rest)) :
  l = LD1 k :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popLD1Ge4_some {k : N} {l rest : list LTok} (h : popLD1Ge4 l = Some (k, rest)) :
  l = LD1 (k + 4) :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  unfold popLD1Ge4 in h. destruct (4 <=? k0) eqn:hle; [| discriminate].
  apply N.leb_le in hle. inversion h; subst.
  replace (k0 - 4 + 4) with k0 by lia. reflexivity.
Qed.

Lemma popML8_some {k : N} {l rest : list LTok} (h : popML8 l = Some (k, rest)) :
  l = ML8 k :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popM2L_some {k : N} {l rest : list LTok} (h : popM2L l = Some (k, rest)) :
  l = M2L k :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popM3L_some {k : N} {l rest : list LTok} (h : popM3L l = Some (k, rest)) :
  l = M3L k :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popM4L_some {k : N} {l rest : list LTok} (h : popM4L l = Some (k, rest)) :
  l = M4L k :: rest.
Proof.
  destruct l as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popR0Eq_some {v : N} {r rest : list RTok} (h : popR0Eq v r = Some rest) :
  r = R0 v :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  unfold popR0Eq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popR1Eq_some {v : N} {r rest : list RTok} (h : popR1Eq v r = Some rest) :
  r = R1 v :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  unfold popR1Eq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popR02Eq_some {v : N} {r rest : list RTok} (h : popR02Eq v r = Some rest) :
  r = R02 v :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  unfold popR02Eq in h. destruct (_ =? _) eqn:heq; [| discriminate].
  apply N.eqb_eq in heq. inversion h; subst; reflexivity.
Qed.

Lemma popR02_some {k : N} {r rest : list RTok} (h : popR02 r = Some (k, rest)) :
  r = R02 k :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popMR11_some {k : N} {r rest : list RTok} (h : popMR11 r = Some (k, rest)) :
  r = MR11 k :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma popM2R_some {k : N} {r rest : list RTok} (h : popM2R r = Some (k, rest)) :
  r = M2R k :: rest.
Proof.
  destruct r as [| [] xs]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma eL_peelLD1 (k : N) (xs : list LTok) :
  eL (peelLD1 k xs) = repBlock wLD1 k *> eL xs.
Proof.
  unfold peelLD1. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_peelML8 (k : N) (xs : list LTok) :
  eL (peelML8 k xs) = repBlock uM k *> eL xs.
Proof.
  unfold peelML8. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_peelM2L (k : N) (xs : list LTok) :
  eL (peelM2L k xs) = repBlock uM2 k *> eL xs.
Proof.
  unfold peelM2L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_peelM3L (k : N) (xs : list LTok) :
  eL (peelM3L k xs) = repBlock wM3 k *> eL xs.
Proof.
  unfold peelM3L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_peelM4L (k : N) (xs : list LTok) :
  eL (peelM4L k xs) = repBlock wM4 k *> eL xs.
Proof.
  unfold peelM4L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_peelR02 (k : N) (xs : list RTok) :
  eR (peelR02 k xs) = repBlock wLD1 k *> eR xs.
Proof.
  unfold peelR02. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_peelMR11 (k : N) (xs : list RTok) :
  eR (peelMR11 k xs) = repBlock vM k *> eR xs.
Proof.
  unfold peelMR11. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_peelM2R (k : N) (xs : list RTok) :
  eR (peelM2R k xs) = repBlock vM2 k *> eR xs.
Proof.
  unfold peelM2R. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_mid42 (xs : list LTok) :
  eL (LD 3 :: LD1 1 :: LD 5 :: L0 1 :: LD 5 :: LD 5 :: xs) = mid42 *> eL xs.
Proof. reflexivity. Qed.

Lemma eL_lu (xs : list LTok) :
  eL (LD 3 :: LD1 1 :: LD 5 :: L0 1 :: LD 5 :: LD 5 :: LD 7 :: xs) = uM *> eL xs.
Proof. reflexivity. Qed.

Lemma eL_u2 (xs : list LTok) :
  eL (LD 7 :: LD 3 :: LD1 12 :: LD 5 :: xs) = uM2 *> eL xs.
Proof. reflexivity. Qed.

Lemma eL_w3 (xs : list LTok) :
  eL (LD 5 :: LD1 0 :: L0 2 :: LD1 0 :: L0 0 :: LD 5 :: LD 3 :: L0 3 ::
      LD1 0 :: L0 0 :: LD1 0 :: LD 7 :: LD 7 :: xs) = wM3 *> eL xs.
Proof. reflexivity. Qed.

Lemma eL_w4 (xs : list LTok) :
  eL (L0 3 :: LD 3 :: L0 0 :: LD 3 :: L0 0 :: LD1 0 :: xs) = wM4 *> eL xs.
Proof. reflexivity. Qed.

Lemma eR_ru (xs : list RTok) :
  eR (R0 2 :: R1 3 :: R02 1 :: R1 3 :: R1 3 :: R02 3 :: R1 3 :: xs) = vM *> eR xs.
Proof. reflexivity. Qed.

Lemma eR_ru2 (xs : list RTok) :
  eR (R0 2 :: R02 6 :: R1 3 :: R02 0 :: R1 3 :: R02 6 :: xs) = vM2 *> eR xs.
Proof. reflexivity. Qed.

Lemma eL_pushM4L (k : N) (xs : list LTok) :
  eL (pushM4L k xs) = repBlock wM4 (k + 1) *> eL xs.
Proof.
  destruct xs as [| [] rest]; try reflexivity.
  cbn [pushM4L eL].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_foldWM4 (xs : list LTok) : eL (foldWM4 xs) = eL xs.
Proof.
  unfold foldWM4.
  destruct (popL0Eq 3 xs) as [l1 |] eqn:h1; [| reflexivity].
  destruct (popLDEq 3 l1) as [l2 |] eqn:h2; [| reflexivity].
  destruct (popL0Eq 0 l2) as [l3 |] eqn:h3; [| reflexivity].
  destruct (popLDEq 3 l3) as [l4 |] eqn:h4; [| reflexivity].
  destruct (popL0Eq 0 l4) as [l5 |] eqn:h5; [| reflexivity].
  destruct (popLD1 l5) as [[rem rest] |] eqn:h6; [| reflexivity].
  rewrite (popL0Eq_some h1), (popLDEq_some h2), (popL0Eq_some h3),
          (popLDEq_some h4), (popL0Eq_some h5), (popLD1_some h6), eL_pushM4L.
  change (0 + 1) with 1. rewrite repBlock_1, <- eL_w4.
  assert (htail : eL (LD1 0 :: peelLD1 rem rest) = eL (LD1 rem :: rest)).
  { change (eL (LD1 0 :: peelLD1 rem rest)) with (wLD1 *> eL (peelLD1 rem rest)).
    rewrite eL_peelLD1, <- Str_app_assoc, <- repBlock_succ_left. reflexivity. }
  cbn [eL] in htail |- *. rewrite htail. reflexivity.
Qed.

Lemma eL_peelL0 (k : N) (xs : list LTok) :
  eL (L0 k :: xs) = wL0 *> eL (peelL0 k xs).
Proof.
  unfold peelL0. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. rewrite eL_foldWM4.
    cbn [eL]. replace k with ((k - 1) + 1) at 1 by lia.
    rewrite repBlock_succ_left, Str_app_assoc. reflexivity.
Qed.

Lemma unconsL_none {l : list LTok} (h : unconsL l = None) : l = [].
Proof. destruct l as [| [] ?]; try discriminate; reflexivity. Qed.

Lemma unconsL_L0 {l rest : list LTok} {k : N}
  (h : unconsL l = Some (LHL0 k, rest)) : eL l = eL (L0 k :: rest).
Proof.
  destruct l as [| [] xs]; try discriminate; cbn [unconsL] in h; inversion h; subst.
  - reflexivity.
  - unfold lw4Tail. rewrite eL_w4, eL_peelM4L, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma unconsL_LD {l rest : list LTok} {v : N}
  (h : unconsL l = Some (LHLD v, rest)) : eL l = eL (LD v :: rest).
Proof.
  destruct l as [| [] xs]; try discriminate; cbn [unconsL] in h; inversion h; subst.
  - reflexivity.
  - change (eL (LD 1 :: peelLD1 k xs)) with (wLD1 *> eL (peelLD1 k xs)).
    rewrite eL_peelLD1, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
  - unfold luTail. rewrite eL_lu, eL_peelML8, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
  - unfold lu2Tail. rewrite eL_u2, eL_peelM2L, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
  - unfold lw3Tail. rewrite eL_w3, eL_peelM3L, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma unconsR_none {r : list RTok} (h : unconsR r = None) : r = [].
Proof. destruct r as [| [] ?]; try discriminate; reflexivity. Qed.

Lemma unconsR_R0 {r rest : list RTok} {d : N}
  (h : unconsR r = Some (RHR0 d, rest)) : eR r = eR (R0 d :: rest).
Proof.
  destruct r as [| [] xs]; try discriminate; cbn [unconsR] in h; inversion h; subst.
  - reflexivity.
  - change (eR (R0 2 :: peelR02 k xs)) with (wLD1 *> eR (peelR02 k xs)).
    rewrite eR_peelR02, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
  - unfold ruTail. rewrite eR_ru, eR_peelMR11, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
  - unfold ru2Tail. rewrite eR_ru2, eR_peelM2R, <- Str_app_assoc, <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma unconsR_R1 {r rest : list RTok} {d : N}
  (h : unconsR r = Some (RHR1 d, rest)) : eR r = eR (R1 d :: rest).
Proof.
  destruct r as [| [] xs]; try discriminate; cbn [unconsR] in h; inversion h; subst.
  reflexivity.
Qed.

Lemma matchU1_some {l rest : list LTok} (h : matchU1 l = Some rest) :
  eL l = uM *> eL rest.
Proof.
  unfold matchU1 in h.
  destruct (popLDEq 3 l) as [l1 |] eqn:h1; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 1 l1) as [l2 |] eqn:h2; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 5 l2) as [l3 |] eqn:h3; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 1 l3) as [l4 |] eqn:h4; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 5 l4) as [l5 |] eqn:h5; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 5 l5) as [l6 |] eqn:h6; [cbn [opt_bind] in h | discriminate].
  rewrite (popLDEq_some h1), (popLD1Eq_some h2), (popLDEq_some h3), (popL0Eq_some h4),
          (popLDEq_some h5), (popLDEq_some h6), (popLDEq_some h).
  reflexivity.
Qed.

Lemma matchU2_some {l rest : list LTok} (h : matchU2 l = Some rest) :
  eL l = uM2 *> eL rest.
Proof.
  unfold matchU2 in h.
  destruct (popLDEq 7 l) as [l1 |] eqn:h1; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 3 l1) as [l2 |] eqn:h2; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 12 l2) as [l3 |] eqn:h3; [cbn [opt_bind] in h | discriminate].
  rewrite (popLDEq_some h1), (popLDEq_some h2), (popLD1Eq_some h3), (popLDEq_some h).
  reflexivity.
Qed.

Lemma eL_pushLD1 (k : N) (xs : list LTok) :
  eL (pushLD1 k xs) = repBlock wLD1 (k + 1) *> eL xs.
Proof.
  destruct xs as [| [] rest]; try reflexivity.
  cbn [pushLD1 eL].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_pushLD (v : N) (xs : list LTok) :
  eL (pushLD v xs) = eL (LD v :: xs).
Proof.
  unfold pushLD. destruct (v =? 1) eqn:hv.
  - apply N.eqb_eq in hv; subst. rewrite eL_pushLD1. reflexivity.
  - reflexivity.
Qed.

Lemma eL_pushML8 (k : N) (xs : list LTok) :
  eL (pushML8 k xs) = repBlock uM (k + 1) *> eL xs.
Proof.
  destruct xs as [| [] rest]; try reflexivity.
  cbn [pushML8 eL].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_pushM2LRaw (k : N) (xs : list LTok) :
  eL (pushM2LRaw k xs) = repBlock uM2 (k + 1) *> eL xs.
Proof.
  destruct xs as [| [] rest]; try reflexivity.
  cbn [pushM2LRaw eL].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_pushM2L (k : N) (xs : list LTok) :
  eL (pushM2L k xs) = repBlock uM2 (k + 1) *> eL xs.
Proof.
  unfold pushM2L. destruct (matchU2 xs) as [rest |] eqn:hm.
  - rewrite eL_pushM2LRaw, (matchU2_some hm), repBlock_succ_right, Str_app_assoc.
    reflexivity.
  - exact (eL_pushM2LRaw k xs).
Qed.

Lemma eL_pushM3L (k : N) (xs : list LTok) :
  eL (pushM3L k xs) = repBlock wM3 (k + 1) *> eL xs.
Proof.
  destruct xs as [| [] rest]; try reflexivity.
  cbn [pushM3L eL].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma pushM3L_pushM3L (a b : N) (xs : list LTok) :
  pushM3L a (pushM3L b xs) = pushM3L (a + 1 + b) xs.
Proof.
  destruct xs as [| [] rest]; cbn [pushM3L]; f_equal; f_equal; lia.
Qed.

Lemma pushM4L_pushM4L (a b : N) (xs : list LTok) :
  pushM4L a (pushM4L b xs) = pushM4L (a + 1 + b) xs.
Proof.
  destruct xs as [| [] rest]; cbn [pushM4L]; f_equal; f_equal; lia.
Qed.

Lemma eL_pushL0Raw (k : N) (xs : list LTok) :
  eL (pushL0Raw k xs) = repBlock wL0 (k + 1) *> eL xs.
Proof.
  unfold pushL0Raw. destruct (unconsL xs) as [[[m | m] rest] |] eqn:hu; try reflexivity.
  rewrite (unconsL_L0 hu). cbn [eL].
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_pushL0 (k : N) (xs : list LTok) :
  eL (pushL0 k xs) = repBlock wL0 (k + 1) *> eL xs.
Proof. unfold pushL0. rewrite eL_foldWM4. exact (eL_pushL0Raw k xs). Qed.

Lemma eL_pushZeros (q : N) (xs : list LTok) :
  eL (pushZeros q xs) = repBlock wL0 q *> eL xs.
Proof.
  unfold pushZeros. destruct (q =? 0) eqn:hq.
  - apply N.eqb_eq in hq; subst; reflexivity.
  - apply N.eqb_neq in hq. rewrite eL_pushL0.
    replace (q - 1 + 1) with q by lia. reflexivity.
Qed.

Lemma eL_bumpL (xs : list LTok) : eL (bumpL xs) = [S1] *> eL xs.
Proof.
  unfold bumpL. destruct (unconsL xs) as [[[v | v] rest] |] eqn:hu.
  - rewrite (unconsL_L0 hu), eL_pushLD, eL_peelL0. reflexivity.
  - rewrite (unconsL_LD hu), eL_pushLD. cbn [eL].
    replace (v + 1 + 2) with (1 + (v + 2)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - rewrite (unconsL_none hu).
    change (eL [L0 0]) with (S1 >> (S0 >> const S0)).
    rewrite zero_cons_def. reflexivity.
Qed.

Lemma eR_pushR02 (k : N) (rs : list RTok) :
  eR (pushR02 k rs) = repBlock wLD1 (k + 1) *> eR rs.
Proof.
  destruct rs as [| [] rest]; try reflexivity.
  cbn [pushR02 eR].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_pushR0 (d : N) (rs : list RTok) :
  eR (pushR0 d rs) = eR (R0 d :: rs).
Proof.
  unfold pushR0. destruct (d =? 2) eqn:hd.
  - apply N.eqb_eq in hd; subst. rewrite eR_pushR02. reflexivity.
  - reflexivity.
Qed.

Lemma eR_pushMR11 (k : N) (rs : list RTok) :
  eR (pushMR11 k rs) = repBlock vM (k + 1) *> eR rs.
Proof.
  destruct rs as [| [] rest]; try reflexivity.
  cbn [pushMR11 eR].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_pushM2R (k : N) (rs : list RTok) :
  eR (pushM2R k rs) = repBlock vM2 (k + 1) *> eR rs.
Proof.
  destruct rs as [| [] rest]; try reflexivity.
  cbn [pushM2R eR].
  replace (k + 1 + k0 + 1) with ((k + 1) + (k0 + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_addR (m : N) (rs : list RTok) :
  eR (addR m rs) = repBlock [S1] (m + 1) *> eR rs.
Proof.
  unfold addR. destruct (unconsR rs) as [[[d | d] rest] |] eqn:hu.
  - rewrite (unconsR_R0 hu), eR_pushR0. cbn [eR].
    replace (d + m + 1 + 1) with ((m + 1) + (d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - rewrite (unconsR_R1 hu). cbn [eR].
    replace (d + m + 1 + 1) with ((m + 1) + (d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - rewrite (unconsR_none hu), eR_pushR0. cbn [eR Str_app].
    rewrite zero_cons_def. reflexivity.
Qed.

Lemma wM_pow_eq (k : N) (s : side) :
  repBlock wM (k + 1) *> s = ld3Bits *> (repBlock uM k *> (mid42 *> (ones4 *> s))).
Proof.
  revert s; pattern k; apply N.peano_ind; intro s.
  - change (0 + 1) with 1. rewrite repBlock_1, repBlock_0.
    unfold wM. rewrite !Str_app_assoc. reflexivity.
  - intros IH. replace (N.succ s) with (s + 1) by lia. intro s0.
    rewrite (repBlock_succ_left wM (s + 1)), Str_app_assoc, (IH s0).
    change wM with (ld3Bits ++ (mid42 ++ ones4)).
    rewrite !Str_app_assoc.
    change (ones4 *> (ld3Bits *> ?x)) with ((ones4 ++ ld3Bits) *> x).
    change (ones4 ++ ld3Bits) with ld7Bits.
    rewrite <- (Str_app_assoc mid42 ld7Bits).
    change (mid42 ++ ld7Bits) with uM.
    rewrite <- (Str_app_assoc uM (repBlock uM s)), <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma eL_pushWM1 (k : N) (l : list LTok) :
  eL (pushWM1 k l) = repBlock wM (k + 1) *> eL l.
Proof.
  assert (hl4 : eL (bumpL (bumpL (bumpL (bumpL l)))) = ones4 *> eL l).
  { rewrite !eL_bumpL. reflexivity. }
  rewrite (wM_pow_eq k (eL l)).
  unfold pushWM1. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst.
    change (eL (LD 3 :: ?xs)) with (ld3Bits *> eL xs).
    rewrite eL_mid42, hl4. reflexivity.
  - apply N.eqb_neq in hk.
    change (eL (LD 3 :: ?xs)) with (ld3Bits *> eL xs).
    rewrite eL_pushML8, eL_mid42, hl4.
    replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma wM2_pow_eq (k : N) (s : side) :
  repBlock wM2 (k + 1) *> s = wM2Prefix34 *> (repBlock uM2 k *> (wM2Mid40 *> ([S1; S1] *> s))).
Proof.
  revert s; pattern k; apply N.peano_ind; intro s.
  - change (0 + 1) with 1. rewrite repBlock_1, repBlock_0.
    unfold wM2. rewrite !Str_app_assoc. reflexivity.
  - intros IH. replace (N.succ s) with (s + 1) by lia. intro s0.
    rewrite (repBlock_succ_left wM2 (s + 1)), Str_app_assoc, (IH s0).
    change wM2 with (wM2Prefix34 ++ (wM2Mid40 ++ [S1; S1])).
    rewrite !Str_app_assoc.
    rewrite <- (Str_app_assoc [S1; S1] wM2Prefix34).
    rewrite <- (Str_app_assoc wM2Mid40 ([S1; S1] ++ wM2Prefix34)).
    change (wM2Mid40 ++ ([S1; S1] ++ wM2Prefix34)) with uM2.
    rewrite <- (Str_app_assoc uM2 (repBlock uM2 s)), <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma eL_pushWM2 (k : N) (l : list LTok) :
  eL (pushWM2 k l) = repBlock wM2 (k + 1) *> eL l.
Proof.
  assert (hl2 : eL (bumpL (bumpL l)) = [S1; S1] *> eL l).
  { rewrite !eL_bumpL. reflexivity. }
  assert (hmid : forall xs, eL (LD 7 :: LD 3 :: pushLD1 5 xs) = wM2Mid40 *> eL xs).
  { intro xs.
    change (eL (LD 7 :: LD 3 :: pushLD1 5 xs)) with ((ld7Bits ++ ld3Bits) *> eL (pushLD1 5 xs)).
    rewrite eL_pushLD1. reflexivity. }
  rewrite (wM2_pow_eq k (eL l)).
  unfold pushWM2. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst.
    change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite hmid, hl2. reflexivity.
  - apply N.eqb_neq in hk.
    change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite eL_pushM2L, hmid, hl2.
    replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma wR02_pow_eq (k : N) (s : side) :
  repBlock [S1; S0; S1; S1] (k + 1) *> s = wL0 *> (repBlock wLD1 k *> ([S1; S1] *> s)).
Proof.
  revert s; pattern k; apply N.peano_ind; intro s.
  - reflexivity.
  - intros IH. replace (N.succ s) with (s + 1) by lia. intro s0.
    rewrite (repBlock_succ_left [S1; S0; S1; S1] (s + 1)), Str_app_assoc, (IH s0).
    change [S1; S0; S1; S1] with (wL0 ++ [S1; S1]).
    rewrite Str_app_assoc, <- (Str_app_assoc [S1; S1] wL0).
    change ([S1; S1] ++ wL0) with wLD1.
    rewrite <- (Str_app_assoc wLD1 (repBlock wLD1 s)), <- repBlock_succ_left.
    reflexivity.
Qed.

Lemma eq_of_beqLTok {a b : LTok} (h : beqLTok a b = true) : a = b.
Proof.
  destruct a, b; try discriminate; cbn in h; apply N.eqb_eq in h; subst; reflexivity.
Qed.

Lemma stripLPrefix_some :
  forall pfx xs rest, stripLPrefix pfx xs = Some rest -> xs = pfx ++ rest.
Proof.
  induction pfx as [| p ps IH]; intros [| x xs] rest h; try discriminate.
  - inversion h; reflexivity.
  - inversion h; reflexivity.
  - cbn [stripLPrefix] in h. destruct (beqLTok p x) eqn:hb; [| discriminate].
    rewrite <- (eq_of_beqLTok hb), (IH xs rest h). reflexivity.
Qed.

Lemma eq_of_beqRTok {a b : RTok} (h : beqRTok a b = true) : a = b.
Proof.
  destruct a, b; try discriminate; cbn in h; apply N.eqb_eq in h; subst; reflexivity.
Qed.

Lemma stripRPrefix_some :
  forall pfx xs rest, stripRPrefix pfx xs = Some rest -> xs = pfx ++ rest.
Proof.
  induction pfx as [| p ps IH]; intros [| x xs] rest h; try discriminate.
  - inversion h; reflexivity.
  - inversion h; reflexivity.
  - cbn [stripRPrefix] in h. destruct (beqRTok p x) eqn:hb; [| discriminate].
    rewrite <- (eq_of_beqRTok hb), (IH xs rest h). reflexivity.
Qed.

Lemma eq_of_beqRList : forall a b, beqRList a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] h; try discriminate.
  - reflexivity.
  - cbn in h. apply andb_prop in h. destruct h as [hx hxs].
    rewrite (eq_of_beqRTok hx), (IH ys hxs). reflexivity.
Qed.

Lemma matchW3_some {l rest : list LTok} (h : matchW3 l = Some rest) :
  eL l = eL (LD 2 :: L0 1 :: pushM3L 0 rest).
Proof.
  unfold matchW3 in h.
  destruct (popLDEq 2 l) as [l1 |] eqn:h1; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 1 l1) as [l2 |] eqn:h2; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 5 l2) as [l3 |] eqn:h3; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 0 l3) as [l4 |] eqn:h4; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 2 l4) as [l5 |] eqn:h5; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 0 l5) as [l6 |] eqn:h6; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 0 l6) as [l7 |] eqn:h7; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 5 l7) as [l8 |] eqn:h8; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 3 l8) as [l9 |] eqn:h9; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 3 l9) as [l10 |] eqn:h10; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 0 l10) as [l11 |] eqn:h11; [cbn [opt_bind] in h | discriminate].
  destruct (popL0Eq 0 l11) as [l12 |] eqn:h12; [cbn [opt_bind] in h | discriminate].
  destruct (popLD1Eq 0 l12) as [l13 |] eqn:h13; [cbn [opt_bind] in h | discriminate].
  destruct (popLDEq 7 l13) as [l14 |] eqn:h14; [cbn [opt_bind] in h | discriminate].
  rewrite (popLDEq_some h1), (popL0Eq_some h2), (popLDEq_some h3), (popLD1Eq_some h4),
          (popL0Eq_some h5), (popLD1Eq_some h6), (popL0Eq_some h7), (popLDEq_some h8),
          (popLDEq_some h9), (popL0Eq_some h10), (popLD1Eq_some h11), (popL0Eq_some h12),
          (popLD1Eq_some h13), (popLDEq_some h14), (popLDEq_some h).
  change (eL (LD 2 :: L0 1 :: ?xs)) with ([S1; S1; S1; S1; S0; S1; S0; S1; S0] *> eL xs).
  change (eL (LD 2 :: L0 1 :: pushM3L 0 rest)) with
    ([S1; S1; S1; S1; S0; S1; S0; S1; S0] *> eL (pushM3L 0 rest)).
  rewrite eL_w3, eL_pushM3L. change (0 + 1) with 1. rewrite repBlock_1. reflexivity.
Qed.

Lemma matchCapTail_true {r : list RTok} (h : matchCapTail r = true) :
  r = [R02 0; R1 3; R02 0].
Proof.
  unfold matchCapTail in h.
  destruct (popR02Eq 0 r) as [r1 |] eqn:h1; [| discriminate].
  destruct (popR1Eq 3 r1) as [r2 |] eqn:h2; [| discriminate].
  destruct (popR02Eq 0 r2) as [[| ? ?] |] eqn:h3; try discriminate.
  rewrite (popR02Eq_some h1), (popR1Eq_some h2), (popR02Eq_some h3). reflexivity.
Qed.

Lemma eL_normB0W3 (m : Mode) (l : list LTok) (r : list RTok) :
  eL (normB0W3 m l r) = eL l.
Proof.
  unfold normB0W3. destruct m; [| reflexivity].
  destruct (popR0Eq 4 r) as [r1 |]; [| reflexivity].
  destruct (popMR11 r1) as [_ |]; [| reflexivity].
  destruct (matchW3 l) as [rest |] eqn:hw; [| reflexivity].
  symmetry; exact (matchW3_some hw).
Qed.

(* ========================================================================= *)
(* Section 5: Base & Motif Macro Transitions and Soundness                   *)
(* ========================================================================= *)

Definition stepDL (l : list LTok) (r : list RTok) : BaseState :=
  match unconsL l with
  | None => Halt r
  | Some (LHL0 v, rest) => Core MDL (bumpL (peelL0 v rest)) (addR 0 r)
  | Some (LHLD v, rest) => Core MB0 rest (pushR0 v r)
  end.

Definition foldDL2 (l1 : list LTok) (r1 : list RTok) : BaseState :=
  match stepDL l1 r1 with
  | Core MDL l2 r2 => stepDL l2 r2
  | bs2 => bs2
  end.

Definition stepB0R00Cons (l : list LTok) (rRest : list RTok) : BaseState :=
  match unconsL l with
  | None => Core MB0 [] (addR 2 rRest)
  | Some (LHL0 lv, lrest) => Core MB0 (peelL0 lv lrest) (addR 3 rRest)
  | Some (LHLD lv, lrest) => Core MB0 lrest (addR (lv + 4) rRest)
  end.

Definition stepB0OddQ0 (l : list LTok) (rNew : list RTok) : BaseState :=
  match unconsL l with
  | None => Core MDL [] (R0 0 :: rNew)
  | Some (LHL0 lv, lrest) => Core MB0 (peelL0 lv lrest) (addR 1 rNew)
  | Some (LHLD lv, lrest) => Core MB0 lrest (addR (lv + 2) rNew)
  end.

Definition stepB0Pos (isR1 : bool) (dp : N) (l : list LTok) (rRest : list RTok) : BaseState :=
  let q := dp / 2 in
  let l2 := bumpL (bumpL l) in
  if dp mod 2 =? 1 then
    if isR1 then
      Core MB0 (LD 0 :: pushZeros q l2) rRest
    else
      match rRest with
      | [] => Core MDL (bumpL (bumpL (pushZeros (q + 1) l2))) [R0 0]
      | _ :: _ => Core MB0 (pushZeros q l2) (addR 1 rRest)
      end
  else
    let rNew := if isR1 then pushR0 2 rRest else addR 2 rRest in
    if q =? 0 then stepB0OddQ0 l rNew
    else if q =? 1 then Core MB0 l2 rNew
    else foldDL2 (pushZeros (q - 2) l2) (R1 0 :: rNew).

Definition stepB0Base (l : list LTok) (r : list RTok) : BaseState :=
  match unconsR r with
  | None => Core MDL (bumpL l) [R0 0]
  | Some (RHR0 d, rRest) =>
    if d =? 0 then
      match rRest with
      | [] => Core MDL (bumpL (bumpL (bumpL (bumpL l)))) [R0 0]
      | r1 :: rs => stepB0R00Cons l (r1 :: rs)
      end
    else stepB0Pos false (d - 1) l rRest
  | Some (RHR1 d, rRest) =>
    if d =? 0 then Core MB0 (bumpL (bumpL (bumpL l))) rRest
    else stepB0Pos true (d - 1) l rRest
  end.

Definition ld5ROut (k : N) (rRest : list RTok) : list RTok :=
  let rMid := R1 3 :: R02 0 :: R1 3 :: pushR02 1 rRest in
  if k =? 0 then rMid else pushR02 (k - 1) rMid.

Definition r02LOut (k : N) (l : list LTok) : list LTok :=
  let l2 := bumpL (bumpL l) in
  let lMid := if k =? 0 then l2 else pushLD1 (k - 1) l2 in
  pushL0 0 lMid.

Definition stepMotifB0 (l : list LTok) (r : list RTok) : option BaseState :=
  match popR0Eq 4 r with
  | Some rAfter4 =>
    match popR02 rAfter4 with
    | None => None
    | Some (kr, r2) =>
      if kr =? 0 then
        match popMR11 r2 with
        | Some (k, r3) =>
          if matchCapTail r3 then
            match popLDEq 3 l with
            | Some lRest =>
              Some (Core MB0 (LD 7 :: lRest) [R0 9; R1 0; MR11 k; R02 0; R1 3; R02 0])
            | None =>
              Some (Core MB0 (pushWM1 k l) (R0 4 :: pushR02 0 r3))
            end
          else
            Some (Core MB0 (pushWM1 k l) (R0 4 :: pushR02 0 r3))
        | None =>
          match popM2R r2 with
          | Some (k, r3) =>
            Some (Core MB0 (pushWM2 k l) (R0 4 :: pushR02 0 r3))
          | None => None
          end
        end
      else
        Some (Core MB0 (r02LOut (kr - 1) l) (R0 4 :: pushR02 0 r2))
    end
  | None =>
    match popR0Eq 9 r with
    | Some rAfter9 =>
      match popR1Eq 0 rAfter9 with
      | None => None
      | Some rRest =>
        match popLDEq 7 l with
        | None => None
        | Some l1 =>
          match popML8 l1 with
          | Some (k, lRest) =>
            Some (Core MB0 (LD 7 :: lRest) (R0 9 :: R1 0 :: pushMR11 k rRest))
          | None =>
            match matchU1 l1 with
            | Some lRest =>
              Some (Core MB0 (LD 7 :: lRest) (R0 9 :: R1 0 :: pushMR11 0 rRest))
            | None => None
            end
          end
        end
      end
    | None =>
      match popR1Eq 9 r with
      | Some rRest =>
        match popLD1 l with
        | Some (k, lRest) =>
          Some (Core MB0 lRest (R1 9 :: pushR02 k rRest))
        | None =>
          match popLDEq 5 l with
          | None => None
          | Some l1 =>
            match popM2L l1 with
            | Some (k, lRest) =>
              Some (Core MB0 (LD 5 :: lRest) (R1 9 :: pushM2R k rRest))
            | None =>
              match matchU2 l1 with
              | Some lRest =>
                Some (Core MB0 (LD 5 :: lRest) (R1 9 :: pushM2R 0 rRest))
              | None => None
              end
            end
          end
        end
      | None =>
        match popR1Eq 5 r with
        | None => None
        | Some rRest =>
          match popLDEq 5 l with
          | None => None
          | Some l1 =>
            match popLD1Ge4 l1 with
            | None => None
            | Some (k, lRest) =>
              Some (Core MB0 lRest (R1 9 :: ld5ROut k rRest))
            end
          end
        end
      end
    end
  end.

Definition stepCoreRaw (m : Mode) (l : list LTok) (r : list RTok) : BaseState :=
  match m with
  | MDL => stepDL l r
  | MB0 =>
    match stepMotifB0 l r with
    | Some res => res
    | None => stepB0Base l r
    end
  end.

Definition tailAfter1R (t : RTok) (rs : list RTok) : side :=
  match t with
  | R0 d => repBlock [S1] d *> ([S0] *> eR rs)
  | R1 d => repBlock [S1] d *> ([S0; S0] *> eR rs)
  | R02 k => [S1; S1; S0] *> (repBlock wLD1 k *> eR rs)
  | MR11 k => vMTail *> (repBlock vM k *> eR rs)
  | M2R k => vM2Tail *> (repBlock vM2 k *> eR rs)
  end.

Lemma eR_cons_one (t : RTok) (rs : list RTok) :
  eR (t :: rs) = [S1] *> tailAfter1R t rs.
Proof.
  destruct t as [d | d | k | k | k]; cbn [eR tailAfter1R];
    rewrite repBlock_succ_left, Str_app_assoc; reflexivity.
Qed.

Lemma pow_one_even (q : N) :
  repBlock [S1] (2 * q) = repBlock [S1; S1] q.
Proof.
  pattern q; apply N.peano_ind; [reflexivity |].
  intros m IH.
  replace (N.succ m) with (m + 1) by lia.
  replace (2 * (m + 1)) with (2 + 2 * m) by lia.
  rewrite repBlock_add, IH, (repBlock_succ_left [S1; S1] m). reflexivity.
Qed.

Lemma stepDL_sound (l : list LTok) (r : list RTok) :
  encodeBase (Core MDL l r) -[ tm ]->* encodeBase (stepDL l r).
Proof.
  unfold stepDL. destruct (unconsL l) as [[[v | v] rest] |] eqn:hl.
  - refine (chkWin_eq false false 3%nat D false [S1; S0] [] D false [S1] [S1]
      (eL (peelL0 v rest)) (eR r) (@no_false _) (@no_false _) _ _ eq_refl).
    + cbn [encodeBase encodeCore]. rewrite (unconsL_L0 hl), eL_peelL0. reflexivity.
    + cbn [encodeBase encodeCore]. rewrite eL_bumpL, (eR_addR 0 r). reflexivity.
  - destruct (v =? 0) eqn:hv0.
    + apply N.eqb_eq in hv0; subst v.
      refine (chkWin_eq false false 2%nat D false [S1; S1; S0] [] B false [S0] [S1; S0]
        (eL rest) (eR r) (@no_false _) (@no_false _) _ _ eq_refl).
      * cbn [encodeBase encodeCore]. rewrite (unconsL_LD hl). reflexivity.
      * cbn [encodeBase encodeCore]. rewrite eR_pushR0, <- evalWin_b0_flip. reflexivity.
    + apply N.eqb_neq in hv0.
      set (a := v - 1).
      assert (hv : v = a + 1) by lia.
      rewrite hv in hl |- *.
      assert (h1 : encodeBase (Core MDL l r) -[ tm ]->*
                   evalWin (repBlock [S1] (a + 2) *> ([S0] *> eL rest)) ([S0] *> eR r) B false [] []).
      { refine (chkWin_eq false false 1%nat D false [S1] [] B false [] [S0]
          (repBlock [S1] (a + 2) *> ([S0] *> eL rest)) (eR r)
          (@no_false _) (@no_false _) _ eq_refl eq_refl).
        cbn [encodeBase encodeCore]. rewrite (unconsL_LD hl). cbn [eL].
        replace (a + 1 + 2) with ((a + 2) + 1) by lia.
        rewrite repBlock_succ_left, Str_app_assoc. reflexivity. }
      eapply rs_trans; [exact h1 |].
      pose proof (walkWordLeft 1%nat B false [] [S1] [] [S1] eq_refl (a + 2)
        ([S0] *> eL rest) ([S0] *> eR r)) as hw.
      assert (hend : evalWin ([S0] *> eL rest) (repBlock [S1] (a + 2) *> ([S0] *> eR r)) B false [] [] =
                     encodeBase (Core MB0 rest (pushR0 (a + 1) r))).
      { cbn [encodeBase encodeCore]. rewrite eR_pushR0. cbn [eR].
        replace (a + 1 + 1) with (a + 2) by lia.
        rewrite <- evalWin_b0_flip. reflexivity. }
      rewrite <- hend. exact hw.
  - rewrite (unconsL_none hl).
    eapply evstep_step; [exact (@step_left tm D E S0 S1 (const S0) (eR r) eq_refl) | apply rs_refl].
Qed.

Lemma foldDL2_sound (c_init : Q * tape) (l1 : list LTok) (r1 : list RTok)
  (h1 : c_init -[ tm ]->* encodeBase (Core MDL l1 r1)) :
  c_init -[ tm ]->* encodeBase (foldDL2 l1 r1).
Proof.
  unfold foldDL2.
  pose proof (stepDL_sound l1 r1) as hr2.
  destruct (stepDL l1 r1) as [| [|] l2 r2 | rH].
  - exact (rs_trans h1 hr2).
  - exact (rs_trans h1 hr2).
  - exact (rs_trans (rs_trans h1 hr2) (stepDL_sound l2 r2)).
  - exact (rs_trans h1 hr2).
Qed.

Lemma stepB0R00Cons_sound (l : list LTok) (r1 : RTok) (rs : list RTok)
  (r : list RTok) (hr : eR r = eR (R0 0 :: r1 :: rs)) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (stepB0R00Cons l (r1 :: rs)).
Proof.
  assert (h7 : encodeBase (Core MB0 l r) -[ tm ]->*
               evalWin (eL l) (eR (addR 2 (r1 :: rs))) B false [] []).
  { refine (chkWin_eq false false 7%nat B true [] [S0; S1; S0; S1] B false [] [S1; S1; S1; S1]
      (eL l) (tailAfter1R r1 rs) (@no_false _) (@no_false _) _ _ eq_refl).
    - cbn [encodeBase encodeCore]. rewrite hr.
      change (eR (R0 0 :: r1 :: rs)) with ([S1; S0] *> eR (r1 :: rs)).
      rewrite (eR_cons_one r1 rs). reflexivity.
    - rewrite (eR_addR 2 (r1 :: rs)), (eR_cons_one r1 rs). reflexivity. }
  unfold stepB0R00Cons.
  destruct (unconsL l) as [[[lv | lv] lrest] |] eqn:hl.
  - eapply rs_trans; [exact h7 |].
    refine (chkWin_eq false false 1%nat B false [S1] [] B false [] [S1]
      ([S0] *> eL (peelL0 lv lrest)) (eR (addR 2 (r1 :: rs)))
      (@no_false _) (@no_false _) _ _ eq_refl).
    + rewrite (unconsL_L0 hl), eL_peelL0. reflexivity.
    + cbn [encodeBase encodeCore]. rewrite (eR_addR 3 (r1 :: rs)), (eR_addR 2 (r1 :: rs)), <- evalWin_b0_flip.
      reflexivity.
  - eapply rs_trans; [exact h7 |].
    assert (hend : encodeBase (Core MB0 lrest (addR (lv + 4) (r1 :: rs))) =
                   evalWin ([S0] *> eL lrest) (repBlock [S1] (lv + 2) *> eR (addR 2 (r1 :: rs))) B false [] []).
    { cbn [encodeBase encodeCore]. rewrite (eR_addR (lv + 4) (r1 :: rs)), (eR_addR 2 (r1 :: rs)).
      change (2 + 1) with 3. rewrite <- Str_app_assoc, <- repBlock_add, <- evalWin_b0_flip.
      replace (lv + 2 + 3) with (lv + 4 + 1) by lia. reflexivity. }
    rewrite (unconsL_LD hl), hend.
    exact (walkWordLeft 1%nat B false [] [S1] [] [S1] eq_refl (lv + 2)
      ([S0] *> eL lrest) (eR (addR 2 (r1 :: rs)))).
  - rewrite (unconsL_none hl) in h7 |- *.
    assert (hend : evalWin (eL []) (eR (addR 2 (r1 :: rs))) B false [] [] =
                   encodeBase (Core MB0 [] (addR 2 (r1 :: rs)))) by reflexivity.
    rewrite <- hend. exact h7.
Qed.

Lemma stepB0OddQ0_sound (l : list LTok) (rNew : list RTok) (rTail : side)
  (hrNew : eR rNew = [S1; S1; S1] *> rTail) :
  evalWin (eL l) rTail B true [] [S0; S1; S1; S0] -[ tm ]->*
  encodeBase (stepB0OddQ0 l rNew).
Proof.
  unfold stepB0OddQ0.
  destruct (unconsL l) as [[[lv | lv] lrest] |] eqn:hl.
  - refine (chkWin_eq false false 12%nat B true [S1] [S0; S1; S1; S0] B false [] [S1; S1; S1; S1; S1]
      ([S0] *> eL (peelL0 lv lrest)) rTail (@no_false _) (@no_false _) _ _ eq_refl).
    + rewrite (unconsL_L0 hl), eL_peelL0. reflexivity.
    + cbn [encodeBase encodeCore]. rewrite (eR_addR 1 rNew), hrNew, <- evalWin_b0_flip. reflexivity.
  - assert (h12 : evalWin (eL l) rTail B true [] [S0; S1; S1; S0] -[ tm ]->*
                  evalWin (repBlock [S1] (lv + 1) *> ([S0] *> eL lrest)) ([S1; S1] *> eR rNew) B false [] []).
    { refine (chkWin_eq false false 12%nat B true [S1] [S0; S1; S1; S0] B false [] [S1; S1; S1; S1; S1]
        (repBlock [S1] (lv + 1) *> ([S0] *> eL lrest)) rTail
        (@no_false _) (@no_false _) _ _ eq_refl).
      - rewrite (unconsL_LD hl). cbn [eL].
        replace (lv + 2) with ((lv + 1) + 1) by lia.
        rewrite repBlock_succ_left, Str_app_assoc. reflexivity.
      - rewrite hrNew. reflexivity. }
    eapply rs_trans; [exact h12 |].
    pose proof (walkWordLeft 1%nat B false [] [S1] [] [S1] eq_refl (lv + 1)
      ([S0] *> eL lrest) ([S1; S1] *> eR rNew)) as hw.
    assert (hend : evalWin ([S0] *> eL lrest) (repBlock [S1] (lv + 1) *> ([S1; S1] *> eR rNew)) B false [] [] =
                   encodeBase (Core MB0 lrest (addR (lv + 2) rNew))).
    { change [S1; S1] with (repBlock [S1] 2).
      rewrite <- Str_app_assoc, <- repBlock_add.
      cbn [encodeBase encodeCore]. rewrite (eR_addR (lv + 2) rNew), <- evalWin_b0_flip.
      replace (lv + 1 + 2) with (lv + 2 + 1) by lia. reflexivity. }
    rewrite <- hend. exact hw.
  - rewrite (unconsL_none hl).
    refine (chkWin_eq true false 8%nat B true [] [S0; S1; S1; S0] D false [] [S1; S0; S1; S1; S1]
      (const S0) rTail (fun _ => eq_refl) (@no_false _) eq_refl _ eq_refl).
    cbn [encodeBase encodeCore eL eR]. rewrite hrNew. reflexivity.
Qed.

Lemma stepB0Pos_sound (isR1 : bool) (dp : N) (l : list LTok) (rRest : list RTok)
  (r : list RTok)
  (hr : eR r = eR ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: rRest)) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (stepB0Pos isR1 dp l rRest).
Proof.
  set (l2 := bumpL (bumpL l)).
  set (rTail := if isR1 then [S0] *> eR rRest else eR rRest).
  assert (heR_start : eR r = [S1] *> (repBlock [S1] (dp + 1) *> ([S0] *> rTail))).
  { rewrite hr. destruct isR1; unfold rTail; cbn [eR];
      replace (dp + 1 + 1) with ((dp + 1) + 1) by lia;
      rewrite (repBlock_succ_left [S1] (dp + 1)), Str_app_assoc; reflexivity. }
  assert (hinit : encodeBase (Core MB0 l r) -[ tm ]->*
                  evalWin (eL l2) (repBlock [S1] (dp + 1) *> ([S0] *> rTail)) A true [] []).
  { refine (chkWin_eq false false 2%nat B true [] [S0; S1] A true [S1; S1] []
      (eL l) (repBlock [S1] (dp + 1) *> ([S0] *> rTail))
      (@no_false _) (@no_false _) _ _ eq_refl).
    - cbn [encodeBase encodeCore]. rewrite heR_start. reflexivity.
    - unfold l2. rewrite !eL_bumpL. reflexivity. }
  unfold stepB0Pos; fold l2.
  destruct (dp mod 2 =? 1) eqn:hrem.
  - apply N.eqb_eq in hrem.
    set (q := dp / 2).
    assert (hdp : dp + 1 = 2 * q + 2) by (unfold q; lia).
    assert (hpow : repBlock [S1] (dp + 1) *> ([S0] *> rTail) =
                   repBlock [S1; S1] q *> ([S1; S1; S0] *> rTail)).
    { rewrite hdp, repBlock_add, pow_one_even, Str_app_assoc. reflexivity. }
    rewrite hpow in hinit.
    assert (h2q : encodeBase (Core MB0 l r) -[ tm ]->*
                  evalWin (eL (pushZeros q l2)) rTail A true [] [S1; S1; S0]).
    { assert (hmid : evalWin (eL (pushZeros q l2)) rTail A true [] [S1; S1; S0] =
                     evalWin (repBlock wL0 q *> eL l2) ([S1; S1; S0] *> rTail) A true [] []).
      { rewrite eL_pushZeros. reflexivity. }
      rewrite hmid.
      exact (rs_trans hinit
        (walkWordRight 2%nat A true [] wL0 [] [S1; S1] eq_refl q (eL l2) ([S1; S1; S0] *> rTail))). }
    destruct isR1.
    + unfold rTail in h2q. eapply rs_trans; [exact h2q |].
      exact (chkWin_eq false false 3%nat A true [] [S1; S1; S0; S0] B true [S1; S1; S0] [S0]
        (eL (pushZeros q l2)) (eR rRest) (@no_false _) (@no_false _) eq_refl eq_refl eq_refl).
    + unfold rTail in h2q. destruct rRest as [| r1 rs].
      * eapply rs_trans; [exact h2q |].
        refine (chkWin_eq false true 5%nat A true [] [S1; S1; S0] D false [S1; S1; S1; S0] [S1]
          (eL (pushZeros q l2)) (const S0) (@no_false _) (fun _ => eq_refl) eq_refl _ eq_refl).
        cbn [encodeBase encodeCore]. rewrite !eL_bumpL, (eL_pushZeros (q + 1)), (eL_pushZeros q).
        replace (q + 1) with (1 + q) by lia.
        rewrite (repBlock_add wL0 1 q), repBlock_1, Str_app_assoc.
        change (eR [R0 0]) with (S1 >> (S0 >> const S0)).
        rewrite zero_cons_def. reflexivity.
      * eapply rs_trans; [exact h2q |].
        refine (chkWin_eq false false 6%nat A true [] [S1; S1; S0; S1] B false [S0] [S1; S1; S1]
          (eL (pushZeros q l2)) (tailAfter1R r1 rs) (@no_false _) (@no_false _) _ _ eq_refl).
        -- rewrite (eR_cons_one r1 rs). reflexivity.
        -- cbn [encodeBase encodeCore].
           rewrite (eR_addR 1 (r1 :: rs)), (eR_cons_one r1 rs), <- evalWin_b0_flip. reflexivity.
  - apply N.eqb_neq in hrem.
    set (q := dp / 2).
    set (rNew := if isR1 then pushR0 2 rRest else addR 2 rRest).
    assert (hrNew : eR rNew = [S1; S1; S1] *> rTail).
    { unfold rNew, rTail. destruct isR1.
      - rewrite eR_pushR0. reflexivity.
      - rewrite (eR_addR 2 rRest). reflexivity. }
    destruct (q =? 0) eqn:hq0.
    + apply N.eqb_eq in hq0.
      assert (hdp0 : dp = 0) by (unfold q in hq0; lia).
      subst dp.
      assert (hstart0 : encodeBase (Core MB0 l r) = evalWin (eL l) rTail B true [] [S0; S1; S1; S0]).
      { cbn [encodeBase encodeCore]. rewrite heR_start. reflexivity. }
      rewrite hstart0. exact (stepB0OddQ0_sound l rNew rTail hrNew).
    + apply N.eqb_neq in hq0.
      assert (hdp : dp + 1 = 2 * q + 1) by (unfold q; lia).
      assert (hpow : repBlock [S1] (dp + 1) *> ([S0] *> rTail) =
                     repBlock [S1; S1] q *> ([S1; S0] *> rTail)).
      { rewrite hdp, repBlock_add, pow_one_even, Str_app_assoc. reflexivity. }
      rewrite hpow in hinit.
      pose proof (walkWordRight 2%nat A true [] wL0 [] [S1; S1] eq_refl q (eL l2) ([S1; S0] *> rTail)) as hw.
      pose proof (rs_trans hinit hw) as h2q.
      destruct (q =? 1) eqn:hq1.
      * apply N.eqb_eq in hq1. rewrite hq1 in h2q.
        eapply rs_trans; [exact h2q |].
        refine (chkWin_eq false false 8%nat A true [S1; S0; S1; S1] [S1; S0] B true [S1; S1] [S0; S1; S1; S1]
          (eL l) rTail (@no_false _) (@no_false _) _ _ eq_refl).
        -- unfold l2. rewrite !eL_bumpL. reflexivity.
        -- cbn [encodeBase encodeCore]. unfold l2. rewrite !eL_bumpL, hrNew. reflexivity.
      * apply N.eqb_neq in hq1.
        set (q' := q - 2).
        assert (hq_eq : q = q' + 2) by (unfold q'; lia).
        rewrite hq_eq in h2q.
        assert (h7 : evalWin (repBlock wL0 (q' + 2) *> eL l2) ([S1; S0] *> rTail) A true [] [] -[ tm ]->*
                     encodeBase (Core MDL (pushZeros q' l2) (R1 0 :: rNew))).
        { refine (chkWin_eq false false 7%nat A true [S1; S0; S1; S0] [S1; S0] D false [] [S1; S0; S0; S1; S1; S1]
            (repBlock wL0 q' *> eL l2) rTail (@no_false _) (@no_false _) _ _ eq_refl).
          - replace (q' + 2) with (2 + q') by lia.
            rewrite (repBlock_add wL0 2 q'), Str_app_assoc. reflexivity.
          - cbn [encodeBase encodeCore eR]. rewrite (eL_pushZeros q' l2), hrNew. reflexivity. }
        exact (foldDL2_sound _ (pushZeros q' l2) (R1 0 :: rNew) (rs_trans h2q h7)).
Qed.

Lemma stepB0Base_sound (l : list LTok) (r : list RTok) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (stepB0Base l r).
Proof.
  unfold stepB0Base. destruct (unconsR r) as [[[d | d] rRest] |] eqn:hr.
  - destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      destruct rRest as [| r1 rs].
      * refine (chkWin_eq false true 5%nat B true [] [S0; S1; S0] D false [S1; S1; S1; S1] [S1]
          (eL l) (const S0) (@no_false _) (fun _ => eq_refl) _ _ eq_refl).
        -- cbn [encodeBase encodeCore]. rewrite (unconsR_R0 hr). reflexivity.
        -- cbn [encodeBase encodeCore]. rewrite !eL_bumpL.
           change (eR [R0 0]) with (S1 >> (S0 >> const S0)).
           rewrite zero_cons_def. reflexivity.
      * exact (stepB0R00Cons_sound l r1 rs r (unconsR_R0 hr)).
    + apply N.eqb_neq in hd0.
      apply (stepB0Pos_sound false (d - 1) l rRest r).
      replace (d - 1 + 1) with d by lia. exact (unconsR_R0 hr).
  - destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      refine (chkWin_eq false false 3%nat B true [] [S0; S1; S0; S0] B true [S1; S1; S1] [S0]
        (eL l) (eR rRest) (@no_false _) (@no_false _) _ _ eq_refl).
      * cbn [encodeBase encodeCore]. rewrite (unconsR_R1 hr). reflexivity.
      * cbn [encodeBase encodeCore]. rewrite !eL_bumpL. reflexivity.
    + apply N.eqb_neq in hd0.
      apply (stepB0Pos_sound true (d - 1) l rRest r).
      replace (d - 1 + 1) with d by lia. exact (unconsR_R1 hr).
  - rewrite (unconsR_none hr).
    refine (chkWin_eq false true 2%nat B true [] [S0] D false [S1] [S1]
      (eL l) (const S0) (@no_false _) (fun _ => eq_refl) eq_refl _ eq_refl).
    cbn [encodeBase encodeCore]. rewrite eL_bumpL.
    change (eR [R0 0]) with (S1 >> (S0 >> const S0)).
    rewrite zero_cons_def. reflexivity.
Qed.

(* ========================================================================= *)
(* Section 6: Closed-Form Motif Window Certificates                          *)
(* ========================================================================= *)

Definition pLA : list Sym := [S0; S1; S1; S1; S1; S1; S1; S1; S1; S1; S0].
Definition pRA : list Sym := [S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S0; S1; S0; S0].
Definition pRB : list Sym := [S1; S1; S1; S1; S1; S0; S1; S1; S1; S0].
Definition r1_9Bits : list Sym := [S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S0; S0].
Definition pL2A : list Sym := [S0; S1; S1; S1; S1; S1; S1; S1; S0].
Definition capRIn : list Sym :=
  [S0; S1; S1; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0].
Definition capROut : list Sym :=
  [S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S0; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1].
Definition ld5InitL : list Sym :=
  [S0; S1; S1; S1; S1; S1; S1; S1; S0;
   S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0; S1; S1; S1; S0].
Definition ld5InitRIn : list Sym := [S1; S1; S1; S1; S1; S1; S0; S0].
Definition ld5InitROut : list Sym :=
  r1_9Bits ++ [S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S0].

Lemma motifA_body :
  checkWin false false 448%nat B false (pLA ++ uM) pRA B false pLA (pRA ++ vM) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma motifB_body :
  checkWin false false 494%nat B false [S0] (pRB ++ vM) B false ([S0] ++ wM) pRB = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma capTurn_body :
  checkWin false true 314%nat B true (ld3Bits ++ uM) capRIn B false (pLA ++ uM) capROut = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ld1Left_body :
  checkWin false false 34%nat B false ([S0] ++ wLD1) r1_9Bits B false [S0] (r1_9Bits ++ wLD1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma motif2A_body :
  checkWin false false 670%nat B false (pL2A ++ uM2) r1_9Bits B false pL2A (r1_9Bits ++ vM2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma motif2B_body :
  checkWin false false 368%nat B false [S0] (pRB ++ vM2) B false ([S0] ++ wM2) pRB = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ld5Init_body :
  checkWin false false 224%nat B false ld5InitL ld5InitRIn B false [S0] ld5InitROut = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma r02Right_body :
  checkWin false false 10%nat B false [S0] (pRB ++ wLD1) B false [S0; S1; S0; S1; S1] pRB = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma motifA_sound (k : N) (lRest : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 (LD 7 :: ML8 k :: lRest) (R0 9 :: R1 0 :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 (LD 7 :: lRest) (R0 9 :: R1 0 :: pushMR11 k rRest)).
Proof.
  pose proof (walkWordLeft 448%nat B false pLA uM pRA vM motifA_body (k + 1) (eL lRest) (eR rRest)) as hw.
  assert (hcfg : forall sL sR : side,
            evalWin (ld7Bits *> sL) (pRA *> sR) B true [] [S0] =
            evalWin sL sR B false pLA pRA) by reflexivity.
  assert (hstart : encodeBase (Core MB0 (LD 7 :: ML8 k :: lRest) (R0 9 :: R1 0 :: rRest)) =
                   evalWin (repBlock uM (k + 1) *> eL lRest) (eR rRest) B false pLA pRA).
  { exact (hcfg (repBlock uM (k + 1) *> eL lRest) (eR rRest)). }
  assert (hend : encodeBase (Core MB0 (LD 7 :: lRest) (R0 9 :: R1 0 :: pushMR11 k rRest)) =
                 evalWin (eL lRest) (repBlock vM (k + 1) *> eR rRest) B false pLA pRA).
  { cbn [encodeBase encodeCore].
    change (eR (R0 9 :: R1 0 :: pushMR11 k rRest)) with (pRA *> eR (pushMR11 k rRest)).
    rewrite eR_pushMR11.
    exact (hcfg (eL lRest) (repBlock vM (k + 1) *> eR rRest)). }
  rewrite hstart, hend. exact hw.
Qed.

Lemma motifB_sound (k : N) (l : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 l (R0 4 :: R02 0 :: MR11 k :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 (pushWM1 k l) (R0 4 :: pushR02 0 rRest)).
Proof.
  pose proof (walkWordRight 494%nat B false [S0] wM pRB vM motifB_body (k + 1) (eL l) (eR rRest)) as hw.
  assert (hcfg : forall sL sR : side,
            evalWin sL (pRB *> sR) B true [] [S0] = evalWin sL sR B false [S0] pRB) by reflexivity.
  assert (hstart : encodeBase (Core MB0 l (R0 4 :: R02 0 :: MR11 k :: rRest)) =
                   evalWin (eL l) (repBlock vM (k + 1) *> eR rRest) B false [S0] pRB).
  { exact (hcfg (eL l) (repBlock vM (k + 1) *> eR rRest)). }
  assert (hend : encodeBase (Core MB0 (pushWM1 k l) (R0 4 :: pushR02 0 rRest)) =
                 evalWin (repBlock wM (k + 1) *> eL l) (eR rRest) B false [S0] pRB).
  { assert (hrp : forall rs, eR (R0 4 :: pushR02 0 rs) = pRB *> eR rs).
    { intro rs. change (eR (R0 4 :: pushR02 0 rs)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 rs)).
      rewrite eR_pushR02. reflexivity. }
    cbn [encodeBase encodeCore]. rewrite eL_pushWM1, hrp.
    exact (hcfg (repBlock wM (k + 1) *> eL l) (eR rRest)). }
  rewrite hstart, hend. exact hw.
Qed.

Lemma capRoundtrip_sound (k : N) (lRest : list LTok) :
  encodeBase (Core MB0 (LD 3 :: lRest) [R0 4; R02 0; MR11 k; R02 0; R1 3; R02 0]) -[ tm ]->*
  encodeBase (Core MB0 (LD 7 :: lRest) [R0 9; R1 0; MR11 k; R02 0; R1 3; R02 0]).
Proof.
  pose proof (motifB_sound k (LD 3 :: lRest) [R02 0; R1 3; R02 0]) as h1.
  assert (heL_mid : eL (pushWM1 k (LD 3 :: lRest)) =
                    (ld3Bits ++ uM) *> (repBlock uM k *> eL lRest)).
  { rewrite eL_pushWM1, wM_pow_eq.
    change (eL (LD 3 :: lRest)) with (ld3Bits *> eL lRest).
    rewrite <- (Str_app_assoc ones4 ld3Bits).
    change (ones4 ++ ld3Bits) with ld7Bits.
    rewrite <- (Str_app_assoc mid42 ld7Bits).
    change (mid42 ++ ld7Bits) with uM.
    rewrite <- (Str_app_assoc (repBlock uM k) uM), <- repBlock_succ_right, repBlock_succ_left,
            (Str_app_assoc uM (repBlock uM k)), <- (Str_app_assoc ld3Bits uM).
    reflexivity. }
  assert (h2 : encodeBase (Core MB0 (pushWM1 k (LD 3 :: lRest))
                 (R0 4 :: pushR02 0 [R02 0; R1 3; R02 0])) -[ tm ]->*
               encodeBase (Core MB0 (LD 7 :: ML8 k :: lRest)
                 [R0 9; R1 0; R02 0; R1 3; R02 0])).
  { refine (chkWin_eq false true 314%nat B true (ld3Bits ++ uM) capRIn
      B false (pLA ++ uM) capROut (repBlock uM k *> eL lRest) (const S0)
      (@no_false _) (fun _ => eq_refl) _ _ capTurn_body).
    - cbn [encodeBase encodeCore]. rewrite heL_mid. reflexivity.
    - cbn [encodeBase encodeCore eL].
      rewrite (repBlock_succ_left uM k), (Str_app_assoc uM (repBlock uM k)), <- evalWin_b0_flip.
      assert (hr0 : capROut *> const S0 =
                    (pRA ++ [S1; S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0]) *> const S0).
      { rewrite <- zero_cons_def at 1. reflexivity. }
      unfold evalWin. rewrite !Str_app_assoc, hr0, Str_app_assoc. reflexivity. }
  pose proof (motifA_sound k lRest [R02 0; R1 3; R02 0]) as h3.
  exact (rs_trans (rs_trans h1 h2) h3).
Qed.

Lemma ld1Left_sound (k : N) (lRest : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 (LD1 k :: lRest) (R1 9 :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 lRest (R1 9 :: pushR02 k rRest)).
Proof.
  pose proof (walkWordLeft 34%nat B false [S0] wLD1 r1_9Bits wLD1 ld1Left_body
    (k + 1) (eL lRest) (eR rRest)) as hw.
  assert (hstart : encodeBase (Core MB0 (LD1 k :: lRest) (R1 9 :: rRest)) =
                   evalWin (repBlock wLD1 (k + 1) *> eL lRest) (eR rRest) B false [S0] r1_9Bits)
    by reflexivity.
  assert (hend : encodeBase (Core MB0 lRest (R1 9 :: pushR02 k rRest)) =
                 evalWin (eL lRest) (repBlock wLD1 (k + 1) *> eR rRest) B false [S0] r1_9Bits).
  { cbn [encodeBase encodeCore].
    change (eR (R1 9 :: pushR02 k rRest)) with (r1_9Bits *> eR (pushR02 k rRest)).
    rewrite eR_pushR02. reflexivity. }
  rewrite hstart, hend. exact hw.
Qed.

Lemma motif2A_sound (k : N) (lRest : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 (LD 5 :: M2L k :: lRest) (R1 9 :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 (LD 5 :: lRest) (R1 9 :: pushM2R k rRest)).
Proof.
  pose proof (walkWordLeft 670%nat B false pL2A uM2 r1_9Bits vM2 motif2A_body
    (k + 1) (eL lRest) (eR rRest)) as hw.
  assert (hcfg : forall sL sR : side,
            evalWin (ld5Bits *> sL) (r1_9Bits *> sR) B true [] [S0] =
            evalWin sL sR B false pL2A r1_9Bits) by reflexivity.
  assert (hstart : encodeBase (Core MB0 (LD 5 :: M2L k :: lRest) (R1 9 :: rRest)) =
                   evalWin (repBlock uM2 (k + 1) *> eL lRest) (eR rRest) B false pL2A r1_9Bits).
  { exact (hcfg (repBlock uM2 (k + 1) *> eL lRest) (eR rRest)). }
  assert (hend : encodeBase (Core MB0 (LD 5 :: lRest) (R1 9 :: pushM2R k rRest)) =
                 evalWin (eL lRest) (repBlock vM2 (k + 1) *> eR rRest) B false pL2A r1_9Bits).
  { cbn [encodeBase encodeCore].
    change (eR (R1 9 :: pushM2R k rRest)) with (r1_9Bits *> eR (pushM2R k rRest)).
    rewrite eR_pushM2R.
    exact (hcfg (eL lRest) (repBlock vM2 (k + 1) *> eR rRest)). }
  rewrite hstart, hend. exact hw.
Qed.

Lemma motif2B_sound (k : N) (l : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 l (R0 4 :: R02 0 :: M2R k :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 (pushWM2 k l) (R0 4 :: pushR02 0 rRest)).
Proof.
  pose proof (walkWordRight 368%nat B false [S0] wM2 pRB vM2 motif2B_body
    (k + 1) (eL l) (eR rRest)) as hw.
  assert (hcfg : forall sL sR : side,
            evalWin sL (pRB *> sR) B true [] [S0] = evalWin sL sR B false [S0] pRB) by reflexivity.
  assert (hstart : encodeBase (Core MB0 l (R0 4 :: R02 0 :: M2R k :: rRest)) =
                   evalWin (eL l) (repBlock vM2 (k + 1) *> eR rRest) B false [S0] pRB).
  { exact (hcfg (eL l) (repBlock vM2 (k + 1) *> eR rRest)). }
  assert (hend : encodeBase (Core MB0 (pushWM2 k l) (R0 4 :: pushR02 0 rRest)) =
                 evalWin (repBlock wM2 (k + 1) *> eL l) (eR rRest) B false [S0] pRB).
  { assert (hrp : forall rs, eR (R0 4 :: pushR02 0 rs) = pRB *> eR rs).
    { intro rs. change (eR (R0 4 :: pushR02 0 rs)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 rs)).
      rewrite eR_pushR02. reflexivity. }
    cbn [encodeBase encodeCore]. rewrite eL_pushWM2, hrp.
    exact (hcfg (repBlock wM2 (k + 1) *> eL l) (eR rRest)). }
  rewrite hstart, hend. exact hw.
Qed.

Lemma ld5Init_sound (k : N) (lRest : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 (LD 5 :: LD1 (k + 4) :: lRest) (R1 5 :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 lRest (R1 9 :: ld5ROut k rRest)).
Proof.
  set (rMid := R1 3 :: R02 0 :: R1 3 :: pushR02 1 rRest).
  assert (hrMid : eR rMid =
    [S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S0] *> eR rRest).
  { unfold rMid.
    change (eR (R1 3 :: R02 0 :: R1 3 :: pushR02 1 rRest)) with
      ([S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0] *> eR (pushR02 1 rRest)).
    rewrite eR_pushR02. reflexivity. }
  assert (hinit : encodeBase (Core MB0 (LD 5 :: LD1 (k + 4) :: lRest) (R1 5 :: rRest)) -[ tm ]->*
                  evalWin (repBlock wLD1 k *> eL lRest) (eR rMid) B false [S0] r1_9Bits).
  { refine (chkWin_eq false false 224%nat B false ld5InitL ld5InitRIn
      B false [S0] ld5InitROut (repBlock wLD1 k *> eL lRest) (eR rRest)
      (@no_false _) (@no_false _) _ _ ld5Init_body).
    - cbn [encodeBase encodeCore eL eR].
      replace (k + 4 + 1) with (5 + k) by lia.
      rewrite (repBlock_add wLD1 5 k), Str_app_assoc, <- evalWin_b0_flip. reflexivity.
    - rewrite hrMid. unfold evalWin, ld5InitROut. rewrite (Str_app_assoc r1_9Bits). reflexivity. }
  assert (hrOut : eR (ld5ROut k rRest) = repBlock wLD1 k *> eR rMid).
  { unfold ld5ROut; fold rMid. destruct (k =? 0) eqn:hk.
    - apply N.eqb_eq in hk; subst; reflexivity.
    - apply N.eqb_neq in hk. rewrite eR_pushR02. replace (k - 1 + 1) with k by lia. reflexivity. }
  assert (hend : evalWin (eL lRest) (repBlock wLD1 k *> eR rMid) B false [S0] r1_9Bits =
                 encodeBase (Core MB0 lRest (R1 9 :: ld5ROut k rRest))).
  { cbn [encodeBase encodeCore].
    change (eR (R1 9 :: ld5ROut k rRest)) with (r1_9Bits *> eR (ld5ROut k rRest)).
    rewrite hrOut. reflexivity. }
  eapply rs_trans; [exact hinit |].
  rewrite <- hend.
  exact (walkWordLeft 34%nat B false [S0] wLD1 r1_9Bits wLD1 ld1Left_body k (eL lRest) (eR rMid)).
Qed.

Lemma r02Right_sound (k : N) (l : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 l (R0 4 :: R02 (k + 1) :: rRest)) -[ tm ]->*
  encodeBase (Core MB0 (r02LOut k l) (R0 4 :: pushR02 0 rRest)).
Proof.
  pose proof (walkWordRight 10%nat B false [S0] [S1; S0; S1; S1] pRB wLD1 r02Right_body
    (k + 1) (eL l) (eR rRest)) as hw.
  assert (hstart : encodeBase (Core MB0 l (R0 4 :: R02 (k + 1) :: rRest)) =
                   evalWin (eL l) (repBlock wLD1 (k + 1) *> eR rRest) B false [S0] pRB).
  { cbn [encodeBase encodeCore eR].
    rewrite (repBlock_succ_left wLD1 (k + 1)), (Str_app_assoc wLD1). reflexivity. }
  assert (hlOut : eL (r02LOut k l) = repBlock [S1; S0; S1; S1] (k + 1) *> eL l).
  { assert (hl2 : eL (bumpL (bumpL l)) = [S1; S1] *> eL l) by (rewrite !eL_bumpL; reflexivity).
    rewrite wR02_pow_eq. unfold r02LOut. destruct (k =? 0) eqn:hk.
    - apply N.eqb_eq in hk; subst. rewrite eL_pushL0, hl2. reflexivity.
    - apply N.eqb_neq in hk. rewrite eL_pushL0, eL_pushLD1, hl2.
      replace (k - 1 + 1) with k by lia. reflexivity. }
  assert (hrp : eR (R0 4 :: pushR02 0 rRest) = pRB *> eR rRest).
  { change (eR (R0 4 :: pushR02 0 rRest)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 rRest)).
    rewrite eR_pushR02. reflexivity. }
  assert (hend : encodeBase (Core MB0 (r02LOut k l) (R0 4 :: pushR02 0 rRest)) =
                 evalWin (repBlock [S1; S0; S1; S1] (k + 1) *> eL l) (eR rRest) B false [S0] pRB).
  { cbn [encodeBase encodeCore]. rewrite hlOut, hrp. reflexivity. }
  rewrite hstart, hend. exact hw.
Qed.

Lemma stepMotifB0_sound (l : list LTok) (r : list RTok) (bs' : BaseState)
  (hm : stepMotifB0 l r = Some bs') :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase bs'.
Proof.
  unfold stepMotifB0 in hm.
  destruct (popR0Eq 4 r) as [rAfter4 |] eqn:hr4.
  - destruct (popR02 rAfter4) as [[kr r2] |] eqn:hr02; [| discriminate].
    rewrite (popR0Eq_some hr4), (popR02_some hr02).
    destruct (kr =? 0) eqn:hkr0.
    + apply N.eqb_eq in hkr0; subst kr.
      destruct (popMR11 r2) as [[k r3] |] eqn:hmr.
      * rewrite (popMR11_some hmr).
        destruct (matchCapTail r3) eqn:hcap.
        -- destruct (popLDEq 3 l) as [lRest |] eqn:hl3; inversion hm; subst.
           ++ rewrite (popLDEq_some hl3), (matchCapTail_true hcap).
              exact (capRoundtrip_sound k lRest).
           ++ exact (motifB_sound k l r3).
        -- inversion hm; subst. exact (motifB_sound k l r3).
      * destruct (popM2R r2) as [[k2 r3'] |] eqn:hm2r; [| discriminate].
        inversion hm; subst. rewrite (popM2R_some hm2r). exact (motif2B_sound k2 l r3').
    + apply N.eqb_neq in hkr0. inversion hm; subst.
      replace kr with ((kr - 1) + 1) at 1 by lia.
      exact (r02Right_sound (kr - 1) l r2).
  - destruct (popR0Eq 9 r) as [rAfter9 |] eqn:hr9.
    + destruct (popR1Eq 0 rAfter9) as [rRest |] eqn:hr10; [| discriminate].
      destruct (popLDEq 7 l) as [l1 |] eqn:hl7; [| discriminate].
      rewrite (popR0Eq_some hr9), (popR1Eq_some hr10), (popLDEq_some hl7).
      destruct (popML8 l1) as [[k lRest] |] eqn:hml.
      * inversion hm; subst. rewrite (popML8_some hml). exact (motifA_sound k lRest rRest).
      * destruct (matchU1 l1) as [lRestU |] eqn:hu1; [| discriminate].
        inversion hm; subst.
        assert (henc : encodeBase (Core MB0 (LD 7 :: l1) (R0 9 :: R1 0 :: rRest)) =
                       encodeBase (Core MB0 (LD 7 :: ML8 0 :: lRestU) (R0 9 :: R1 0 :: rRest))).
        { apply encodeBase_core_congr; [| reflexivity].
          change (eL (LD 7 :: l1)) with (ld7Bits *> eL l1).
          rewrite (matchU1_some hu1). reflexivity. }
        rewrite henc. exact (motifA_sound 0 lRestU rRest).
    + destruct (popR1Eq 9 r) as [rRest |] eqn:hr19.
      * rewrite (popR1Eq_some hr19).
        destruct (popLD1 l) as [[k lRest] |] eqn:hld1.
        -- inversion hm; subst. rewrite (popLD1_some hld1). exact (ld1Left_sound k lRest rRest).
        -- destruct (popLDEq 5 l) as [l1 |] eqn:hl5; [| discriminate].
           rewrite (popLDEq_some hl5).
           destruct (popM2L l1) as [[k2 lRest2] |] eqn:hm2.
           ++ inversion hm; subst. rewrite (popM2L_some hm2). exact (motif2A_sound k2 lRest2 rRest).
           ++ destruct (matchU2 l1) as [lRestU |] eqn:hu2; [| discriminate].
              inversion hm; subst.
              assert (henc : encodeBase (Core MB0 (LD 5 :: l1) (R1 9 :: rRest)) =
                             encodeBase (Core MB0 (LD 5 :: M2L 0 :: lRestU) (R1 9 :: rRest))).
              { apply encodeBase_core_congr; [| reflexivity].
                change (eL (LD 5 :: l1)) with (ld5Bits *> eL l1).
                rewrite (matchU2_some hu2). reflexivity. }
              rewrite henc. exact (motif2A_sound 0 lRestU rRest).
      * destruct (popR1Eq 5 r) as [rRest5 |] eqn:hr15; [| discriminate].
        destruct (popLDEq 5 l) as [l1 |] eqn:hl5; [| discriminate].
        destruct (popLD1Ge4 l1) as [[k lRest] |] eqn:hld4; [| discriminate].
        inversion hm; subst.
        rewrite (popR1Eq_some hr15), (popLDEq_some hl5), (popLD1Ge4_some hld4).
        exact (ld5Init_sound k lRest rRest5).
Qed.

Lemma stepCoreRaw_sound_B0 (l : list LTok) (r : list RTok) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (stepCoreRaw MB0 l r).
Proof.
  unfold stepCoreRaw.
  destruct (stepMotifB0 l r) as [bs' |] eqn:hm.
  - exact (stepMotifB0_sound l r bs' hm).
  - exact (stepB0Base_sound l r).
Qed.

(* ========================================================================= *)
(* Section 7: Symbolic Stack Engine (SymLTok, SymRTok, symStepA, symStepB)   *)
(* ========================================================================= *)

Definition opt_map {T U : Type} (f : T -> U) (x : option T) : option U :=
  match x with
  | Some a => Some (f a)
  | None => None
  end.

Lemma b0EvenGe2_preDL_sound (isR1 : bool) (dp q' : N)
  (hrem : dp mod 2 <> 1) (hq : dp / 2 = q' + 2)
  (l : list LTok) (rRest : list RTok) :
  encodeBase (Core MB0 l ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: rRest)) -[ tm ]->*
  encodeBase (Core MDL (pushZeros q' (bumpL (bumpL l)))
    (R1 0 :: (if isR1 then pushR0 2 rRest else addR 2 rRest))).
Proof.
  set (r := (if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: rRest).
  set (rTail := if isR1 then [S0] *> eR rRest else eR rRest).
  assert (heR_start : eR r = [S1] *> (repBlock [S1] (dp + 1) *> ([S0] *> rTail))).
  { unfold r, rTail. destruct isR1; cbn [eR];
      replace (dp + 1 + 1) with ((dp + 1) + 1) by lia;
      rewrite (repBlock_succ_left [S1] (dp + 1)), Str_app_assoc; reflexivity. }
  set (l2 := bumpL (bumpL l)).
  assert (hinit : encodeBase (Core MB0 l r) -[ tm ]->*
                  evalWin (eL l2) (repBlock [S1] (dp + 1) *> ([S0] *> rTail)) A true [] []).
  { refine (chkWin_eq false false 2%nat B true [] [S0; S1] A true [S1; S1] []
      (eL l) (repBlock [S1] (dp + 1) *> ([S0] *> rTail))
      (@no_false _) (@no_false _) _ _ eq_refl).
    - cbn [encodeBase encodeCore]. rewrite heR_start. reflexivity.
    - unfold l2. rewrite !eL_bumpL. reflexivity. }
  set (rNew := if isR1 then pushR0 2 rRest else addR 2 rRest).
  assert (hrNew : eR rNew = [S1; S1; S1] *> rTail).
  { unfold rNew, rTail. destruct isR1.
    - rewrite eR_pushR0. reflexivity.
    - rewrite (eR_addR 2 rRest). reflexivity. }
  assert (hdp : dp + 1 = 2 * (q' + 2) + 1) by lia.
  assert (hpow : repBlock [S1] (dp + 1) *> ([S0] *> rTail) =
                 repBlock [S1; S1] (q' + 2) *> ([S1; S0] *> rTail)).
  { rewrite hdp, repBlock_add, pow_one_even, Str_app_assoc. reflexivity. }
  rewrite hpow in hinit.
  pose proof (walkWordRight 2%nat A true [] wL0 [] [S1; S1] eq_refl (q' + 2) (eL l2) ([S1; S0] *> rTail)) as hw.
  pose proof (rs_trans hinit hw) as h2q.
  assert (h7 : evalWin (repBlock wL0 (q' + 2) *> eL l2) ([S1; S0] *> rTail) A true [] [] -[ tm ]->*
               encodeBase (Core MDL (pushZeros q' l2) (R1 0 :: rNew))).
  { refine (chkWin_eq false false 7%nat A true [S1; S0; S1; S0] [S1; S0] D false [] [S1; S0; S0; S1; S1; S1]
      (repBlock wL0 q' *> eL l2) rTail (@no_false _) (@no_false _) _ _ eq_refl).
    - replace (q' + 2) with (2 + q') by lia.
      rewrite (repBlock_add wL0 2 q'), Str_app_assoc. reflexivity.
    - cbn [encodeBase encodeCore eR]. rewrite (eL_pushZeros q' l2), hrNew. reflexivity. }
  exact (rs_trans h2q h7).
Qed.

Inductive SymLTok :=
| SLC (t : LTok)
| SM2 (d : N)
| SM3 (d : N)
| SM4 (d : N)
| SM3P (d : N)
| SM4P (d : N).

Inductive SymRTok :=
| SRC (t : RTok)
| SMR (d : N)
| SM2R (d : N).

Fixpoint evalSymL (v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) : list LTok :=
  match sl with
  | [] => rest
  | SLC t :: tl => t :: evalSymL v2 v3 v4 tl rest
  | SM2 d :: tl => M2L (v2 + d) :: evalSymL v2 v3 v4 tl rest
  | SM3 d :: tl => M3L (v3 + d) :: evalSymL v2 v3 v4 tl rest
  | SM4 d :: tl => M4L (v4 + d) :: evalSymL v2 v3 v4 tl rest
  | SM3P d :: tl => pushM3L d (evalSymL v2 v3 v4 tl rest)
  | SM4P d :: tl => pushM4L d (evalSymL v2 v3 v4 tl rest)
  end.

Fixpoint evalSymR (vr v2 : N) (sr : list SymRTok) : list RTok :=
  match sr with
  | [] => []
  | SRC t :: tl => t :: evalSymR vr v2 tl
  | SMR d :: tl => MR11 (vr + d) :: evalSymR vr v2 tl
  | SM2R d :: tl => M2R (v2 + d) :: evalSymR vr v2 tl
  end.

Definition SymReached (m : Mode) (sl : list SymLTok) (sr : list SymRTok)
  (m' : Mode) (sl' : list SymLTok) (sr' : list SymRTok) : Prop :=
  forall (vr v2 v3 v4 : N) (rest : list LTok),
    encodeBase (Core m (evalSymL v2 v3 v4 sl rest) (evalSymR vr v2 sr)) -[ tm ]->*
    encodeBase (Core m' (evalSymL v2 v3 v4 sl' rest) (evalSymR vr v2 sr')).

Lemma symReached_refl (m : Mode) (sl : list SymLTok) (sr : list SymRTok) :
  SymReached m sl sr m sl sr.
Proof. intros vr v2 v3 v4 rest; apply rs_refl. Qed.

Lemma symReached_trans
  {m0 m1 m2 : Mode} {sl0 sl1 sl2 : list SymLTok} {sr0 sr1 sr2 : list SymRTok}
  (h1 : SymReached m0 sl0 sr0 m1 sl1 sr1)
  (h2 : SymReached m1 sl1 sr1 m2 sl2 sr2) :
  SymReached m0 sl0 sr0 m2 sl2 sr2.
Proof.
  intros vr v2 v3 v4 rest.
  exact (rs_trans (h1 vr v2 v3 v4 rest) (h2 vr v2 v3 v4 rest)).
Qed.

Definition beqMode (a b : Mode) : bool :=
  match a, b with
  | MB0, MB0 => true
  | MDL, MDL => true
  | _, _ => false
  end.

Definition beqSymLTok (x y : SymLTok) : bool :=
  match x, y with
  | SLC a, SLC b => beqLTok a b
  | SM2 a, SM2 b => a =? b
  | SM3 a, SM3 b => a =? b
  | SM4 a, SM4 b => a =? b
  | SM3P a, SM3P b => a =? b
  | SM4P a, SM4P b => a =? b
  | _, _ => false
  end.

Definition beqSymRTok (x y : SymRTok) : bool :=
  match x, y with
  | SRC a, SRC b => beqRTok a b
  | SMR a, SMR b => a =? b
  | SM2R a, SM2R b => a =? b
  | _, _ => false
  end.

Fixpoint beqSymLList (xs ys : list SymLTok) : bool :=
  match xs, ys with
  | [], [] => true
  | a :: as_, b :: bs => beqSymLTok a b && beqSymLList as_ bs
  | _, _ => false
  end.

Fixpoint beqSymRList (xs ys : list SymRTok) : bool :=
  match xs, ys with
  | [], [] => true
  | a :: as_, b :: bs => beqSymRTok a b && beqSymRList as_ bs
  | _, _ => false
  end.

Fixpoint stripSymLC (pfx : list LTok) (sl : list SymLTok) : option (list SymLTok) :=
  match pfx, sl with
  | [], _ => Some sl
  | p :: ps, SLC x :: xs => if beqLTok p x then stripSymLC ps xs else None
  | _ :: _, _ => None
  end.

Fixpoint stripSymRC (pfx : list RTok) (sr : list SymRTok) : option (list SymRTok) :=
  match pfx, sr with
  | [], _ => Some sr
  | p :: ps, SRC x :: xs => if beqRTok p x then stripSymRC ps xs else None
  | _ :: _, _ => None
  end.

Lemma eq_of_beqMode {a b : Mode} (h : beqMode a b = true) : a = b.
Proof. destruct a, b; try discriminate; reflexivity. Qed.

Lemma eq_of_beqSymLTok {a b : SymLTok} (h : beqSymLTok a b = true) : a = b.
Proof.
  destruct a, b; try discriminate; cbn in h;
    [f_equal; exact (eq_of_beqLTok h) |
     apply N.eqb_eq in h; subst; reflexivity |
     apply N.eqb_eq in h; subst; reflexivity |
     apply N.eqb_eq in h; subst; reflexivity |
     apply N.eqb_eq in h; subst; reflexivity |
     apply N.eqb_eq in h; subst; reflexivity].
Qed.

Lemma eq_of_beqSymRTok {a b : SymRTok} (h : beqSymRTok a b = true) : a = b.
Proof.
  destruct a, b; try discriminate; cbn in h;
    [f_equal; exact (eq_of_beqRTok h) |
     apply N.eqb_eq in h; subst; reflexivity |
     apply N.eqb_eq in h; subst; reflexivity].
Qed.

Lemma eq_of_beqSymLList : forall a b, beqSymLList a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] h; try discriminate.
  - reflexivity.
  - cbn in h. apply andb_prop in h. destruct h as [hx hxs].
    rewrite (eq_of_beqSymLTok hx), (IH ys hxs). reflexivity.
Qed.

Lemma eq_of_beqSymRList : forall a b, beqSymRList a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] h; try discriminate.
  - reflexivity.
  - cbn in h. apply andb_prop in h. destruct h as [hx hxs].
    rewrite (eq_of_beqSymRTok hx), (IH ys hxs). reflexivity.
Qed.

Lemma stripSymLC_some :
  forall pfx sl rest, stripSymLC pfx sl = Some rest -> sl = map SLC pfx ++ rest.
Proof.
  induction pfx as [| p ps IH].
  - intros sl rest h; inversion h; reflexivity.
  - intros [| [t | ? | ? | ? | ? | ?] xs] rest h; try discriminate.
    cbn [stripSymLC] in h. destruct (beqLTok p t) eqn:hb; [| discriminate].
    rewrite <- (eq_of_beqLTok hb), (IH xs rest h). reflexivity.
Qed.

Lemma stripSymRC_some :
  forall pfx sr rest, stripSymRC pfx sr = Some rest -> sr = map SRC pfx ++ rest.
Proof.
  induction pfx as [| p ps IH].
  - intros sr rest h; inversion h; reflexivity.
  - intros [| [t | ? | ?] xs] rest h; try discriminate.
    cbn [stripSymRC] in h. destruct (beqRTok p t) eqn:hb; [| discriminate].
    rewrite <- (eq_of_beqRTok hb), (IH xs rest h). reflexivity.
Qed.

Lemma evalSymL_map_c :
  forall pfx sl v2 v3 v4 rest,
    evalSymL v2 v3 v4 (map SLC pfx ++ sl) rest = pfx ++ evalSymL v2 v3 v4 sl rest.
Proof.
  induction pfx as [| t ts IH]; intros sl v2 v3 v4 rest; [reflexivity |].
  cbn [map app evalSymL]. rewrite (IH sl v2 v3 v4 rest). reflexivity.
Qed.

Lemma evalSymL_map_c_nil (pfx : list LTok) (v2 v3 v4 : N) (rest : list LTok) :
  evalSymL v2 v3 v4 (map SLC pfx) rest = pfx ++ rest.
Proof.
  pose proof (evalSymL_map_c pfx [] v2 v3 v4 rest) as h.
  rewrite app_nil_r in h. exact h.
Qed.

Lemma evalSymR_map_c :
  forall pfx sr vr v2,
    evalSymR vr v2 (map SRC pfx ++ sr) = pfx ++ evalSymR vr v2 sr.
Proof.
  induction pfx as [| t ts IH]; intros sr vr v2; [reflexivity |].
  cbn [map app evalSymR]. rewrite (IH sr vr v2). reflexivity.
Qed.

Definition w3TopL : list LTok :=
  [LD 2; L0 1; LD 5; LD1 0; L0 2; LD1 0; L0 0; LD 5; LD 3; L0 3;
   LD1 0; L0 0; LD1 0; LD 7; LD 7].
Definition u1TopL : list LTok := [LD 3; LD1 1; LD 5; L0 1; LD 5; LD 5; LD 7].
Definition u2TopL : list LTok := [LD 7; LD 3; LD1 12; LD 5].
Definition wm4Pfx5L : list LTok := [L0 3; LD 3; L0 0; LD 3; L0 0].

Definition luTailSym : list SymLTok :=
  [SLC (LD1 1); SLC (LD 5); SLC (L0 1); SLC (LD 5); SLC (LD 5); SLC (LD 7)].
Definition lu2TailSym : list SymLTok :=
  [SLC (LD 3); SLC (LD1 12); SLC (LD 5)].
Definition lw3TailSym : list SymLTok :=
  [SLC (LD1 0); SLC (L0 2); SLC (LD1 0); SLC (L0 0); SLC (LD 5); SLC (LD 3); SLC (L0 3);
   SLC (LD1 0); SLC (L0 0); SLC (LD1 0); SLC (LD 7); SLC (LD 7)].
Definition lw4TailSym : list SymLTok :=
  [SLC (LD 3); SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0)].
Definition ruTailSym : list SymRTok :=
  [SRC (R1 3); SRC (R02 1); SRC (R1 3); SRC (R1 3); SRC (R02 3); SRC (R1 3)].
Definition ru2TailSym : list SymRTok :=
  [SRC (R02 6); SRC (R1 3); SRC (R02 0); SRC (R1 3); SRC (R02 6)].

Definition sPushM3L (k : N) (sl : list SymLTok) : list SymLTok :=
  match sl with
  | SLC (M3L m) :: tl => SLC (M3L (k + 1 + m)) :: tl
  | SM3 d :: tl => SM3 (d + k + 1) :: tl
  | SM3P d :: tl => SM3P (k + 1 + d) :: tl
  | SLC t :: tl => SLC (M3L k) :: SLC t :: tl
  | _ => SM3P k :: sl
  end.

Definition sPushM4L (k : N) (sl : list SymLTok) : list SymLTok :=
  match sl with
  | SLC (M4L m) :: tl => SLC (M4L (k + 1 + m)) :: tl
  | SM4 d :: tl => SM4 (d + k + 1) :: tl
  | SM4P d :: tl => SM4P (k + 1 + d) :: tl
  | SLC t :: tl => SLC (M4L k) :: SLC t :: tl
  | _ => SM4P k :: sl
  end.

Definition sPushLD1 (k : N) (sl : list SymLTok) : list SymLTok :=
  match sl with
  | SLC (LD1 m) :: tl => SLC (LD1 (k + 1 + m)) :: tl
  | _ => SLC (LD1 k) :: sl
  end.

Definition sPushLD (v : N) (sl : list SymLTok) : list SymLTok :=
  if v =? 1 then sPushLD1 0 sl else SLC (LD v) :: sl.

Definition sPeelLD1 (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else SLC (LD1 (k - 1)) :: sl.

Definition sPeelML8 (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else SLC (ML8 (k - 1)) :: sl.

Definition sPeelM2L (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else SLC (M2L (k - 1)) :: sl.

Definition sPeelM3L (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else SLC (M3L (k - 1)) :: sl.

Definition sPeelM4L (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else SLC (M4L (k - 1)) :: sl.

Definition sFoldWM4 (sl : list SymLTok) : list SymLTok :=
  match stripSymLC wm4Pfx5L sl with
  | Some (SLC (LD1 rem) :: rest) => sPushM4L 0 (sPeelLD1 rem rest)
  | _ => sl
  end.

Definition sPeelL0 (k : N) (sl : list SymLTok) : list SymLTok :=
  if k =? 0 then sl else sFoldWM4 (SLC (L0 (k - 1)) :: sl).

Definition sUnconsL (sl : list SymLTok) : option (LHead * list SymLTok) :=
  match sl with
  | SLC (L0 k) :: tl => Some (LHL0 k, tl)
  | SLC (LD v) :: tl => Some (LHLD v, tl)
  | SLC (LD1 k) :: tl => Some (LHLD 1, sPeelLD1 k tl)
  | SLC (ML8 k) :: tl => Some (LHLD 3, luTailSym ++ sPeelML8 k tl)
  | SLC (M2L k) :: tl => Some (LHLD 7, lu2TailSym ++ sPeelM2L k tl)
  | SLC (M3L k) :: tl => Some (LHLD 5, lw3TailSym ++ sPeelM3L k tl)
  | SLC (M4L k) :: tl => Some (LHL0 3, lw4TailSym ++ sPeelM4L k tl)
  | SM2 d :: tl => if d =? 0 then None else Some (LHLD 7, lu2TailSym ++ (SM2 (d - 1) :: tl))
  | SM3 d :: tl => if d =? 0 then None else Some (LHLD 5, lw3TailSym ++ (SM3 (d - 1) :: tl))
  | SM4 d :: tl => if d =? 0 then None else Some (LHL0 3, lw4TailSym ++ (SM4 (d - 1) :: tl))
  | SM4P d :: tl => if d =? 0 then None else Some (LHL0 3, lw4TailSym ++ (SM4P (d - 1) :: tl))
  | _ => None
  end.

Definition sPushL0 (k : N) (sl : list SymLTok) : list SymLTok :=
  match sUnconsL sl with
  | Some (LHL0 m, rest) => sFoldWM4 (SLC (L0 (k + 1 + m)) :: rest)
  | _ => sFoldWM4 (SLC (L0 k) :: sl)
  end.

Definition sPushZeros (q : N) (sl : list SymLTok) : list SymLTok :=
  if q =? 0 then sl else sPushL0 (q - 1) sl.

Definition sBumpL (sl : list SymLTok) : option (list SymLTok) :=
  match sUnconsL sl with
  | None => None
  | Some (LHL0 v, rest) => Some (sPushLD 0 (sPeelL0 v rest))
  | Some (LHLD v, rest) => Some (sPushLD (v + 1) rest)
  end.

Fixpoint sBumpLN (n : nat) (sl : list SymLTok) : option (list SymLTok) :=
  match n with
  | O => Some sl
  | S n' => opt_bind (sBumpL sl) (sBumpLN n')
  end.

Definition sPushM2LRaw_conc (k : N) (sl : list SymLTok) : list SymLTok :=
  match sl with
  | SLC (M2L m) :: tl => SLC (M2L (k + 1 + m)) :: tl
  | SM2 d :: tl => SM2 (k + 1 + d) :: tl
  | _ => SLC (M2L k) :: sl
  end.

Definition sPushM2LRaw_sym (d : N) (sl : list SymLTok) : option (list SymLTok) :=
  match sl with
  | SLC (M2L m) :: tl => Some (SM2 (d + 1 + m) :: tl)
  | SM2 _ :: _ => None
  | _ => Some (SM2 d :: sl)
  end.

Definition sPushM2L_conc (k : N) (sl : list SymLTok) : list SymLTok :=
  match stripSymLC u2TopL sl with
  | Some rest => sPushM2LRaw_conc (k + 1) rest
  | None => sPushM2LRaw_conc k sl
  end.

Definition sPushM2L_sym (d : N) (sl : list SymLTok) : option (list SymLTok) :=
  match stripSymLC u2TopL sl with
  | Some rest => sPushM2LRaw_sym (d + 1) rest
  | None => sPushM2LRaw_sym d sl
  end.

Definition sPushML8 (k : N) (sl : list SymLTok) : list SymLTok :=
  match sl with
  | SLC (ML8 m) :: tl => SLC (ML8 (k + 1 + m)) :: tl
  | _ => SLC (ML8 k) :: sl
  end.

Definition sPushWM1_conc (k : N) (sl : list SymLTok) : option (list SymLTok) :=
  match sBumpLN 4%nat sl with
  | None => None
  | Some l4 =>
    let lMid := [SLC (LD 3); SLC (LD1 1); SLC (LD 5); SLC (L0 1); SLC (LD 5); SLC (LD 5)] ++ l4 in
    if k =? 0 then Some (SLC (LD 3) :: lMid)
    else Some (SLC (LD 3) :: sPushML8 (k - 1) lMid)
  end.

Definition sPushWM2_conc (k : N) (sl : list SymLTok) : option (list SymLTok) :=
  match sBumpLN 2%nat sl with
  | None => None
  | Some l2 =>
    let lMid := SLC (LD 7) :: SLC (LD 3) :: sPushLD1 5 l2 in
    let lBody := if k =? 0 then lMid else sPushM2L_conc (k - 1) lMid in
    Some (SLC (L0 0) :: SLC (LD1 5) :: SLC (LD 5) :: lBody)
  end.

Definition sPushWM2_sym (d : N) (sl : list SymLTok) : option (list SymLTok) :=
  match sBumpLN 2%nat sl with
  | None => None
  | Some l2 =>
    let lMid := SLC (LD 7) :: SLC (LD 3) :: sPushLD1 5 l2 in
    let lBodyOpt :=
      if d =? 0 then
        match stripSymLC u2TopL lMid with
        | Some mRest => sPushM2LRaw_sym 0 mRest
        | None => None
        end
      else sPushM2L_sym (d - 1) lMid in
    match lBodyOpt with
    | None => None
    | Some lBody => Some (SLC (L0 0) :: SLC (LD1 5) :: SLC (LD 5) :: lBody)
    end
  end.

Definition sPeelR02 (k : N) (sr : list SymRTok) : list SymRTok :=
  if k =? 0 then sr else SRC (R02 (k - 1)) :: sr.

Definition sPeelMR11 (k : N) (sr : list SymRTok) : list SymRTok :=
  if k =? 0 then sr else SRC (MR11 (k - 1)) :: sr.

Definition sPeelM2R (k : N) (sr : list SymRTok) : list SymRTok :=
  if k =? 0 then sr else SRC (M2R (k - 1)) :: sr.

Definition sPushR02 (k : N) (sr : list SymRTok) : list SymRTok :=
  match sr with
  | SRC (R02 m) :: tl => SRC (R02 (k + 1 + m)) :: tl
  | _ => SRC (R02 k) :: sr
  end.

Definition sPushR0 (d : N) (sr : list SymRTok) : list SymRTok :=
  if d =? 2 then sPushR02 0 sr else SRC (R0 d) :: sr.

Definition sPushMR11_conc (k : N) (sr : list SymRTok) : list SymRTok :=
  match sr with
  | SRC (MR11 m) :: tl => SRC (MR11 (k + 1 + m)) :: tl
  | SMR d :: tl => SMR (k + 1 + d) :: tl
  | _ => SRC (MR11 k) :: sr
  end.

Definition sPushM2R_conc (k : N) (sr : list SymRTok) : list SymRTok :=
  match sr with
  | SRC (M2R m) :: tl => SRC (M2R (k + 1 + m)) :: tl
  | SM2R d :: tl => SM2R (k + 1 + d) :: tl
  | _ => SRC (M2R k) :: sr
  end.

Definition sPushM2R_sym (d : N) (sr : list SymRTok) : option (list SymRTok) :=
  match sr with
  | SRC (M2R m) :: tl => Some (SM2R (d + 1 + m) :: tl)
  | SM2R _ :: _ => None
  | _ => Some (SM2R d :: sr)
  end.

Definition sUnconsR (sr : list SymRTok) : option (option (RHead * list SymRTok)) :=
  match sr with
  | [] => Some None
  | SRC (R0 d) :: tl => Some (Some (RHR0 d, tl))
  | SRC (R1 d) :: tl => Some (Some (RHR1 d, tl))
  | SRC (R02 k) :: tl => Some (Some (RHR0 2, sPeelR02 k tl))
  | SRC (MR11 k) :: tl => Some (Some (RHR0 2, ruTailSym ++ sPeelMR11 k tl))
  | SRC (M2R k) :: tl => Some (Some (RHR0 2, ru2TailSym ++ sPeelM2R k tl))
  | SMR d :: tl => if d =? 0 then None else Some (Some (RHR0 2, ruTailSym ++ (SMR (d - 1) :: tl)))
  | _ => None
  end.

Definition sAddR (m : N) (sr : list SymRTok) : option (list SymRTok) :=
  match sUnconsR sr with
  | None => None
  | Some None => Some (sPushR0 m [])
  | Some (Some (RHR0 d, rest)) => Some (sPushR0 (d + m + 1) rest)
  | Some (Some (RHR1 d, rest)) => Some (SRC (R1 (d + m + 1)) :: rest)
  end.

Definition sNormB0W3 (m : Mode) (sl : list SymLTok) (sr : list SymRTok) : list SymLTok :=
  match m with
  | MDL => sl
  | MB0 =>
    match stripSymRC [R0 4] sr with
    | Some (SMR _ :: _) =>
      match stripSymLC w3TopL sl with
      | Some rest => SLC (LD 2) :: SLC (L0 1) :: sPushM3L 0 rest
      | None => sl
      end
    | Some (SRC (MR11 _) :: _) =>
      match stripSymLC w3TopL sl with
      | Some rest => SLC (LD 2) :: SLC (L0 1) :: sPushM3L 0 rest
      | None => sl
      end
    | _ => sl
    end
  end.

(* ========================================================================= *)
(* Section 8: Soundness of Symbolic Stack Operations                         *)
(* ========================================================================= *)

Lemma eL_sPushM3L (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushM3L k sl) rest) =
  repBlock wM3 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| hd tl]; [exact (eL_pushM3L k rest) |].
  destruct hd as [t | d | d | d | d | d].
  - destruct t as [? | ? | ? | ? | ? | m | ?]; try reflexivity.
    cbn [sPushM3L evalSymL eL].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - exact (eL_pushM3L k _).
  - cbn [sPushM3L evalSymL eL].
    replace (v3 + (d + k + 1) + 1) with ((k + 1) + (v3 + d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - exact (eL_pushM3L k _).
  - cbn [sPushM3L evalSymL]. rewrite <- (pushM3L_pushM3L k d), eL_pushM3L. reflexivity.
  - exact (eL_pushM3L k _).
Qed.

Lemma eL_sPushM4L (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushM4L k sl) rest) =
  repBlock wM4 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| hd tl]; [exact (eL_pushM4L k rest) |].
  destruct hd as [t | d | d | d | d | d].
  - destruct t as [? | ? | ? | ? | ? | ? | m]; try reflexivity.
    cbn [sPushM4L evalSymL eL].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - exact (eL_pushM4L k _).
  - exact (eL_pushM4L k _).
  - cbn [sPushM4L evalSymL eL].
    replace (v4 + (d + k + 1) + 1) with ((k + 1) + (v4 + d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - exact (eL_pushM4L k _).
  - cbn [sPushM4L evalSymL]. rewrite <- (pushM4L_pushM4L k d), eL_pushM4L. reflexivity.
Qed.

Lemma eL_sPushLD1 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushLD1 k sl) rest) =
  repBlock wLD1 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try reflexivity.
  destruct t as [? | ? | m | ? | ? | ? | ?]; try reflexivity.
  cbn [sPushLD1 evalSymL eL].
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_sPushLD (v v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushLD v sl) rest) =
  eL (LD v :: evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushLD. destruct (v =? 1) eqn:hv.
  - apply N.eqb_eq in hv; subst. rewrite eL_sPushLD1. reflexivity.
  - reflexivity.
Qed.

Lemma eL_sPeelLD1 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPeelLD1 k sl) rest) =
  repBlock wLD1 k *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPeelLD1. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymL eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPeelML8 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPeelML8 k sl) rest) =
  repBlock uM k *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPeelML8. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymL eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPeelM2L (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPeelM2L k sl) rest) =
  repBlock uM2 k *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPeelM2L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymL eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPeelM3L (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPeelM3L k sl) rest) =
  repBlock wM3 k *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPeelM3L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymL eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPeelM4L (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPeelM4L k sl) rest) =
  repBlock wM4 k *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPeelM4L. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymL eL]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sFoldWM4 (v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sFoldWM4 sl) rest) = eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sFoldWM4.
  destruct (stripSymLC wm4Pfx5L sl) as [[| [t | ? | ? | ? | ? | ?] tl] |] eqn:hs; try reflexivity.
  destruct t as [? | ? | rem | ? | ? | ? | ?]; try reflexivity.
  rewrite (stripSymLC_some wm4Pfx5L sl (SLC (LD1 rem) :: tl) hs), evalSymL_map_c, eL_sPushM4L.
  change (0 + 1) with 1. rewrite repBlock_1.
  cbn [wm4Pfx5L app evalSymL].
  rewrite <- (eL_w4 (evalSymL v2 v3 v4 (sPeelLD1 rem tl) rest)).
  assert (htail : eL (LD1 0 :: evalSymL v2 v3 v4 (sPeelLD1 rem tl) rest) =
                  eL (LD1 rem :: evalSymL v2 v3 v4 tl rest)).
  { change (eL (LD1 0 :: evalSymL v2 v3 v4 (sPeelLD1 rem tl) rest)) with
      (wLD1 *> eL (evalSymL v2 v3 v4 (sPeelLD1 rem tl) rest)).
    rewrite eL_sPeelLD1, <- Str_app_assoc, <- repBlock_succ_left. reflexivity. }
  cbn [eL] in htail |- *. rewrite htail. reflexivity.
Qed.

Lemma eL_sPeelL0 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (L0 k :: evalSymL v2 v3 v4 sl rest) =
  wL0 *> eL (evalSymL v2 v3 v4 (sPeelL0 k sl) rest).
Proof.
  unfold sPeelL0. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. rewrite eL_sFoldWM4.
    cbn [evalSymL eL]. replace k with ((k - 1) + 1) at 1 by lia.
    rewrite repBlock_succ_left, Str_app_assoc. reflexivity.
Qed.

Lemma eL_peelL0_eq_sPeelL0 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (peelL0 k (evalSymL v2 v3 v4 sl rest)) =
  eL (evalSymL v2 v3 v4 (sPeelL0 k sl) rest).
Proof.
  unfold peelL0, sPeelL0. destruct (k =? 0) eqn:hk.
  - reflexivity.
  - rewrite eL_foldWM4, eL_sFoldWM4. reflexivity.
Qed.

Lemma sUnconsL_L0 {sl sl' : list SymLTok} {k : N}
  (h : sUnconsL sl = Some (LHL0 k, sl')) (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl rest) = eL (L0 k :: evalSymL v2 v3 v4 sl' rest).
Proof.
  destruct sl as [| hd tl]; [discriminate |].
  destruct hd as [t | d | d | d | d | d].
  - destruct t as [m | ? | ? | ? | ? | ? | m]; try discriminate; cbn [sUnconsL] in h; inversion h; subst.
    + reflexivity.
    + cbn [lw4TailSym app evalSymL].
      rewrite eL_w4, eL_sPeelM4L, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
  - cbn [sUnconsL] in h. destruct (d =? 0); discriminate.
  - cbn [sUnconsL] in h. destruct (d =? 0); discriminate.
  - cbn [sUnconsL] in h. destruct (d =? 0) eqn:hd0; [discriminate |].
    apply N.eqb_neq in hd0. inversion h; subst.
    cbn [lw4TailSym app evalSymL]. rewrite eL_w4. cbn [eL].
    replace (v4 + d + 1) with (1 + (v4 + (d - 1) + 1)) by lia.
    rewrite repBlock_add, repBlock_1, Str_app_assoc. reflexivity.
  - discriminate.
  - cbn [sUnconsL] in h. destruct (d =? 0) eqn:hd0; [discriminate |].
    apply N.eqb_neq in hd0. inversion h; subst.
    cbn [lw4TailSym app evalSymL].
    rewrite eL_w4, !eL_pushM4L, <- Str_app_assoc, <- repBlock_succ_left.
    replace (d - 1 + 1 + 1) with (d + 1) by lia. reflexivity.
Qed.

Lemma sUnconsL_LD {sl sl' : list SymLTok} {v : N}
  (h : sUnconsL sl = Some (LHLD v, sl')) (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl rest) = eL (LD v :: evalSymL v2 v3 v4 sl' rest).
Proof.
  destruct sl as [| hd tl]; [discriminate |].
  destruct hd as [t | d | d | d | d | d].
  - destruct t as [? | m | k | k | k | k | ?]; try discriminate; cbn [sUnconsL] in h; inversion h; subst.
    + reflexivity.
    + change (eL (LD 1 :: evalSymL v2 v3 v4 (sPeelLD1 k tl) rest)) with
        (wLD1 *> eL (evalSymL v2 v3 v4 (sPeelLD1 k tl) rest)).
      rewrite eL_sPeelLD1, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
    + cbn [luTailSym app evalSymL].
      rewrite eL_lu, eL_sPeelML8, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
    + cbn [lu2TailSym app evalSymL].
      rewrite eL_u2, eL_sPeelM2L, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
    + cbn [lw3TailSym app evalSymL].
      rewrite eL_w3, eL_sPeelM3L, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
  - cbn [sUnconsL] in h. destruct (d =? 0) eqn:hd0; [discriminate |].
    apply N.eqb_neq in hd0. inversion h; subst.
    cbn [lu2TailSym app evalSymL]. rewrite eL_u2. cbn [eL].
    replace (v2 + d + 1) with (1 + (v2 + (d - 1) + 1)) by lia.
    rewrite repBlock_add, repBlock_1, Str_app_assoc. reflexivity.
  - cbn [sUnconsL] in h. destruct (d =? 0) eqn:hd0; [discriminate |].
    apply N.eqb_neq in hd0. inversion h; subst.
    cbn [lw3TailSym app evalSymL]. rewrite eL_w3. cbn [eL].
    replace (v3 + d + 1) with (1 + (v3 + (d - 1) + 1)) by lia.
    rewrite repBlock_add, repBlock_1, Str_app_assoc. reflexivity.
  - cbn [sUnconsL] in h. destruct (d =? 0); discriminate.
  - discriminate.
  - cbn [sUnconsL] in h. destruct (d =? 0); discriminate.
Qed.

Lemma eL_sPushL0 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushL0 k sl) rest) =
  repBlock wL0 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushL0. destruct (sUnconsL sl) as [[[m | m] rest'] |] eqn:hu.
  - rewrite eL_sFoldWM4, (sUnconsL_L0 hu v2 v3 v4 rest).
    cbn [evalSymL eL].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - rewrite eL_sFoldWM4. reflexivity.
  - rewrite eL_sFoldWM4. reflexivity.
Qed.

Lemma eL_sPushZeros (q v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushZeros q sl) rest) =
  repBlock wL0 q *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushZeros. destruct (q =? 0) eqn:hq.
  - apply N.eqb_eq in hq; subst; reflexivity.
  - apply N.eqb_neq in hq. rewrite eL_sPushL0.
    replace (q - 1 + 1) with q by lia. reflexivity.
Qed.

Lemma eL_sBumpL {sl sl' : list SymLTok} (h : sBumpL sl = Some sl')
  (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) = [S1] *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sBumpL in h. destruct (sUnconsL sl) as [[[v | v] rest'] |] eqn:hu; [| | discriminate].
  - inversion h; subst. rewrite (sUnconsL_L0 hu v2 v3 v4 rest), eL_sPushLD, eL_sPeelL0. reflexivity.
  - inversion h; subst. rewrite (sUnconsL_LD hu v2 v3 v4 rest), eL_sPushLD. cbn [eL].
    replace (v + 1 + 2) with (1 + (v + 2)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_sBumpLN :
  forall (n : nat) {sl sl' : list SymLTok},
    sBumpLN n sl = Some sl' ->
    forall (v2 v3 v4 : N) (rest : list LTok),
      eL (evalSymL v2 v3 v4 sl' rest) =
      repBlock [S1] (N.of_nat n) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  induction n as [| n IH]; intros sl sl' h v2 v3 v4 rest.
  - inversion h; subst. reflexivity.
  - cbn [sBumpLN] in h. destruct (sBumpL sl) as [sl1 |] eqn:hb; [cbn [opt_bind] in h | discriminate].
    rewrite (IH sl1 sl' h v2 v3 v4 rest), (eL_sBumpL hb v2 v3 v4 rest).
    rewrite <- Str_app_assoc, <- repBlock_succ_right.
    replace (N.of_nat n + 1) with (N.of_nat (S n)) by lia. reflexivity.
Qed.

Lemma eL_sPushML8 (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushML8 k sl) rest) =
  repBlock uM (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try reflexivity.
  destruct t as [? | ? | ? | m | ? | ? | ?]; try reflexivity.
  cbn [sPushML8 evalSymL eL].
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_sPushM2LRaw_conc (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushM2LRaw_conc k sl) rest) =
  repBlock uM2 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| [t | d | ? | ? | ? | ?] tl]; try reflexivity.
  - destruct t as [? | ? | ? | ? | m | ? | ?]; try reflexivity.
    cbn [sPushM2LRaw_conc evalSymL eL].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - cbn [sPushM2LRaw_conc evalSymL eL].
    replace (v2 + (k + 1 + d) + 1) with ((k + 1) + (v2 + d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_sPushM2LRaw_sym {d : N} {sl sl' : list SymLTok}
  (h : sPushM2LRaw_sym d sl = Some sl') (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) =
  repBlock uM2 (v2 + d + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl];
    try (inversion h; subst; reflexivity).
  destruct t as [? | ? | ? | ? | m | ? | ?];
    try (inversion h; subst; reflexivity).
  cbn [sPushM2LRaw_sym] in h; inversion h; subst.
  cbn [evalSymL eL].
  replace (v2 + (d + 1 + m) + 1) with ((v2 + d + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eL_sPushM2L_conc (k v2 v3 v4 : N) (sl : list SymLTok) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sPushM2L_conc k sl) rest) =
  repBlock uM2 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushM2L_conc. destruct (stripSymLC u2TopL sl) as [rest' |] eqn:hm.
  - rewrite (eL_sPushM2LRaw_conc (k + 1)), (stripSymLC_some u2TopL sl rest' hm), evalSymL_map_c,
            (repBlock_succ_right uM2 (k + 1)), Str_app_assoc. reflexivity.
  - exact (eL_sPushM2LRaw_conc k v2 v3 v4 sl rest).
Qed.

Lemma eL_sPushM2L_sym {d : N} {sl sl' : list SymLTok}
  (h : sPushM2L_sym d sl = Some sl') (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) =
  repBlock uM2 (v2 + d + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushM2L_sym in h. destruct (stripSymLC u2TopL sl) as [rest' |] eqn:hm.
  - rewrite (eL_sPushM2LRaw_sym h v2 v3 v4 rest), (stripSymLC_some u2TopL sl rest' hm), evalSymL_map_c.
    replace (v2 + (d + 1) + 1) with ((v2 + d + 1) + 1) by lia.
    rewrite (repBlock_succ_right uM2 (v2 + d + 1)), Str_app_assoc. reflexivity.
  - exact (eL_sPushM2LRaw_sym h v2 v3 v4 rest).
Qed.

Lemma eL_sPushWM1_conc {k : N} {sl sl' : list SymLTok}
  (h : sPushWM1_conc k sl = Some sl') (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) = repBlock wM (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushWM1_conc in h.
  destruct (sBumpLN 4%nat sl) as [l4 |] eqn:hb4; [| discriminate].
  remember ([SLC (LD 3); SLC (LD1 1); SLC (LD 5); SLC (L0 1); SLC (LD 5); SLC (LD 5)] ++ l4)
    as lMid eqn:hlMid.
  pose proof (eL_sBumpLN 4%nat hb4 v2 v3 v4 rest) as hl4.
  change (repBlock [S1] (N.of_nat 4)) with ones4 in hl4.
  assert (hmid : eL (evalSymL v2 v3 v4 lMid rest) =
                 mid42 *> (ones4 *> eL (evalSymL v2 v3 v4 sl rest))).
  { subst lMid. cbn [app evalSymL]. rewrite eL_mid42, hl4. reflexivity. }
  rewrite (wM_pow_eq k (eL (evalSymL v2 v3 v4 sl rest))).
  destruct (k =? 0) eqn:hk; injection h as <-.
  - apply N.eqb_eq in hk; subst k.
    cbn [evalSymL]. change (eL (LD 3 :: ?xs)) with (ld3Bits *> eL xs).
    rewrite hmid. reflexivity.
  - apply N.eqb_neq in hk.
    cbn [evalSymL]. change (eL (LD 3 :: ?xs)) with (ld3Bits *> eL xs).
    rewrite eL_sPushML8, hmid.
    replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPushWM2_conc {k : N} {sl sl' : list SymLTok}
  (h : sPushWM2_conc k sl = Some sl') (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) = repBlock wM2 (k + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushWM2_conc in h.
  destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
  remember (SLC (LD 7) :: SLC (LD 3) :: sPushLD1 5 l2) as lMid eqn:hlMid.
  injection h as <-.
  pose proof (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest) as hl2.
  change (repBlock [S1] (N.of_nat 2)) with [S1; S1] in hl2.
  assert (hmid : eL (evalSymL v2 v3 v4 lMid rest) =
                 wM2Mid40 *> ([S1; S1] *> eL (evalSymL v2 v3 v4 sl rest))).
  { subst lMid. cbn [evalSymL].
    change (eL (LD 7 :: LD 3 :: evalSymL v2 v3 v4 (sPushLD1 5 l2) rest)) with
      ((ld7Bits ++ ld3Bits) *> eL (evalSymL v2 v3 v4 (sPushLD1 5 l2) rest)).
    rewrite eL_sPushLD1, hl2. reflexivity. }
  rewrite (wM2_pow_eq k (eL (evalSymL v2 v3 v4 sl rest))).
  destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst k.
    cbn [evalSymL]. change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite hmid. reflexivity.
  - apply N.eqb_neq in hk.
    cbn [evalSymL]. change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite eL_sPushM2L_conc, hmid.
    replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eL_sPushWM2_sym {d : N} {sl sl' : list SymLTok}
  (h : sPushWM2_sym d sl = Some sl') (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 sl' rest) = repBlock wM2 (v2 + d + 1) *> eL (evalSymL v2 v3 v4 sl rest).
Proof.
  unfold sPushWM2_sym in h.
  destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
  set (lMid := SLC (LD 7) :: SLC (LD 3) :: sPushLD1 5 l2) in h |- *.
  pose proof (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest) as hl2.
  change (repBlock [S1] (N.of_nat 2)) with [S1; S1] in hl2.
  assert (hmid : eL (evalSymL v2 v3 v4 lMid rest) =
                 wM2Mid40 *> ([S1; S1] *> eL (evalSymL v2 v3 v4 sl rest))).
  { unfold lMid; cbn [evalSymL].
    change (eL (LD 7 :: LD 3 :: evalSymL v2 v3 v4 (sPushLD1 5 l2) rest)) with
      ((ld7Bits ++ ld3Bits) *> eL (evalSymL v2 v3 v4 (sPushLD1 5 l2) rest)).
    rewrite eL_sPushLD1, hl2. reflexivity. }
  rewrite (wM2_pow_eq (v2 + d) (eL (evalSymL v2 v3 v4 sl rest))).
  destruct (d =? 0) eqn:hd0.
  - apply N.eqb_eq in hd0; subst d.
    destruct (stripSymLC u2TopL lMid) as [mRest |] eqn:hm; [| discriminate].
    destruct (sPushM2LRaw_sym 0 mRest) as [lBody |] eqn:hbody; [| discriminate].
    inversion h; subst.
    assert (hu2 : eL (evalSymL v2 v3 v4 lMid rest) = uM2 *> eL (evalSymL v2 v3 v4 mRest rest)).
    { rewrite (stripSymLC_some u2TopL lMid mRest hm), evalSymL_map_c. reflexivity. }
    cbn [evalSymL]. change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite (eL_sPushM2LRaw_sym hbody v2 v3 v4 rest).
    replace (v2 + 0 + 1) with (v2 + 1) by lia.
    replace (v2 + 0) with v2 by lia.
    rewrite (repBlock_succ_right uM2 v2), Str_app_assoc, <- hu2, hmid. reflexivity.
  - apply N.eqb_neq in hd0.
    destruct (sPushM2L_sym (d - 1) lMid) as [lBody |] eqn:hbody; [| discriminate].
    inversion h; subst.
    cbn [evalSymL]. change (eL (L0 0 :: LD1 5 :: LD 5 :: ?xs)) with (wM2Prefix34 *> eL xs).
    rewrite (eL_sPushM2L_sym hbody v2 v3 v4 rest).
    replace (v2 + (d - 1) + 1) with (v2 + d) by lia.
    rewrite hmid. reflexivity.
Qed.

Lemma eR_sPeelR02 (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPeelR02 k sr)) = repBlock wLD1 k *> eR (evalSymR vr v2 sr).
Proof.
  unfold sPeelR02. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymR eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_sPeelMR11 (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPeelMR11 k sr)) = repBlock vM k *> eR (evalSymR vr v2 sr).
Proof.
  unfold sPeelMR11. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymR eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_sPeelM2R (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPeelM2R k sr)) = repBlock vM2 k *> eR (evalSymR vr v2 sr).
Proof.
  unfold sPeelM2R. destruct (k =? 0) eqn:hk.
  - apply N.eqb_eq in hk; subst; reflexivity.
  - apply N.eqb_neq in hk. cbn [evalSymR eR]. replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

Lemma eR_sPushR02 (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPushR02 k sr)) = repBlock wLD1 (k + 1) *> eR (evalSymR vr v2 sr).
Proof.
  destruct sr as [| [t | ? | ?] tl]; try reflexivity.
  destruct t as [? | ? | m | ? | ?]; try reflexivity.
  cbn [sPushR02 evalSymR eR].
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_sPushR0 (d vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPushR0 d sr)) = eR (R0 d :: evalSymR vr v2 sr).
Proof.
  unfold sPushR0. destruct (d =? 2) eqn:hd.
  - apply N.eqb_eq in hd; subst. rewrite eR_sPushR02. reflexivity.
  - reflexivity.
Qed.

Lemma eR_sPushMR11_conc (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPushMR11_conc k sr)) = repBlock vM (k + 1) *> eR (evalSymR vr v2 sr).
Proof.
  destruct sr as [| [t | d | ?] tl]; try reflexivity.
  - destruct t as [? | ? | ? | m | ?]; try reflexivity.
    cbn [sPushMR11_conc evalSymR eR].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - cbn [sPushMR11_conc evalSymR eR].
    replace (vr + (k + 1 + d) + 1) with ((k + 1) + (vr + d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_sPushM2R_conc (k vr v2 : N) (sr : list SymRTok) :
  eR (evalSymR vr v2 (sPushM2R_conc k sr)) = repBlock vM2 (k + 1) *> eR (evalSymR vr v2 sr).
Proof.
  destruct sr as [| [t | ? | d] tl]; try reflexivity.
  - destruct t as [? | ? | ? | ? | m]; try reflexivity.
    cbn [sPushM2R_conc evalSymR eR].
    replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - cbn [sPushM2R_conc evalSymR eR].
    replace (v2 + (k + 1 + d) + 1) with ((k + 1) + (v2 + d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma eR_sPushM2R_sym {d : N} {sr sr' : list SymRTok}
  (h : sPushM2R_sym d sr = Some sr') (vr v2 : N) :
  eR (evalSymR vr v2 sr') = repBlock vM2 (v2 + d + 1) *> eR (evalSymR vr v2 sr).
Proof.
  destruct sr as [| [t | ? | ?] tl];
    try (inversion h; subst; reflexivity).
  destruct t as [? | ? | ? | ? | m];
    try (inversion h; subst; reflexivity).
  cbn [sPushM2R_sym] in h; inversion h; subst.
  cbn [evalSymR eR].
  replace (v2 + (d + 1 + m) + 1) with ((v2 + d + 1) + (m + 1)) by lia.
  rewrite repBlock_add, Str_app_assoc. reflexivity.
Qed.

Lemma sUnconsR_empty {sr : list SymRTok} (h : sUnconsR sr = Some None) (vr v2 : N) :
  evalSymR vr v2 sr = [].
Proof.
  destruct sr as [| [t | d | ?] tl]; [reflexivity | | | discriminate].
  - destruct t; discriminate.
  - cbn [sUnconsR] in h; destruct (d =? 0); discriminate.
Qed.

Lemma sUnconsR_R0 {sr sr' : list SymRTok} {d : N}
  (h : sUnconsR sr = Some (Some (RHR0 d, sr'))) (vr v2 : N) :
  eR (evalSymR vr v2 sr) = eR (R0 d :: evalSymR vr v2 sr').
Proof.
  destruct sr as [| [t | d' | ?] tl]; try discriminate.
  - destruct t as [m | ? | k | k | k]; try discriminate; cbn [sUnconsR] in h; inversion h; subst.
    + reflexivity.
    + change (eR (R0 2 :: evalSymR vr v2 (sPeelR02 k tl))) with
        (wLD1 *> eR (evalSymR vr v2 (sPeelR02 k tl))).
      rewrite eR_sPeelR02, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
    + cbn [ruTailSym app evalSymR].
      rewrite eR_ru, eR_sPeelMR11, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
    + cbn [ru2TailSym app evalSymR].
      rewrite eR_ru2, eR_sPeelM2R, <- Str_app_assoc, <- repBlock_succ_left. reflexivity.
  - cbn [sUnconsR] in h. destruct (d' =? 0) eqn:hd0; [discriminate |].
    apply N.eqb_neq in hd0. inversion h; subst.
    cbn [ruTailSym app evalSymR]. rewrite eR_ru. cbn [eR].
    rewrite <- (Str_app_assoc vM (repBlock vM (vr + (d' - 1) + 1))),
            <- (repBlock_succ_left vM (vr + (d' - 1) + 1)).
    replace (vr + (d' - 1) + 1 + 1) with (vr + d' + 1) by lia. reflexivity.
Qed.

Lemma sUnconsR_R1 {sr sr' : list SymRTok} {d : N}
  (h : sUnconsR sr = Some (Some (RHR1 d, sr'))) (vr v2 : N) :
  eR (evalSymR vr v2 sr) = eR (R1 d :: evalSymR vr v2 sr').
Proof.
  destruct sr as [| [t | d' | ?] tl]; try discriminate.
  - destruct t as [? | m | ? | ? | ?]; try discriminate.
    cbn [sUnconsR] in h; inversion h; subst; reflexivity.
  - cbn [sUnconsR] in h; destruct (d' =? 0); discriminate.
Qed.

Lemma eR_sAddR {m : N} {sr sr' : list SymRTok} (h : sAddR m sr = Some sr')
  (vr v2 : N) :
  eR (evalSymR vr v2 sr') = repBlock [S1] (m + 1) *> eR (evalSymR vr v2 sr).
Proof.
  unfold sAddR in h. destruct (sUnconsR sr) as [[[[d | d] rest] |] |] eqn:hu; try discriminate.
  - inversion h; subst. rewrite (sUnconsR_R0 hu vr v2), eR_sPushR0. cbn [eR].
    replace (d + m + 1 + 1) with ((m + 1) + (d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - inversion h; subst. rewrite (sUnconsR_R1 hu vr v2). cbn [evalSymR eR].
    replace (d + m + 1 + 1) with ((m + 1) + (d + 1)) by lia.
    rewrite repBlock_add, Str_app_assoc. reflexivity.
  - inversion h; subst. rewrite (sUnconsR_empty hu vr v2), eR_sPushR0.
    cbn [evalSymR eR Str_app]. rewrite zero_cons_def. reflexivity.
Qed.

Lemma eL_sNormB0W3 (m : Mode) (sl : list SymLTok) (sr : list SymRTok)
  (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sNormB0W3 m sl sr) rest) = eL (evalSymL v2 v3 v4 sl rest).
Proof.
  assert (hfold : forall sl0 rest', stripSymLC w3TopL sl0 = Some rest' ->
            eL (evalSymL v2 v3 v4 (SLC (LD 2) :: SLC (L0 1) :: sPushM3L 0 rest') rest) =
            eL (evalSymL v2 v3 v4 sl0 rest)).
  { intros sl0 rest' hm.
    rewrite (stripSymLC_some w3TopL sl0 rest' hm), evalSymL_map_c.
    cbn [w3TopL app evalSymL].
    change (eL (LD 2 :: L0 1 :: evalSymL v2 v3 v4 (sPushM3L 0 rest') rest)) with
      ([S1; S1; S1; S1; S0; S1; S0; S1; S0] *> eL (evalSymL v2 v3 v4 (sPushM3L 0 rest') rest)).
    change (eL (LD 2 :: L0 1 :: ?xs)) with ([S1; S1; S1; S1; S0; S1; S0; S1; S0] *> eL xs).
    rewrite eL_sPushM3L. change (0 + 1) with 1. rewrite repBlock_1, eL_w3. reflexivity. }
  unfold sNormB0W3. destruct m; [| reflexivity].
  destruct (stripSymRC [R0 4] sr) as [[| [t1 | ? | ?] ?] |]; try reflexivity.
  - destruct t1 as [? | ? | ? | ? | ?]; try reflexivity.
    destruct (stripSymLC w3TopL sl) as [rest' |] eqn:hm; [exact (hfold sl rest' hm) | reflexivity].
  - destruct (stripSymLC w3TopL sl) as [rest' |] eqn:hm; [exact (hfold sl rest' hm) | reflexivity].
Qed.

Lemma symReached_norm
  {m0 m1 : Mode} {sl0 sl1 : list SymLTok} {sr0 sr1 : list SymRTok}
  (h : SymReached m0 sl0 sr0 m1 sl1 sr1) :
  SymReached m0 sl0 sr0 m1 (sNormB0W3 m1 sl1 sr1) sr1.
Proof.
  intros vr v2 v3 v4 rest.
  rewrite (encodeBase_core_congr m1 (eL_sNormB0W3 m1 sl1 sr1 v2 v3 v4 rest) eq_refl).
  exact (h vr v2 v3 v4 rest).
Qed.

(* ========================================================================= *)
(* Section 9: Symbolic Stepper symStepA (Layer 1) & Soundness                *)
(* ========================================================================= *)

Definition capTailSym : list SymRTok := [SRC (R02 0); SRC (R1 3); SRC (R02 0)].

Definition sStepDL (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match sUnconsL sl with
  | None => None
  | Some (LHL0 v, rest) =>
    match sBumpL (sPeelL0 v rest), sAddR 0 sr with
    | Some sl', Some sr' => Some (MDL, sl', sr')
    | _, _ => None
    end
  | Some (LHLD v, rest) => Some (MB0, rest, sPushR0 v sr)
  end.

Definition sFoldDL2 (sl1 : list SymLTok) (sr1 : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match sStepDL sl1 sr1 with
  | None => None
  | Some (MDL, sl2, sr2) => sStepDL sl2 sr2
  | Some (MB0, sl2, sr2) => Some (MB0, sl2, sr2)
  end.

Definition sStepB0Pos (isR1 : bool) (dp : N) (sl : list SymLTok) (rRest : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  let q := dp / 2 in
  if dp mod 2 =? 1 then
    match sBumpLN 2%nat sl with
    | None => None
    | Some l2 =>
      if isR1 then
        Some (MB0, SLC (LD 0) :: sPushZeros q l2, rRest)
      else
        match rRest with
        | [] =>
          match sBumpLN 2%nat (sPushZeros (q + 1) l2) with
          | None => None
          | Some l4 => Some (MDL, l4, [SRC (R0 0)])
          end
        | _ :: _ =>
          match sAddR 1 rRest with
          | None => None
          | Some sr' => Some (MB0, sPushZeros q l2, sr')
          end
        end
    end
  else
    let srNewOpt := if isR1 then Some (sPushR0 2 rRest) else sAddR 2 rRest in
    match srNewOpt with
    | None => None
    | Some srNew =>
      if q =? 0 then
        match sUnconsL sl with
        | None => None
        | Some (LHL0 lv, lRest) =>
          match sAddR 1 srNew with
          | None => None
          | Some sr' => Some (MB0, sPeelL0 lv lRest, sr')
          end
        | Some (LHLD lv, lRest) =>
          match sAddR (lv + 2) srNew with
          | None => None
          | Some sr' => Some (MB0, lRest, sr')
          end
        end
      else if q =? 1 then
        match sBumpLN 2%nat sl with
        | None => None
        | Some l2 => Some (MB0, l2, srNew)
        end
      else
        match sBumpLN 2%nat sl with
        | None => None
        | Some l2 => sFoldDL2 (sPushZeros (q - 2) l2) (SRC (R1 0) :: srNew)
        end
    end.

Definition sStepB0Base (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match sUnconsR sr with
  | None => None
  | Some None =>
    match sBumpL sl with
    | None => None
    | Some sl' => Some (MDL, sl', [SRC (R0 0)])
    end
  | Some (Some (RHR0 d, rRest)) =>
    if d =? 0 then
      match rRest with
      | [] =>
        match sBumpLN 4%nat sl with
        | None => None
        | Some sl' => Some (MDL, sl', [SRC (R0 0)])
        end
      | r1 :: rs =>
        match sUnconsL sl with
        | None => None
        | Some (LHL0 lv, lRest) =>
          match sAddR 3 (r1 :: rs) with
          | None => None
          | Some sr' => Some (MB0, sPeelL0 lv lRest, sr')
          end
        | Some (LHLD lv, lRest) =>
          match sAddR (lv + 4) (r1 :: rs) with
          | None => None
          | Some sr' => Some (MB0, lRest, sr')
          end
        end
      end
    else sStepB0Pos false (d - 1) sl rRest
  | Some (Some (RHR1 d, rRest)) =>
    if d =? 0 then
      match sBumpLN 3%nat sl with
      | None => None
      | Some sl' => Some (MB0, sl', rRest)
      end
    else sStepB0Pos true (d - 1) sl rRest
  end.

Definition sPopR02 (sr : list SymRTok) : option (N * list SymRTok) :=
  match sr with
  | SRC (R02 k) :: tl => Some (k, tl)
  | _ => None
  end.

Definition sPopLD1 (sl : list SymLTok) : option (N * list SymLTok) :=
  match sl with
  | SLC (LD1 k) :: tl => Some (k, tl)
  | _ => None
  end.

Definition sPopLD1Ge4 (sl : list SymLTok) : option (N * list SymLTok) :=
  match sl with
  | SLC (LD1 m) :: tl => if 4 <=? m then Some (m - 4, tl) else None
  | _ => None
  end.

Definition sPopML8 (sl : list SymLTok) : option (N * list SymLTok) :=
  match sl with
  | SLC (ML8 k) :: tl => Some (k, tl)
  | _ => None
  end.

Definition sPopM2L (sl : list SymLTok) : option (N * list SymLTok) :=
  match sl with
  | SLC (M2L k) :: tl => Some (k, tl)
  | _ => None
  end.

Definition sPopSymM2 (sl : list SymLTok) : option (N * list SymLTok) :=
  match sl with
  | SM2 d :: tl => Some (d, tl)
  | _ => None
  end.

Definition sLd5ROut (k : N) (rRest : list SymRTok) : list SymRTok :=
  let rMid := SRC (R1 3) :: SRC (R02 0) :: SRC (R1 3) :: sPushR02 1 rRest in
  if k =? 0 then rMid else sPushR02 (k - 1) rMid.

Definition sR02LOut (k : N) (l2 : list SymLTok) : list SymLTok :=
  let lMid := if k =? 0 then l2 else sPushLD1 (k - 1) l2 in
  sPushL0 0 lMid.

Definition sStepMotifR4Zero (sl : list SymLTok) (r2 : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match r2 with
  | SMR d :: r3 =>
    if beqSymRList r3 capTailSym then
      match stripSymLC [LD 3] sl with
      | Some lRest =>
        Some (MB0, SLC (LD 7) :: lRest, SRC (R0 9) :: SRC (R1 0) :: SMR d :: capTailSym)
      | None => None
      end
    else None
  | SRC t :: r3 =>
    match t with
    | MR11 k =>
      if beqSymRList r3 capTailSym then
        match stripSymLC [LD 3] sl with
        | Some lRest =>
          Some (MB0, SLC (LD 7) :: lRest, SRC (R0 9) :: SRC (R1 0) :: SRC (MR11 k) :: capTailSym)
        | None =>
          opt_map (fun p => (MB0, p, SRC (R0 4) :: sPushR02 0 r3)) (sPushWM1_conc k sl)
        end
      else
        opt_map (fun p => (MB0, p, SRC (R0 4) :: sPushR02 0 r3)) (sPushWM1_conc k sl)
    | M2R k =>
      opt_map (fun p => (MB0, p, SRC (R0 4) :: sPushR02 0 r3)) (sPushWM2_conc k sl)
    | _ => None
    end
  | SM2R d :: r3 =>
    opt_map (fun p => (MB0, p, SRC (R0 4) :: sPushR02 0 r3)) (sPushWM2_sym d sl)
  | [] => None
  end.

Definition sMotifR4 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match stripSymRC [R0 4] sr with
  | None => None
  | Some rAfter4 =>
    match sPopR02 rAfter4 with
    | None => None
    | Some (kr, r2) =>
      if kr =? 0 then sStepMotifR4Zero sl r2
      else
        opt_map (fun l2 => (MB0, sR02LOut (kr - 1) l2, SRC (R0 4) :: sPushR02 0 r2))
          (sBumpLN 2%nat sl)
    end
  end.

Definition sMotifR9 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match stripSymRC [R0 9; R1 0] sr with
  | None => None
  | Some rRest =>
    match stripSymLC [LD 7] sl with
    | None => None
    | Some l1 =>
      match sPopML8 l1 with
      | Some (k, lRest) =>
        Some (MB0, SLC (LD 7) :: lRest, SRC (R0 9) :: SRC (R1 0) :: sPushMR11_conc k rRest)
      | None =>
        match stripSymLC u1TopL l1 with
        | Some lRest =>
          Some (MB0, SLC (LD 7) :: lRest, SRC (R0 9) :: SRC (R1 0) :: sPushMR11_conc 0 rRest)
        | None => None
        end
      end
    end
  end.

Definition sMotifR19 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match stripSymRC [R1 9] sr with
  | None => None
  | Some rRest =>
    match sPopLD1 sl with
    | Some (k, lRest) =>
      Some (MB0, lRest, SRC (R1 9) :: sPushR02 k rRest)
    | None =>
      match stripSymLC [LD 5] sl with
      | None => None
      | Some l1 =>
        match sPopSymM2 l1 with
        | Some (d, lRest) =>
          opt_map (fun pr => (MB0, SLC (LD 5) :: lRest, SRC (R1 9) :: pr))
            (sPushM2R_sym d rRest)
        | None =>
          match sPopM2L l1 with
          | Some (k, lRest) =>
            Some (MB0, SLC (LD 5) :: lRest, SRC (R1 9) :: sPushM2R_conc k rRest)
          | None =>
            match stripSymLC u2TopL l1 with
            | Some lRest =>
              Some (MB0, SLC (LD 5) :: lRest, SRC (R1 9) :: sPushM2R_conc 0 rRest)
            | None => None
            end
          end
        end
      end
    end
  end.

Definition sMotifR15 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match stripSymRC [R1 5] sr with
  | None => None
  | Some rRest =>
    match stripSymLC [LD 5] sl with
    | None => None
    | Some l1 =>
      match sPopLD1Ge4 l1 with
      | None => None
      | Some (k, lRest) =>
        Some (MB0, lRest, SRC (R1 9) :: sLd5ROut k rRest)
      end
    end
  end.

Definition sStepMotifB0 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match sMotifR4 sl sr with
  | Some res => Some res
  | None =>
    match sMotifR9 sl sr with
    | Some res => Some res
    | None =>
      match sMotifR19 sl sr with
      | Some res => Some res
      | None => sMotifR15 sl sr
      end
    end
  end.

Definition symStepA (m : Mode) (sl0 : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  let sl := sNormB0W3 m sl0 sr in
  match m with
  | MDL => sStepDL sl sr
  | MB0 =>
    match sStepMotifB0 sl sr with
    | Some res => Some res
    | None => sStepB0Base sl sr
    end
  end.

Fixpoint symRunA (steps : nat) (m : Mode) (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match steps with
  | O => Some (m, sl, sr)
  | S n =>
    match symStepA m sl sr with
    | None => None
    | Some (m', sl', sr') => symRunA n m' sl' sr'
    end
  end.

Definition checkSymA (steps : nat) (m : Mode) (sl : list SymLTok) (sr : list SymRTok)
  (m' : Mode) (sl' : list SymLTok) (sr' : list SymRTok) : bool :=
  match symRunA steps m sl sr with
  | None => false
  | Some (rm, rsl, rsr) =>
    beqMode rm m' && beqSymLList rsl sl' && beqSymRList rsr sr'
  end.

Lemma evalSymR_cons (r1 : SymRTok) (rs : list SymRTok) (vr v2 : N) :
  exists y ys, evalSymR vr v2 (r1 :: rs) = y :: ys.
Proof. destruct r1; eexists; eexists; reflexivity. Qed.

Lemma sStepDL_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sStepDL sl sr = Some (m', sl', sr')) :
  SymReached MDL sl sr m' sl' sr'.
Proof.
  unfold sStepDL in h.
  destruct (sUnconsL sl) as [[[v | v] lRest] |] eqn:hu; [| | discriminate].
  - destruct (sBumpL (sPeelL0 v lRest)) as [sl1 |] eqn:hb; [| discriminate].
    destruct (sAddR 0 sr) as [sr1 |] eqn:har; [| discriminate].
    injection h as <- <- <-.
    intros vr v2 v3 v4 rest.
    set (xs := evalSymL v2 v3 v4 lRest rest).
    set (R := evalSymR vr v2 sr).
    pose proof (stepDL_sound (L0 v :: xs) R) as hs.
    change (stepDL (L0 v :: xs) R) with (Core MDL (bumpL (peelL0 v xs)) (addR 0 R)) in hs.
    assert (heL : eL (evalSymL v2 v3 v4 sl1 rest) = eL (bumpL (peelL0 v xs))).
    { rewrite (eL_sBumpL hb v2 v3 v4 rest), <- eL_peelL0_eq_sPeelL0, eL_bumpL. reflexivity. }
    assert (heR : eR (evalSymR vr v2 sr1) = eR (addR 0 R)).
    { rewrite (eR_sAddR har vr v2), eR_addR. reflexivity. }
    rewrite (encodeBase_core_congr MDL (sUnconsL_L0 hu v2 v3 v4 rest) (@eq_refl _ (eR R))),
            (encodeBase_core_congr MDL heL heR).
    exact hs.
  - injection h as <- <- <-.
    intros vr v2 v3 v4 rest.
    set (xs := evalSymL v2 v3 v4 lRest rest).
    set (R := evalSymR vr v2 sr).
    pose proof (stepDL_sound (LD v :: xs) R) as hs.
    change (stepDL (LD v :: xs) R) with (Core MB0 xs (pushR0 v R)) in hs.
    assert (heR : eR (evalSymR vr v2 (sPushR0 v sr)) = eR (pushR0 v R)).
    { rewrite eR_sPushR0, eR_pushR0. reflexivity. }
    rewrite (encodeBase_core_congr MDL (sUnconsL_LD hu v2 v3 v4 rest) (@eq_refl _ (eR R))),
            (encodeBase_core_congr MB0 (@eq_refl _ (eL xs)) heR).
    exact hs.
Qed.

Lemma sFoldDL2_sound
  {m0 : Mode} {sl0 sl1 : list SymLTok} {sr0 sr1 : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (hpre : SymReached m0 sl0 sr0 MDL sl1 sr1)
  (hf : sFoldDL2 sl1 sr1 = Some (m', sl', sr')) :
  SymReached m0 sl0 sr0 m' sl' sr'.
Proof.
  unfold sFoldDL2 in hf.
  destruct (sStepDL sl1 sr1) as [[[m2 sl2] sr2] |] eqn:h1; [| discriminate].
  pose proof (symReached_trans hpre (sStepDL_sound h1)) as hs1.
  destruct m2.
  - injection hf as <- <- <-. exact hs1.
  - exact (symReached_trans hs1 (sStepDL_sound hf)).
Qed.

Lemma eL_bumpL2 (xs : list LTok) : eL (bumpL (bumpL xs)) = repBlock [S1] 2 *> eL xs.
Proof. rewrite !eL_bumpL. reflexivity. Qed.

Lemma eL_bumpL3 (xs : list LTok) : eL (bumpL (bumpL (bumpL xs))) = repBlock [S1] 3 *> eL xs.
Proof. rewrite !eL_bumpL. reflexivity. Qed.

Lemma eL_bumpL4 (xs : list LTok) : eL (bumpL (bumpL (bumpL (bumpL xs)))) = repBlock [S1] 4 *> eL xs.
Proof. rewrite !eL_bumpL. reflexivity. Qed.

Lemma stepB0Base_to_pos (isR1 : bool) (dp : N) (L_ : list LTok) (RRest : list RTok) :
  stepB0Base L_ ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: RRest) =
  stepB0Pos isR1 dp L_ RRest.
Proof.
  assert (hpos : dp + 1 =? 0 = false) by (apply N.eqb_neq; lia).
  assert (hsub : dp + 1 - 1 = dp) by lia.
  destruct isR1; cbn [stepB0Base unconsR]; rewrite hpos, hsub; reflexivity.
Qed.

Lemma stepB0Pos_even (isR1 : bool) (dp : N) (hmod : dp mod 2 =? 1 = false) (L_ : list LTok) (RRest : list RTok) :
  stepB0Pos isR1 dp L_ RRest =
  let q := dp / 2 in
  let l2 := bumpL (bumpL L_) in
  let rNew := if isR1 then pushR0 2 RRest else addR 2 RRest in
  if q =? 0 then stepB0OddQ0 L_ rNew
  else if q =? 1 then Core MB0 l2 rNew
  else foldDL2 (pushZeros (q - 2) l2) (R1 0 :: rNew).
Proof. unfold stepB0Pos; rewrite hmod; reflexivity. Qed.

Lemma sStepB0Pos_sound (isR1 : bool) (dp : N)
  {sl : list SymLTok} {sr rRest : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (hR : forall vr v2, eR (evalSymR vr v2 sr) =
          eR ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: evalSymR vr v2 rRest))
  (hp : sStepB0Pos isR1 dp sl rRest = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sStepB0Pos in hp.
  destruct (dp mod 2 =? 1) eqn:hmod.
  - destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
    destruct isR1.
    + injection hp as <- <- <-.
      intros vr v2 v3 v4 rest.
      set (L_ := evalSymL v2 v3 v4 sl rest).
      set (RRest := evalSymR vr v2 rRest).
      pose proof (stepB0Base_sound L_ (R1 (dp + 1) :: RRest)) as hs.
      rewrite (stepB0Base_to_pos true dp L_ RRest) in hs.
      unfold stepB0Pos in hs; rewrite hmod in hs.
      assert (heL : eL (evalSymL v2 v3 v4 (SLC (LD 0) :: sPushZeros (dp / 2) l2) rest) =
                    eL (LD 0 :: pushZeros (dp / 2) (bumpL (bumpL L_)))).
      { cbn [evalSymL].
        change (eL (LD 0 :: evalSymL v2 v3 v4 (sPushZeros (dp / 2) l2) rest)) with
          ([S1; S1; S0] *> eL (evalSymL v2 v3 v4 (sPushZeros (dp / 2) l2) rest)).
        change (eL (LD 0 :: pushZeros (dp / 2) (bumpL (bumpL L_)))) with
          ([S1; S1; S0] *> eL (pushZeros (dp / 2) (bumpL (bumpL L_)))).
        rewrite eL_sPushZeros, eL_pushZeros, (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2.
        reflexivity. }
      rewrite (encodeBase_core_congr MB0 eq_refl (hR vr v2)),
              (encodeBase_core_congr MB0 heL eq_refl).
      exact hs.
    + destruct rRest as [| r1 rs].
      * destruct (sBumpLN 2%nat (sPushZeros (dp / 2 + 1) l2)) as [l4 |] eqn:hb4; [| discriminate].
        injection hp as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (L_ := evalSymL v2 v3 v4 sl rest).
        pose proof (stepB0Base_sound L_ [R0 (dp + 1)]) as hs.
        rewrite (stepB0Base_to_pos false dp L_ []) in hs.
        unfold stepB0Pos in hs; rewrite hmod in hs.
        assert (heL : eL (evalSymL v2 v3 v4 l4 rest) =
                      eL (bumpL (bumpL (pushZeros (dp / 2 + 1) (bumpL (bumpL L_)))))).
        { rewrite (eL_sBumpLN 2%nat hb4 v2 v3 v4 rest), eL_sPushZeros,
                  (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2, eL_pushZeros, eL_bumpL2.
          reflexivity. }
        rewrite (encodeBase_core_congr MB0 eq_refl (hR vr v2)),
                (encodeBase_core_congr MDL heL eq_refl).
        exact hs.
      * destruct (sAddR 1 (r1 :: rs)) as [sr1 |] eqn:har; [| discriminate].
        injection hp as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (L_ := evalSymL v2 v3 v4 sl rest).
        destruct (evalSymR_cons r1 rs vr v2) as [y [ys hcons]].
        pose proof (stepB0Base_sound L_ (R0 (dp + 1) :: y :: ys)) as hs.
        rewrite (stepB0Base_to_pos false dp L_ (y :: ys)) in hs.
        unfold stepB0Pos in hs; rewrite hmod in hs.
        assert (heL : eL (evalSymL v2 v3 v4 (sPushZeros (dp / 2) l2) rest) =
                      eL (pushZeros (dp / 2) (bumpL (bumpL L_)))).
        { rewrite eL_sPushZeros, eL_pushZeros, (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2.
          reflexivity. }
        assert (heR : eR (evalSymR vr v2 sr1) = eR (addR 1 (y :: ys))).
        { rewrite (eR_sAddR har vr v2), hcons, eR_addR. reflexivity. }
        assert (hR0 : eR (evalSymR vr v2 sr) = eR (R0 (dp + 1) :: y :: ys)).
        { rewrite (hR vr v2), hcons. reflexivity. }
        rewrite (encodeBase_core_congr MB0 eq_refl hR0),
                (encodeBase_core_congr MB0 heL heR).
        exact hs.
  - set (srNewOpt := if isR1 then Some (sPushR0 2 rRest) else sAddR 2 rRest) in hp.
    destruct srNewOpt as [srNew |] eqn:hnew; [| discriminate].
    assert (heRNew : forall vr v2, eR (evalSymR vr v2 srNew) =
              eR (if isR1 then pushR0 2 (evalSymR vr v2 rRest) else addR 2 (evalSymR vr v2 rRest))).
    { intros vr v2. unfold srNewOpt in hnew. destruct isR1.
      - injection hnew as <-. rewrite eR_sPushR0, eR_pushR0. reflexivity.
      - rewrite (eR_sAddR hnew vr v2), eR_addR. reflexivity. }
    destruct (dp / 2 =? 0) eqn:hq0.
    + destruct (sUnconsL sl) as [[[lv | lv] lRest] |] eqn:hu; [| | discriminate].
      * destruct (sAddR 1 srNew) as [sr1 |] eqn:har; [| discriminate].
        injection hp as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (xs := evalSymL v2 v3 v4 lRest rest).
        set (RRest := evalSymR vr v2 rRest).
        pose proof (stepB0Base_sound (L0 lv :: xs)
          ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: RRest)) as hs.
        rewrite (stepB0Base_to_pos isR1 dp (L0 lv :: xs) RRest),
                (stepB0Pos_even isR1 dp hmod (L0 lv :: xs) RRest) in hs.
        cbv zeta in hs; rewrite hq0 in hs. cbn [stepB0OddQ0 unconsL] in hs.
        assert (heL : eL (evalSymL v2 v3 v4 (sPeelL0 lv lRest) rest) = eL (peelL0 lv xs)).
        { symmetry; exact (eL_peelL0_eq_sPeelL0 lv v2 v3 v4 lRest rest). }
        assert (heR : eR (evalSymR vr v2 sr1) =
                      eR (addR 1 (if isR1 then pushR0 2 RRest else addR 2 RRest))).
        { rewrite (eR_sAddR har vr v2), (heRNew vr v2), eR_addR. reflexivity. }
        rewrite (encodeBase_core_congr MB0 (sUnconsL_L0 hu v2 v3 v4 rest) (hR vr v2)),
                (encodeBase_core_congr MB0 heL heR).
        exact hs.
      * destruct (sAddR (lv + 2) srNew) as [sr1 |] eqn:har; [| discriminate].
        injection hp as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (xs := evalSymL v2 v3 v4 lRest rest).
        set (RRest := evalSymR vr v2 rRest).
        pose proof (stepB0Base_sound (LD lv :: xs)
          ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: RRest)) as hs.
        rewrite (stepB0Base_to_pos isR1 dp (LD lv :: xs) RRest),
                (stepB0Pos_even isR1 dp hmod (LD lv :: xs) RRest) in hs.
        cbv zeta in hs; rewrite hq0 in hs. cbn [stepB0OddQ0 unconsL] in hs.
        assert (heR : eR (evalSymR vr v2 sr1) =
                      eR (addR (lv + 2) (if isR1 then pushR0 2 RRest else addR 2 RRest))).
        { rewrite (eR_sAddR har vr v2), (heRNew vr v2), eR_addR. reflexivity. }
        rewrite (encodeBase_core_congr MB0 (sUnconsL_LD hu v2 v3 v4 rest) (hR vr v2)),
                (encodeBase_core_congr MB0 (@eq_refl _ (eL xs)) heR).
        exact hs.
    + destruct (dp / 2 =? 1) eqn:hq1.
      * destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
        injection hp as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (L_ := evalSymL v2 v3 v4 sl rest).
        set (RRest := evalSymR vr v2 rRest).
        pose proof (stepB0Base_sound L_
          ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: RRest)) as hs.
        rewrite (stepB0Base_to_pos isR1 dp L_ RRest),
                (stepB0Pos_even isR1 dp hmod L_ RRest) in hs.
        cbv zeta in hs; rewrite hq0, hq1 in hs.
        assert (heL : eL (evalSymL v2 v3 v4 l2 rest) = eL (bumpL (bumpL L_))).
        { rewrite (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2. reflexivity. }
        rewrite (encodeBase_core_congr MB0 eq_refl (hR vr v2)),
                (encodeBase_core_congr MB0 heL (heRNew vr v2)).
        exact hs.
      * destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
        apply N.eqb_neq in hq0. apply N.eqb_neq in hq1. apply N.eqb_neq in hmod.
        set (q' := dp / 2 - 2) in hp |- *.
        assert (hq_eq : dp / 2 = q' + 2) by (unfold q'; lia).
        assert (hpre : SymReached MB0 sl sr MDL (sPushZeros q' l2) (SRC (R1 0) :: srNew)).
        { intros vr v2 v3 v4 rest.
          set (L_ := evalSymL v2 v3 v4 sl rest).
          set (RRest := evalSymR vr v2 rRest).
          pose proof (b0EvenGe2_preDL_sound isR1 dp q' hmod hq_eq L_ RRest) as hbs.
          assert (heL : eL (evalSymL v2 v3 v4 (sPushZeros q' l2) rest) =
                        eL (pushZeros q' (bumpL (bumpL L_)))).
          { rewrite eL_sPushZeros, eL_pushZeros, (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2.
            reflexivity. }
          assert (heR : eR (evalSymR vr v2 (SRC (R1 0) :: srNew)) =
                        eR (R1 0 :: (if isR1 then pushR0 2 RRest else addR 2 RRest))).
          { cbn [evalSymR].
            change (eR (R1 0 :: evalSymR vr v2 srNew)) with ([S1; S0; S0] *> eR (evalSymR vr v2 srNew)).
            change (eR (R1 0 :: (if isR1 then pushR0 2 RRest else addR 2 RRest))) with
              ([S1; S0; S0] *> eR (if isR1 then pushR0 2 RRest else addR 2 RRest)).
            rewrite (heRNew vr v2). reflexivity. }
          rewrite (encodeBase_core_congr MB0 eq_refl (hR vr v2)),
                  (encodeBase_core_congr MDL heL heR).
          exact hbs. }
        exact (sFoldDL2_sound hpre hp).
Qed.

Lemma sStepB0Base_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sStepB0Base sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sStepB0Base in h.
  destruct (sUnconsR sr) as [[[[d | d] rRest] |] |] eqn:hur; try discriminate.
  - destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      destruct rRest as [| r1 rs].
      * destruct (sBumpLN 4%nat sl) as [sl1 |] eqn:hb4; [| discriminate].
        injection h as <- <- <-.
        intros vr v2 v3 v4 rest.
        set (L_ := evalSymL v2 v3 v4 sl rest).
        pose proof (stepB0Base_sound L_ [R0 0]) as hs.
        change (stepB0Base L_ [R0 0]) with (Core MDL (bumpL (bumpL (bumpL (bumpL L_)))) [R0 0]) in hs.
        assert (heL : eL (evalSymL v2 v3 v4 sl1 rest) = eL (bumpL (bumpL (bumpL (bumpL L_))))).
        { rewrite (eL_sBumpLN 4%nat hb4 v2 v3 v4 rest), eL_bumpL4. reflexivity. }
        rewrite (encodeBase_core_congr MB0 eq_refl (sUnconsR_R0 hur vr v2)),
                (encodeBase_core_congr MDL heL eq_refl).
        exact hs.
      * destruct (sUnconsL sl) as [[[lv | lv] lRest] |] eqn:hul; [| | discriminate].
        -- destruct (sAddR 3 (r1 :: rs)) as [sr1 |] eqn:har; [| discriminate].
           injection h as <- <- <-.
           intros vr v2 v3 v4 rest.
           set (xs := evalSymL v2 v3 v4 lRest rest).
           destruct (evalSymR_cons r1 rs vr v2) as [y [ys hcons]].
           pose proof (stepB0Base_sound (L0 lv :: xs) (R0 0 :: y :: ys)) as hs.
           change (stepB0Base (L0 lv :: xs) (R0 0 :: y :: ys)) with
             (Core MB0 (peelL0 lv xs) (addR 3 (y :: ys))) in hs.
           assert (hR0 : eR (evalSymR vr v2 sr) = eR (R0 0 :: y :: ys)).
           { rewrite (sUnconsR_R0 hur vr v2), hcons. reflexivity. }
           assert (heL : eL (evalSymL v2 v3 v4 (sPeelL0 lv lRest) rest) = eL (peelL0 lv xs)).
           { symmetry; exact (eL_peelL0_eq_sPeelL0 lv v2 v3 v4 lRest rest). }
           assert (heR : eR (evalSymR vr v2 sr1) = eR (addR 3 (y :: ys))).
           { rewrite (eR_sAddR har vr v2), hcons, eR_addR. reflexivity. }
           rewrite (encodeBase_core_congr MB0 (sUnconsL_L0 hul v2 v3 v4 rest) hR0),
                   (encodeBase_core_congr MB0 heL heR).
           exact hs.
        -- destruct (sAddR (lv + 4) (r1 :: rs)) as [sr1 |] eqn:har; [| discriminate].
           injection h as <- <- <-.
           intros vr v2 v3 v4 rest.
           set (xs := evalSymL v2 v3 v4 lRest rest).
           destruct (evalSymR_cons r1 rs vr v2) as [y [ys hcons]].
           pose proof (stepB0Base_sound (LD lv :: xs) (R0 0 :: y :: ys)) as hs.
           change (stepB0Base (LD lv :: xs) (R0 0 :: y :: ys)) with
             (Core MB0 xs (addR (lv + 4) (y :: ys))) in hs.
           assert (hR0 : eR (evalSymR vr v2 sr) = eR (R0 0 :: y :: ys)).
           { rewrite (sUnconsR_R0 hur vr v2), hcons. reflexivity. }
           assert (heR : eR (evalSymR vr v2 sr1) = eR (addR (lv + 4) (y :: ys))).
           { rewrite (eR_sAddR har vr v2), hcons, eR_addR. reflexivity. }
           rewrite (encodeBase_core_congr MB0 (sUnconsL_LD hul v2 v3 v4 rest) hR0),
                   (encodeBase_core_congr MB0 (@eq_refl _ (eL xs)) heR).
           exact hs.
    + apply N.eqb_neq in hd0.
      refine (sStepB0Pos_sound false (d - 1) _ h).
      intros vr v2. replace (d - 1 + 1) with d by lia. exact (sUnconsR_R0 hur vr v2).
  - destruct (d =? 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d.
      destruct (sBumpLN 3%nat sl) as [sl1 |] eqn:hb3; [| discriminate].
      injection h as <- <- <-.
      intros vr v2 v3 v4 rest.
      set (L_ := evalSymL v2 v3 v4 sl rest).
      set (RRest := evalSymR vr v2 rRest).
      pose proof (stepB0Base_sound L_ (R1 0 :: RRest)) as hs.
      change (stepB0Base L_ (R1 0 :: RRest)) with (Core MB0 (bumpL (bumpL (bumpL L_))) RRest) in hs.
      assert (heL : eL (evalSymL v2 v3 v4 sl1 rest) = eL (bumpL (bumpL (bumpL L_)))).
      { rewrite (eL_sBumpLN 3%nat hb3 v2 v3 v4 rest), eL_bumpL3. reflexivity. }
      rewrite (encodeBase_core_congr MB0 eq_refl (sUnconsR_R1 hur vr v2)),
              (encodeBase_core_congr MB0 heL eq_refl).
      exact hs.
    + apply N.eqb_neq in hd0.
      refine (sStepB0Pos_sound true (d - 1) _ h).
      intros vr v2. replace (d - 1 + 1) with d by lia. exact (sUnconsR_R1 hur vr v2).
  - destruct (sBumpL sl) as [sl1 |] eqn:hb; [| discriminate].
    injection h as <- <- <-.
    intros vr v2 v3 v4 rest.
    set (L_ := evalSymL v2 v3 v4 sl rest).
    pose proof (stepB0Base_sound L_ []) as hs.
    change (stepB0Base L_ []) with (Core MDL (bumpL L_) [R0 0]) in hs.
    assert (heL : eL (evalSymL v2 v3 v4 sl1 rest) = eL (bumpL L_)).
    { rewrite (eL_sBumpL hb v2 v3 v4 rest), eL_bumpL. reflexivity. }
    rewrite (sUnconsR_empty hur vr v2), (encodeBase_core_congr MDL heL eq_refl).
    exact hs.
Qed.

Lemma sPopR02_some {sr r2 : list SymRTok} {k : N}
  (h : sPopR02 sr = Some (k, r2)) : sr = SRC (R02 k) :: r2.
Proof.
  destruct sr as [| [t | ? | ?] tl]; try discriminate.
  destruct t; try discriminate; inversion h; subst; reflexivity.
Qed.

Lemma sPopLD1_some {sl lRest : list SymLTok} {k : N}
  (h : sPopLD1 sl = Some (k, lRest)) : sl = SLC (LD1 k) :: lRest.
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try discriminate.
  destruct t; try discriminate; inversion h; subst; reflexivity.
Qed.

Lemma sPopLD1Ge4_some {sl lRest : list SymLTok} {k : N}
  (h : sPopLD1Ge4 sl = Some (k, lRest)) : sl = SLC (LD1 (k + 4)) :: lRest.
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try discriminate.
  destruct t as [? | ? | m | ? | ? | ? | ?]; try discriminate.
  cbn [sPopLD1Ge4] in h. destruct (4 <=? m) eqn:hle; [| discriminate].
  apply N.leb_le in hle. inversion h; subst.
  replace (m - 4 + 4) with m by lia. reflexivity.
Qed.

Lemma sPopML8_some {sl lRest : list SymLTok} {k : N}
  (h : sPopML8 sl = Some (k, lRest)) : sl = SLC (ML8 k) :: lRest.
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try discriminate.
  destruct t; try discriminate; inversion h; subst; reflexivity.
Qed.

Lemma sPopM2L_some {sl lRest : list SymLTok} {k : N}
  (h : sPopM2L sl = Some (k, lRest)) : sl = SLC (M2L k) :: lRest.
Proof.
  destruct sl as [| [t | ? | ? | ? | ? | ?] tl]; try discriminate.
  destruct t; try discriminate; inversion h; subst; reflexivity.
Qed.

Lemma sPopSymM2_some {sl lRest : list SymLTok} {d : N}
  (h : sPopSymM2 sl = Some (d, lRest)) : sl = SM2 d :: lRest.
Proof.
  destruct sl as [| [? | d' | ? | ? | ? | ?] tl]; try discriminate.
  inversion h; subst; reflexivity.
Qed.

Lemma eR_sLd5ROut (k vr v2 : N) (rRest : list SymRTok) :
  eR (evalSymR vr v2 (sLd5ROut k rRest)) = eR (ld5ROut k (evalSymR vr v2 rRest)).
Proof.
  assert (hmid : eR (evalSymR vr v2 (SRC (R1 3) :: SRC (R02 0) :: SRC (R1 3) :: sPushR02 1 rRest)) =
                 eR (R1 3 :: R02 0 :: R1 3 :: pushR02 1 (evalSymR vr v2 rRest))).
  { cbn [evalSymR].
    change (eR (R1 3 :: R02 0 :: R1 3 :: evalSymR vr v2 (sPushR02 1 rRest))) with
      ([S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0] *>
       eR (evalSymR vr v2 (sPushR02 1 rRest))).
    change (eR (R1 3 :: R02 0 :: R1 3 :: pushR02 1 (evalSymR vr v2 rRest))) with
      ([S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S1; S1; S1; S0; S0] *>
       eR (pushR02 1 (evalSymR vr v2 rRest))).
    rewrite eR_sPushR02, eR_pushR02. reflexivity. }
  unfold sLd5ROut, ld5ROut. destruct (k =? 0) eqn:hk.
  - exact hmid.
  - rewrite eR_sPushR02, eR_pushR02, hmid. reflexivity.
Qed.

Lemma eL_sR02LOut {k : N} {sl l2 : list SymLTok} (hb2 : sBumpLN 2%nat sl = Some l2)
  (v2 v3 v4 : N) (rest : list LTok) :
  eL (evalSymL v2 v3 v4 (sR02LOut k l2) rest) =
  eL (r02LOut k (evalSymL v2 v3 v4 sl rest)).
Proof.
  assert (hl2 : eL (evalSymL v2 v3 v4 l2 rest) = eL (bumpL (bumpL (evalSymL v2 v3 v4 sl rest)))).
  { rewrite (eL_sBumpLN 2%nat hb2 v2 v3 v4 rest), eL_bumpL2. reflexivity. }
  unfold sR02LOut, r02LOut. destruct (k =? 0) eqn:hk.
  - rewrite eL_sPushL0, eL_pushL0, hl2. reflexivity.
  - rewrite eL_sPushL0, eL_pushL0, eL_sPushLD1, eL_pushLD1, hl2. reflexivity.
Qed.

Lemma sStepMotifR4Zero_sound {sl : list SymLTok} {r2 : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sStepMotifR4Zero sl r2 = Some (m', sl', sr')) :
  SymReached MB0 sl (SRC (R0 4) :: SRC (R02 0) :: r2) m' sl' sr'.
Proof.
  destruct r2 as [| [t | d | d] r3]; [discriminate | | |].
  - destruct t as [? | ? | ? | k | k]; try discriminate; cbn [sStepMotifR4Zero] in h.
    + assert (hmb : forall sl0 p, sPushWM1_conc k sl0 = Some p ->
                SymReached MB0 sl0 (SRC (R0 4) :: SRC (R02 0) :: SRC (MR11 k) :: r3)
                  MB0 p (SRC (R0 4) :: sPushR02 0 r3)).
      { intros sl0 p hp vr v2 v3 v4 rest.
        set (L_ := evalSymL v2 v3 v4 sl0 rest).
        set (R3 := evalSymR vr v2 r3).
        assert (heR : eR (evalSymR vr v2 (SRC (R0 4) :: sPushR02 0 r3)) = eR (R0 4 :: pushR02 0 R3)).
        { cbn [evalSymR].
          change (eR (R0 4 :: evalSymR vr v2 (sPushR02 0 r3))) with
            ([S1; S1; S1; S1; S1; S0] *> eR (evalSymR vr v2 (sPushR02 0 r3))).
          change (eR (R0 4 :: pushR02 0 R3)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 R3)).
          rewrite eR_sPushR02, eR_pushR02. reflexivity. }
        assert (heL : eL (evalSymL v2 v3 v4 p rest) = eL (pushWM1 k L_)).
        { rewrite (eL_sPushWM1_conc hp v2 v3 v4 rest), eL_pushWM1. reflexivity. }
        rewrite (encodeBase_core_congr MB0 heL heR).
        exact (motifB_sound k L_ R3). }
      destruct (beqSymRList r3 capTailSym) eqn:hcap.
      * destruct (stripSymLC [LD 3] sl) as [lRest |] eqn:hl3.
        -- injection h as <- <- <-.
           rewrite (eq_of_beqSymRList r3 capTailSym hcap), (stripSymLC_some [LD 3] sl lRest hl3).
           intros vr v2 v3 v4 rest.
           exact (capRoundtrip_sound k (evalSymL v2 v3 v4 lRest rest)).
        -- destruct (sPushWM1_conc k sl) as [p |] eqn:hp; [| discriminate].
           injection h as <- <- <-. exact (hmb sl p hp).
      * destruct (sPushWM1_conc k sl) as [p |] eqn:hp; [| discriminate].
        injection h as <- <- <-. exact (hmb sl p hp).
    + destruct (sPushWM2_conc k sl) as [p |] eqn:hp; [| discriminate].
      injection h as <- <- <-.
      intros vr v2 v3 v4 rest.
      set (L_ := evalSymL v2 v3 v4 sl rest).
      set (R3 := evalSymR vr v2 r3).
      assert (heR : eR (evalSymR vr v2 (SRC (R0 4) :: sPushR02 0 r3)) = eR (R0 4 :: pushR02 0 R3)).
      { cbn [evalSymR].
        change (eR (R0 4 :: evalSymR vr v2 (sPushR02 0 r3))) with
          ([S1; S1; S1; S1; S1; S0] *> eR (evalSymR vr v2 (sPushR02 0 r3))).
        change (eR (R0 4 :: pushR02 0 R3)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 R3)).
        rewrite eR_sPushR02, eR_pushR02. reflexivity. }
      assert (heL : eL (evalSymL v2 v3 v4 p rest) = eL (pushWM2 k L_)).
      { rewrite (eL_sPushWM2_conc hp v2 v3 v4 rest), eL_pushWM2. reflexivity. }
      rewrite (encodeBase_core_congr MB0 heL heR).
      exact (motif2B_sound k L_ R3).
  - cbn [sStepMotifR4Zero] in h.
    destruct (beqSymRList r3 capTailSym) eqn:hcap; [| discriminate].
    destruct (stripSymLC [LD 3] sl) as [lRest |] eqn:hl3; [| discriminate].
    injection h as <- <- <-.
    rewrite (eq_of_beqSymRList r3 capTailSym hcap), (stripSymLC_some [LD 3] sl lRest hl3).
    intros vr v2 v3 v4 rest.
    exact (capRoundtrip_sound (vr + d) (evalSymL v2 v3 v4 lRest rest)).
  - cbn [sStepMotifR4Zero] in h.
    destruct (sPushWM2_sym d sl) as [p |] eqn:hp; [| discriminate].
    injection h as <- <- <-.
    intros vr v2 v3 v4 rest.
    set (L_ := evalSymL v2 v3 v4 sl rest).
    set (R3 := evalSymR vr v2 r3).
    assert (heR : eR (evalSymR vr v2 (SRC (R0 4) :: sPushR02 0 r3)) = eR (R0 4 :: pushR02 0 R3)).
    { cbn [evalSymR].
      change (eR (R0 4 :: evalSymR vr v2 (sPushR02 0 r3))) with
        ([S1; S1; S1; S1; S1; S0] *> eR (evalSymR vr v2 (sPushR02 0 r3))).
      change (eR (R0 4 :: pushR02 0 R3)) with ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 R3)).
      rewrite eR_sPushR02, eR_pushR02. reflexivity. }
    assert (heL : eL (evalSymL v2 v3 v4 p rest) = eL (pushWM2 (v2 + d) L_)).
    { rewrite (eL_sPushWM2_sym hp v2 v3 v4 rest), eL_pushWM2. reflexivity. }
    rewrite (encodeBase_core_congr MB0 heL heR).
    exact (motif2B_sound (v2 + d) L_ R3).
Qed.

Lemma sMotifR4_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sMotifR4 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sMotifR4 in h.
  destruct (stripSymRC [R0 4] sr) as [rAfter4 |] eqn:hr4; [| discriminate].
  destruct (sPopR02 rAfter4) as [[kr r2] |] eqn:hr02; [| discriminate].
  rewrite (stripSymRC_some [R0 4] sr rAfter4 hr4), (sPopR02_some hr02).
  destruct (kr =? 0) eqn:hkr0.
  - apply N.eqb_eq in hkr0; subst kr. exact (sStepMotifR4Zero_sound h).
  - apply N.eqb_neq in hkr0.
    destruct (sBumpLN 2%nat sl) as [l2 |] eqn:hb2; [| discriminate].
    injection h as <- <- <-.
    intros vr v2 v3 v4 rest.
    assert (heR_out : eR (evalSymR vr v2 (SRC (R0 4) :: sPushR02 0 r2)) =
                      eR (R0 4 :: pushR02 0 (evalSymR vr v2 r2))).
    { cbn [evalSymR].
      change (eR (R0 4 :: evalSymR vr v2 (sPushR02 0 r2))) with
        ([S1; S1; S1; S1; S1; S0] *> eR (evalSymR vr v2 (sPushR02 0 r2))).
      change (eR (R0 4 :: pushR02 0 (evalSymR vr v2 r2))) with
        ([S1; S1; S1; S1; S1; S0] *> eR (pushR02 0 (evalSymR vr v2 r2))).
      rewrite eR_sPushR02, eR_pushR02. reflexivity. }
    rewrite (encodeBase_core_congr MB0 (eL_sR02LOut hb2 v2 v3 v4 rest) heR_out).
    cbn [map app evalSymR].
    replace kr with ((kr - 1) + 1) at 1 by lia.
    exact (r02Right_sound (kr - 1) (evalSymL v2 v3 v4 sl rest) (evalSymR vr v2 r2)).
Qed.

Lemma sMotifR9_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sMotifR9 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sMotifR9 in h.
  destruct (stripSymRC [R0 9; R1 0] sr) as [rRest |] eqn:hr9; [| discriminate].
  destruct (stripSymLC [LD 7] sl) as [l1 |] eqn:hl7; [| discriminate].
  rewrite (stripSymRC_some [R0 9; R1 0] sr rRest hr9), (stripSymLC_some [LD 7] sl l1 hl7).
  destruct (sPopML8 l1) as [[k lRest] |] eqn:hml.
  - injection h as <- <- <-. rewrite (sPopML8_some hml).
    intros vr v2 v3 v4 rest.
    assert (heR_out : eR (evalSymR vr v2 (SRC (R0 9) :: SRC (R1 0) :: sPushMR11_conc k rRest)) =
                      eR (R0 9 :: R1 0 :: pushMR11 k (evalSymR vr v2 rRest))).
    { cbn [evalSymR].
      change (eR (R0 9 :: R1 0 :: evalSymR vr v2 (sPushMR11_conc k rRest))) with
        (pRA *> eR (evalSymR vr v2 (sPushMR11_conc k rRest))).
      change (eR (R0 9 :: R1 0 :: pushMR11 k (evalSymR vr v2 rRest))) with
        (pRA *> eR (pushMR11 k (evalSymR vr v2 rRest))).
      rewrite eR_sPushMR11_conc, eR_pushMR11. reflexivity. }
    rewrite (encodeBase_core_congr MB0 eq_refl heR_out).
    exact (motifA_sound k (evalSymL v2 v3 v4 lRest rest) (evalSymR vr v2 rRest)).
  - destruct (stripSymLC u1TopL l1) as [lRestU |] eqn:hu1; [| discriminate].
    injection h as <- <- <-. rewrite (stripSymLC_some u1TopL l1 lRestU hu1).
    intros vr v2 v3 v4 rest.
    set (LRest := evalSymL v2 v3 v4 lRestU rest).
    set (RRest := evalSymR vr v2 rRest).
    assert (heL_in : eL (evalSymL v2 v3 v4 (map SLC [LD 7] ++ (map SLC u1TopL ++ lRestU)) rest) =
                     eL (LD 7 :: ML8 0 :: LRest)).
    { cbn [map app evalSymL].
      change (eL (LD 7 :: evalSymL v2 v3 v4 (map SLC u1TopL ++ lRestU) rest)) with
        (ld7Bits *> eL (evalSymL v2 v3 v4 (map SLC u1TopL ++ lRestU) rest)).
      rewrite evalSymL_map_c. cbn [u1TopL app]. rewrite eL_lu. reflexivity. }
    assert (heR_out : eR (evalSymR vr v2 (SRC (R0 9) :: SRC (R1 0) :: sPushMR11_conc 0 rRest)) =
                      eR (R0 9 :: R1 0 :: pushMR11 0 RRest)).
    { cbn [evalSymR].
      change (eR (R0 9 :: R1 0 :: evalSymR vr v2 (sPushMR11_conc 0 rRest))) with
        (pRA *> eR (evalSymR vr v2 (sPushMR11_conc 0 rRest))).
      change (eR (R0 9 :: R1 0 :: pushMR11 0 RRest)) with (pRA *> eR (pushMR11 0 RRest)).
      rewrite eR_sPushMR11_conc, eR_pushMR11. reflexivity. }
    rewrite (encodeBase_core_congr MB0 heL_in eq_refl),
            (encodeBase_core_congr MB0 eq_refl heR_out).
    exact (motifA_sound 0 LRest RRest).
Qed.

Lemma sMotifR19_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sMotifR19 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sMotifR19 in h.
  destruct (stripSymRC [R1 9] sr) as [rRest19 |] eqn:hr19; [| discriminate].
  rewrite (stripSymRC_some [R1 9] sr rRest19 hr19).
  destruct (sPopLD1 sl) as [[k lRest] |] eqn:hld1.
  - injection h as <- <- <-. rewrite (sPopLD1_some hld1).
    intros vr v2 v3 v4 rest.
    assert (heR_out : eR (evalSymR vr v2 (SRC (R1 9) :: sPushR02 k rRest19)) =
                      eR (R1 9 :: pushR02 k (evalSymR vr v2 rRest19))).
    { cbn [evalSymR].
      change (eR (R1 9 :: evalSymR vr v2 (sPushR02 k rRest19))) with
        (r1_9Bits *> eR (evalSymR vr v2 (sPushR02 k rRest19))).
      change (eR (R1 9 :: pushR02 k (evalSymR vr v2 rRest19))) with
        (r1_9Bits *> eR (pushR02 k (evalSymR vr v2 rRest19))).
      rewrite eR_sPushR02, eR_pushR02. reflexivity. }
    rewrite (encodeBase_core_congr MB0 eq_refl heR_out).
    exact (ld1Left_sound k (evalSymL v2 v3 v4 lRest rest) (evalSymR vr v2 rRest19)).
  - destruct (stripSymLC [LD 5] sl) as [l1 |] eqn:hl5; [| discriminate].
    rewrite (stripSymLC_some [LD 5] sl l1 hl5).
    destruct (sPopSymM2 l1) as [[d lRestM] |] eqn:hsm2.
    + destruct (sPushM2R_sym d rRest19) as [pr |] eqn:hpr; [| discriminate].
      injection h as <- <- <-. rewrite (sPopSymM2_some hsm2).
      intros vr v2 v3 v4 rest.
      assert (heR_out : eR (evalSymR vr v2 (SRC (R1 9) :: pr)) =
                        eR (R1 9 :: pushM2R (v2 + d) (evalSymR vr v2 rRest19))).
      { cbn [evalSymR].
        change (eR (R1 9 :: evalSymR vr v2 pr)) with (r1_9Bits *> eR (evalSymR vr v2 pr)).
        change (eR (R1 9 :: pushM2R (v2 + d) (evalSymR vr v2 rRest19))) with
          (r1_9Bits *> eR (pushM2R (v2 + d) (evalSymR vr v2 rRest19))).
        rewrite (eR_sPushM2R_sym hpr vr v2), eR_pushM2R. reflexivity. }
      rewrite (encodeBase_core_congr MB0 eq_refl heR_out).
      exact (motif2A_sound (v2 + d) (evalSymL v2 v3 v4 lRestM rest) (evalSymR vr v2 rRest19)).
    + destruct (sPopM2L l1) as [[k2 lRest2] |] eqn:hm2c.
      * injection h as <- <- <-. rewrite (sPopM2L_some hm2c).
        intros vr v2 v3 v4 rest.
        assert (heR_out : eR (evalSymR vr v2 (SRC (R1 9) :: sPushM2R_conc k2 rRest19)) =
                          eR (R1 9 :: pushM2R k2 (evalSymR vr v2 rRest19))).
        { cbn [evalSymR].
          change (eR (R1 9 :: evalSymR vr v2 (sPushM2R_conc k2 rRest19))) with
            (r1_9Bits *> eR (evalSymR vr v2 (sPushM2R_conc k2 rRest19))).
          change (eR (R1 9 :: pushM2R k2 (evalSymR vr v2 rRest19))) with
            (r1_9Bits *> eR (pushM2R k2 (evalSymR vr v2 rRest19))).
          rewrite eR_sPushM2R_conc, eR_pushM2R. reflexivity. }
        rewrite (encodeBase_core_congr MB0 eq_refl heR_out).
        exact (motif2A_sound k2 (evalSymL v2 v3 v4 lRest2 rest) (evalSymR vr v2 rRest19)).
      * destruct (stripSymLC u2TopL l1) as [lRestU |] eqn:hu2; [| discriminate].
        injection h as <- <- <-. rewrite (stripSymLC_some u2TopL l1 lRestU hu2).
        intros vr v2 v3 v4 rest.
        set (LRest := evalSymL v2 v3 v4 lRestU rest).
        set (RRest := evalSymR vr v2 rRest19).
        assert (heL_in : eL (evalSymL v2 v3 v4 (map SLC [LD 5] ++ (map SLC u2TopL ++ lRestU)) rest) =
                         eL (LD 5 :: M2L 0 :: LRest)).
        { cbn [map app evalSymL].
          change (eL (LD 5 :: evalSymL v2 v3 v4 (map SLC u2TopL ++ lRestU) rest)) with
            (ld5Bits *> eL (evalSymL v2 v3 v4 (map SLC u2TopL ++ lRestU) rest)).
          rewrite evalSymL_map_c. cbn [u2TopL app]. rewrite eL_u2. reflexivity. }
        assert (heR_out : eR (evalSymR vr v2 (SRC (R1 9) :: sPushM2R_conc 0 rRest19)) =
                          eR (R1 9 :: pushM2R 0 RRest)).
        { cbn [evalSymR].
          change (eR (R1 9 :: evalSymR vr v2 (sPushM2R_conc 0 rRest19))) with
            (r1_9Bits *> eR (evalSymR vr v2 (sPushM2R_conc 0 rRest19))).
          change (eR (R1 9 :: pushM2R 0 RRest)) with (r1_9Bits *> eR (pushM2R 0 RRest)).
          rewrite eR_sPushM2R_conc, eR_pushM2R. reflexivity. }
        rewrite (encodeBase_core_congr MB0 heL_in eq_refl),
                (encodeBase_core_congr MB0 eq_refl heR_out).
        exact (motif2A_sound 0 LRest RRest).
Qed.

Lemma sMotifR15_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sMotifR15 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sMotifR15 in h.
  destruct (stripSymRC [R1 5] sr) as [rRest15 |] eqn:hr15; [| discriminate].
  destruct (stripSymLC [LD 5] sl) as [l1 |] eqn:hl5; [| discriminate].
  destruct (sPopLD1Ge4 l1) as [[k lRest] |] eqn:hld4; [| discriminate].
  injection h as <- <- <-.
  rewrite (stripSymRC_some [R1 5] sr rRest15 hr15),
          (stripSymLC_some [LD 5] sl l1 hl5), (sPopLD1Ge4_some hld4).
  intros vr v2 v3 v4 rest.
  assert (heR : eR (evalSymR vr v2 (SRC (R1 9) :: sLd5ROut k rRest15)) =
                eR (R1 9 :: ld5ROut k (evalSymR vr v2 rRest15))).
  { cbn [evalSymR].
    change (eR (R1 9 :: evalSymR vr v2 (sLd5ROut k rRest15))) with
      (r1_9Bits *> eR (evalSymR vr v2 (sLd5ROut k rRest15))).
    change (eR (R1 9 :: ld5ROut k (evalSymR vr v2 rRest15))) with
      (r1_9Bits *> eR (ld5ROut k (evalSymR vr v2 rRest15))).
    rewrite eR_sLd5ROut. reflexivity. }
  rewrite (encodeBase_core_congr MB0 eq_refl heR).
  exact (ld5Init_sound k (evalSymL v2 v3 v4 lRest rest) (evalSymR vr v2 rRest15)).
Qed.

Lemma sStepMotifB0_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sStepMotifB0 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sStepMotifB0 in h.
  destruct (sMotifR4 sl sr) as [res |] eqn:h4; [inversion h; subst; exact (sMotifR4_sound h4) |].
  destruct (sMotifR9 sl sr) as [res |] eqn:h9; [inversion h; subst; exact (sMotifR9_sound h9) |].
  destruct (sMotifR19 sl sr) as [res |] eqn:h19; [inversion h; subst; exact (sMotifR19_sound h19) |].
  exact (sMotifR15_sound h).
Qed.

Lemma symStepA_sound {m m' : Mode} {sl0 sl' : list SymLTok} {sr sr' : list SymRTok}
  (h : symStepA m sl0 sr = Some (m', sl', sr')) :
  SymReached m sl0 sr m' sl' sr'.
Proof.
  assert (hraw : SymReached m (sNormB0W3 m sl0 sr) sr m' sl' sr').
  { unfold symStepA in h. destruct m.
    - destruct (sStepMotifB0 (sNormB0W3 MB0 sl0 sr) sr) as [res |] eqn:hm.
      + inversion h; subst. exact (sStepMotifB0_sound hm).
      + exact (sStepB0Base_sound h).
    - exact (sStepDL_sound h). }
  intros vr v2 v3 v4 rest.
  rewrite <- (encodeBase_core_congr m (eL_sNormB0W3 m sl0 sr v2 v3 v4 rest) eq_refl).
  exact (hraw vr v2 v3 v4 rest).
Qed.

Lemma symRunA_sound :
  forall (steps : nat) {m0 m rm : Mode} {sl0 sl rsl : list SymLTok} {sr0 sr rsr : list SymRTok},
    SymReached m0 sl0 sr0 m sl sr ->
    symRunA steps m sl sr = Some (rm, rsl, rsr) ->
    SymReached m0 sl0 sr0 rm rsl rsr.
Proof.
  induction steps as [| n IH]; intros m0 m rm sl0 sl rsl sr0 sr rsr hpre hr.
  - inversion hr; subst. exact hpre.
  - cbn [symRunA] in hr.
    destruct (symStepA m sl sr) as [[[m1 sl1] sr1] |] eqn:hs; [| discriminate].
    exact (IH _ _ _ _ _ _ _ _ _ (symReached_trans hpre (symStepA_sound hs)) hr).
Qed.

Lemma checkSymA_sound {steps : nat} {m m' : Mode} {sl sl' : list SymLTok} {sr sr' : list SymRTok}
  (h : checkSymA steps m sl sr m' sl' sr' = true) :
  SymReached m sl sr m' sl' sr'.
Proof.
  unfold checkSymA in h.
  destruct (symRunA steps m sl sr) as [[[rm rsl] rsr] |] eqn:hrun; [| discriminate].
  apply andb_prop in h. destruct h as [h hsr].
  apply andb_prop in h. destruct h as [hm hsl].
  rewrite <- (eq_of_beqMode hm), <- (eq_of_beqSymLList rsl sl' hsl), <- (eq_of_beqSymRList rsr sr' hsr).
  exact (symRunA_sound steps (symReached_refl m sl sr) hrun).
Qed.

(* ========================================================================= *)
(* Section 10: Layer-1 Bridges & Layer-2 Symbolic Engine (symStepB)          *)
(* ========================================================================= *)

Definition capTailR : list RTok := [R02 0; R1 3; R02 0].
Definition rc6Of (mr : N) : list RTok := R0 9 :: R1 0 :: MR11 mr :: capTailR.
Definition rc4Of (mr : N) : list RTok := R0 4 :: MR11 mr :: capTailR.

Definition h10Top : list LTok :=
  [LD 7; LD 3; LD 5; LD 7; LD 3; LD1 1; LD 5; LD 3; LD1 8; LD 5].
Definition era2MidTop : list LTok := [L0 3; LD 9; LD 7].
Definition era3aMidTop : list LTok := [LD 7; LD 3; LD1 7; LD 9; L0 3; LD1 1].
Definition era3bMidTop : list LTok := [LD 7; L0 0; LD1 1].
Definition era3cMidTop : list LTok := [LD 7; LD 3; LD1 3; LD 5; LD1 3].
Definition era4aMidTop : list LTok :=
  [LD 7; LD 3; LD1 10; LD 4; LD1 0; L0 0; LD 3; L0 0; LD1 0].
Definition era4bMidTop : list LTok :=
  [LD 7; LD 3; LD1 1; LD 4; L0 4; LD 3; L0 0; LD 3; L0 0; LD1 0].
Definition era4aEndOutTop : list LTok :=
  [LD 2; L0 1; LD 5; LD1 0; L0 2; LD1 0; L0 0; LD 7; L0 1; LD1 0;
   L0 0; LD 7; L0 2; LD1 0; L0 4; LD1 0; L0 2; LD1 0; L0 2; LD1 0].
Definition era4bEndOutTop : list LTok :=
  [LD 2; L0 1; LD 5; LD1 0; L0 2; LD1 0; L0 0; LD1 1; LD 9; L0 0; LD 7;
   LD1 1; LD 9; L0 0; LD 7; L0 2; LD 3; L0 0; LD 3; L0 0; LD1 0].

Definition bridgeH10OutTop : list RTok :=
  [R1 9; R02 7; R1 3; R02 0; R1 3; R1 3; R02 1; R1 3; R02 0; R1 3; R02 3; R1 3].
Definition bridge0aPfx : list RTok :=
  [R0 4; R02 4; R1 3; R02 3; R1 3; R02 0; R1 3; R02 1; R1 3; R02 0; R1 3;
   R02 1; R1 3; R1 3; R02 3; R1 3].
Definition bridge1Pfx : list RTok :=
  [R0 4; R02 3; R1 3; R02 0; R1 3; R02 2; R1 3; R02 1; R1 3; R1 3; R02 3; R1 3].
Definition bridge1OutTop : list RTok :=
  [R1 9; R02 3; R1 3; R02 3; R1 3; R02 0; R1 3; R02 1; R1 3; R02 0; R1 3;
   R02 1; R1 3; R1 3; R02 3; R1 3].
Definition bridge2Pfx : list RTok :=
  [R0 4; R02 8; R1 3; R02 0; R1 3; R1 3; R02 1; R1 3; R02 0; R1 3; R02 3; R1 3].
Definition bridge2OutTop : list RTok :=
  [R1 9; R02 7; R1 3; R02 0; R1 3; R02 9; R1 3; R02 0; R1 3; R1 3; R02 3; R1 3].
Definition bridge3Pfx : list RTok :=
  [R0 4; R02 8; R1 3; R02 0; R1 3; R02 9; R1 3; R02 0; R1 3; R1 3; R02 3; R1 3].
Definition bridge3OutTop : list RTok :=
  [R1 9; M2R 0; R02 2; R1 3; R02 0; R1 3; R02 2; R1 3; R02 1; R1 3; R1 3; R02 3; R1 3].

Lemma era1_step_raw :
  checkSymA 133%nat MB0
    [SLC (LD 2); SLC (L0 1)]
    (SRC (R0 4) :: SMR 1 :: capTailSym)
    MB0
    (map SLC w3TopL)
    (SRC (R0 4) :: SMR 0 :: capTailSym) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era1_step_sym :
  SymReached MB0
    [SLC (LD 2); SLC (L0 1)]
    (SRC (R0 4) :: SMR 1 :: capTailSym)
    MB0
    [SLC (LD 2); SLC (L0 1); SM3P 0]
    (SRC (R0 4) :: SMR 0 :: capTailSym).
Proof. exact (symReached_norm (checkSymA_sound era1_step_raw)). Qed.

Lemma era1_step_concrete (k : N) (after : list LTok) :
  encodeBase (Core MB0 (LD 2 :: L0 1 :: after) (rc4Of (k + 1))) -[ tm ]->*
  encodeBase (Core MB0 (LD 2 :: L0 1 :: pushM3L 0 after) (rc4Of k)).
Proof.
  pose proof (era1_step_sym k 0 0 0 after) as hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (k + 0) with k in hr by lia.
  exact hr.
Qed.

Lemma bridgeH10_raw :
  checkSymA 33%nat MB0
    (map SLC h10Top)
    (SRC (R0 9) :: SRC (R1 0) :: SMR 0 :: capTailSym)
    MB0
    [SLC (LD 5)]
    (map SRC bridgeH10OutTop ++ (SMR 0 :: capTailSym)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridgeH10_concrete (mr : N) (afterH10 : list LTok) :
  encodeBase (Core MB0 (h10Top ++ afterH10) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (LD 5 :: afterH10) (bridgeH10OutTop ++ (MR11 mr :: capTailR))).
Proof.
  pose proof (checkSymA_sound bridgeH10_raw mr 0 0 0 afterH10) as hr.
  rewrite evalSymL_map_c_nil, evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge0a_raw :
  checkSymA 73%nat MB0
    [SLC (L0 0); SLC (LD1 5); SLC (LD 5)]
    (map SRC bridge0aPfx ++ (SMR 0 :: capTailSym))
    MB0
    (map SLC h10Top)
    (SRC (R0 9) :: SRC (R1 0) :: SMR 1 :: capTailSym) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge0a_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (L0 0 :: LD1 5 :: LD 5 :: rest) (bridge0aPfx ++ (MR11 mr :: capTailR))) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ rest) (rc6Of (mr + 1))).
Proof.
  pose proof (checkSymA_sound bridge0a_raw mr 0 0 0 rest) as hr.
  rewrite evalSymL_map_c_nil, evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge1_raw :
  checkSymA 107%nat MB0
    [SLC (L0 0); SLC (LD1 5); SLC (LD 5)]
    (map SRC bridge1Pfx ++ (SMR 0 :: capTailSym))
    MB0
    [SLC (LD 5)]
    (map SRC bridge1OutTop ++ (SMR 0 :: capTailSym)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge1_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (L0 0 :: LD1 5 :: LD 5 :: rest) (bridge1Pfx ++ (MR11 mr :: capTailR))) -[ tm ]->*
  encodeBase (Core MB0 (LD 5 :: rest) (bridge1OutTop ++ (MR11 mr :: capTailR))).
Proof.
  pose proof (checkSymA_sound bridge1_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge2_raw :
  checkSymA 98%nat MB0
    [SLC (L0 0); SLC (LD1 5); SLC (LD 5)]
    (map SRC bridge2Pfx ++ (SMR 0 :: capTailSym))
    MB0
    [SLC (LD 5)]
    (map SRC bridge2OutTop ++ (SMR 0 :: capTailSym)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge2_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (L0 0 :: LD1 5 :: LD 5 :: rest) (bridge2Pfx ++ (MR11 mr :: capTailR))) -[ tm ]->*
  encodeBase (Core MB0 (LD 5 :: rest) (bridge2OutTop ++ (MR11 mr :: capTailR))).
Proof.
  pose proof (checkSymA_sound bridge2_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge3_raw :
  checkSymA 84%nat MB0
    [SLC (L0 0); SLC (LD1 5); SLC (LD 5)]
    (map SRC bridge3Pfx ++ (SMR 0 :: capTailSym))
    MB0
    [SLC (LD 5)]
    (map SRC bridge3OutTop ++ (SMR 0 :: capTailSym)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge3_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (L0 0 :: LD1 5 :: LD 5 :: rest) (bridge3Pfx ++ (MR11 mr :: capTailR))) -[ tm ]->*
  encodeBase (Core MB0 (LD 5 :: rest) (bridge3OutTop ++ (MR11 mr :: capTailR))).
Proof.
  pose proof (checkSymA_sound bridge3_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

(* Layer-2 Symbolic Bridges on SymLTok / SymRTok *)

Definition sPopMRTail (sr : list SymRTok) : option (bool * N) :=
  match sr with
  | SMR d :: rTail => if beqSymRList rTail capTailSym then Some (true, d) else None
  | SRC (MR11 k) :: rTail => if beqSymRList rTail capTailSym then Some (false, k) else None
  | _ => None
  end.

Definition mkMRSym (isSym : bool) (d : N) : SymRTok :=
  if isSym then SMR d else SRC (MR11 d).

Lemma sPopMRTail_some {sr : list SymRTok} {isSym : bool} {d : N}
  (h : sPopMRTail sr = Some (isSym, d)) :
  sr = mkMRSym isSym d :: capTailSym.
Proof.
  destruct sr as [| [t | d' | ?] rTail]; try discriminate.
  - destruct t as [? | ? | ? | k | ?]; try discriminate.
    cbn [sPopMRTail] in h. destruct (beqSymRList rTail capTailSym) eqn:hc; [| discriminate].
    inversion h; subst. rewrite (eq_of_beqSymRList rTail capTailSym hc). reflexivity.
  - cbn [sPopMRTail] in h. destruct (beqSymRList rTail capTailSym) eqn:hc; [| discriminate].
    inversion h; subst. rewrite (eq_of_beqSymRList rTail capTailSym hc). reflexivity.
Qed.

Lemma evalSymR_mkMRSym (isSym : bool) (d vr v2 : N) :
  evalSymR vr v2 (mkMRSym isSym d :: capTailSym) =
  MR11 (if isSym then vr + d else d) :: capTailR.
Proof. destruct isSym; reflexivity. Qed.

Definition sStepBridgesB0 (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  match opt_bind (stripSymRC [R0 9; R1 0] sr) sPopMRTail, stripSymLC h10Top sl with
  | Some (isSym, d), Some afterH10 =>
    Some (MB0, SLC (LD 5) :: afterH10, map SRC bridgeH10OutTop ++ (mkMRSym isSym d :: capTailSym))
  | _, _ =>
    match stripSymLC [L0 0; LD1 5; LD 5] sl with
    | None => None
    | Some restL =>
      match opt_bind (stripSymRC bridge0aPfx sr) sPopMRTail with
      | Some (isSym, d) =>
        Some (MB0, map SLC h10Top ++ restL,
              SRC (R0 9) :: SRC (R1 0) :: mkMRSym isSym (d + 1) :: capTailSym)
      | None =>
        match opt_bind (stripSymRC bridge1Pfx sr) sPopMRTail with
        | Some (isSym, d) =>
          Some (MB0, SLC (LD 5) :: restL, map SRC bridge1OutTop ++ (mkMRSym isSym d :: capTailSym))
        | None =>
          match opt_bind (stripSymRC bridge2Pfx sr) sPopMRTail with
          | Some (isSym, d) =>
            Some (MB0, SLC (LD 5) :: restL, map SRC bridge2OutTop ++ (mkMRSym isSym d :: capTailSym))
          | None =>
            match opt_bind (stripSymRC bridge3Pfx sr) sPopMRTail with
            | Some (isSym, d) =>
              Some (MB0, SLC (LD 5) :: restL, map SRC bridge3OutTop ++ (mkMRSym isSym d :: capTailSym))
            | None => None
            end
          end
        end
      end
    end
  end.

Lemma stripSymRC_bind_sPopMRTail {pfx : list RTok} {sr : list SymRTok} {isSym : bool} {d : N}
  (h : opt_bind (stripSymRC pfx sr) sPopMRTail = Some (isSym, d)) :
  sr = map SRC pfx ++ (mkMRSym isSym d :: capTailSym).
Proof.
  destruct (stripSymRC pfx sr) as [rAfter |] eqn:hs; [cbn [opt_bind] in h | discriminate].
  rewrite (stripSymRC_some pfx sr rAfter hs), (sPopMRTail_some h). reflexivity.
Qed.

Lemma sStepBridgesB0_sound {sl : list SymLTok} {sr : list SymRTok}
  {m' : Mode} {sl' : list SymLTok} {sr' : list SymRTok}
  (h : sStepBridgesB0 sl sr = Some (m', sl', sr')) :
  SymReached MB0 sl sr m' sl' sr'.
Proof.
  unfold sStepBridgesB0 in h.
  assert (hcap_cases :
    (match stripSymLC [L0 0; LD1 5; LD 5] sl with
     | None => None
     | Some restL =>
       match opt_bind (stripSymRC bridge0aPfx sr) sPopMRTail with
       | Some (isSym, d) =>
         Some (MB0, map SLC h10Top ++ restL,
               SRC (R0 9) :: SRC (R1 0) :: mkMRSym isSym (d + 1) :: capTailSym)
       | None =>
         match opt_bind (stripSymRC bridge1Pfx sr) sPopMRTail with
         | Some (isSym, d) =>
           Some (MB0, SLC (LD 5) :: restL, map SRC bridge1OutTop ++ (mkMRSym isSym d :: capTailSym))
         | None =>
           match opt_bind (stripSymRC bridge2Pfx sr) sPopMRTail with
           | Some (isSym, d) =>
             Some (MB0, SLC (LD 5) :: restL, map SRC bridge2OutTop ++ (mkMRSym isSym d :: capTailSym))
           | None =>
             match opt_bind (stripSymRC bridge3Pfx sr) sPopMRTail with
             | Some (isSym, d) =>
               Some (MB0, SLC (LD 5) :: restL, map SRC bridge3OutTop ++ (mkMRSym isSym d :: capTailSym))
             | None => None
             end
           end
         end
       end
     end) = Some (m', sl', sr') -> SymReached MB0 sl sr m' sl' sr').
  { intro hc.
    destruct (stripSymLC [L0 0; LD1 5; LD 5] sl) as [restL |] eqn:hl; [| discriminate].
    rewrite (stripSymLC_some [L0 0; LD1 5; LD 5] sl restL hl).
    destruct (opt_bind (stripSymRC bridge0aPfx sr) sPopMRTail) as [[isSym d] |] eqn:hb0.
    - injection hc as <- <- <-. rewrite (stripSymRC_bind_sPopMRTail hb0).
      intros vr v2 v3 v4 rest.
      rewrite !evalSymL_map_c, evalSymR_map_c.
      destruct isSym; cbn [mkMRSym map app evalSymL evalSymR capTailSym].
      + replace (vr + (d + 1)) with ((vr + d) + 1) by lia.
        exact (bridge0a_concrete (vr + d) (evalSymL v2 v3 v4 restL rest)).
      + exact (bridge0a_concrete d (evalSymL v2 v3 v4 restL rest)).
    - destruct (opt_bind (stripSymRC bridge1Pfx sr) sPopMRTail) as [[isSym d] |] eqn:hb1.
      + injection hc as <- <- <-. rewrite (stripSymRC_bind_sPopMRTail hb1).
        intros vr v2 v3 v4 rest.
        rewrite evalSymR_map_c.
        destruct isSym; cbn [mkMRSym map app evalSymL evalSymR capTailSym].
        * exact (bridge1_concrete (vr + d) (evalSymL v2 v3 v4 restL rest)).
        * exact (bridge1_concrete d (evalSymL v2 v3 v4 restL rest)).
      + destruct (opt_bind (stripSymRC bridge2Pfx sr) sPopMRTail) as [[isSym d] |] eqn:hb2.
        * injection hc as <- <- <-. rewrite (stripSymRC_bind_sPopMRTail hb2).
          intros vr v2 v3 v4 rest.
          rewrite evalSymR_map_c.
          destruct isSym; cbn [mkMRSym map app evalSymL evalSymR capTailSym].
          -- exact (bridge2_concrete (vr + d) (evalSymL v2 v3 v4 restL rest)).
          -- exact (bridge2_concrete d (evalSymL v2 v3 v4 restL rest)).
        * destruct (opt_bind (stripSymRC bridge3Pfx sr) sPopMRTail) as [[isSym d] |] eqn:hb3; [| discriminate].
          injection hc as <- <- <-. rewrite (stripSymRC_bind_sPopMRTail hb3).
          intros vr v2 v3 v4 rest.
          rewrite evalSymR_map_c.
          destruct isSym; cbn [mkMRSym map app evalSymL evalSymR capTailSym].
          -- exact (bridge3_concrete (vr + d) (evalSymL v2 v3 v4 restL rest)).
          -- exact (bridge3_concrete d (evalSymL v2 v3 v4 restL rest)). }
  destruct (opt_bind (stripSymRC [R0 9; R1 0] sr) sPopMRTail) as [[isSym d] |] eqn:hr9;
    [| exact (hcap_cases h)].
  destruct (stripSymLC h10Top sl) as [afterH10 |] eqn:hh10;
    [| exact (hcap_cases h)].
  injection h as <- <- <-.
  rewrite (stripSymRC_bind_sPopMRTail hr9), (stripSymLC_some h10Top sl afterH10 hh10).
  intros vr v2 v3 v4 rest.
  rewrite evalSymL_map_c, evalSymR_map_c.
  destruct isSym; cbn [mkMRSym map app evalSymL evalSymR capTailSym].
  - exact (bridgeH10_concrete (vr + d) (evalSymL v2 v3 v4 afterH10 rest)).
  - exact (bridgeH10_concrete d (evalSymL v2 v3 v4 afterH10 rest)).
Qed.

Definition symStepB (m : Mode) (sl0 : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  let sl := sNormB0W3 m sl0 sr in
  match m with
  | MDL => sStepDL sl sr
  | MB0 =>
    match sStepBridgesB0 sl sr with
    | Some res => Some res
    | None =>
      match sStepMotifB0 sl sr with
      | Some res => Some res
      | None => sStepB0Base sl sr
      end
    end
  end.

Definition symStepBOpt (st : option (Mode * list SymLTok * list SymRTok)) :
  option (Mode * list SymLTok * list SymRTok) :=
  match st with
  | None => None
  | Some (m, sl, sr) => symStepB m sl sr
  end.

Definition symRunB (steps : positive) (m : Mode) (sl : list SymLTok) (sr : list SymRTok) :
  option (Mode * list SymLTok * list SymRTok) :=
  Pos.iter symStepBOpt (Some (m, sl, sr)) steps.

Definition checkSymB (steps : positive) (m : Mode) (sl : list SymLTok) (sr : list SymRTok)
  (m' : Mode) (sl' : list SymLTok) (sr' : list SymRTok) : bool :=
  match symRunB steps m sl sr with
  | None => false
  | Some (rm, rsl, rsr) =>
    beqMode rm m' && beqSymLList rsl sl' && beqSymRList rsr sr'
  end.

Lemma symStepB_sound {m m' : Mode} {sl0 sl' : list SymLTok} {sr sr' : list SymRTok}
  (h : symStepB m sl0 sr = Some (m', sl', sr')) :
  SymReached m sl0 sr m' sl' sr'.
Proof.
  assert (hraw : SymReached m (sNormB0W3 m sl0 sr) sr m' sl' sr').
  { unfold symStepB in h. destruct m.
    - destruct (sStepBridgesB0 (sNormB0W3 MB0 sl0 sr) sr) as [res |] eqn:hb.
      + inversion h; subst. exact (sStepBridgesB0_sound hb).
      + destruct (sStepMotifB0 (sNormB0W3 MB0 sl0 sr) sr) as [res |] eqn:hm.
        * inversion h; subst. exact (sStepMotifB0_sound hm).
        * exact (sStepB0Base_sound h).
    - exact (sStepDL_sound h). }
  intros vr v2 v3 v4 rest.
  rewrite <- (encodeBase_core_congr m (eL_sNormB0W3 m sl0 sr v2 v3 v4 rest) eq_refl).
  exact (hraw vr v2 v3 v4 rest).
Qed.

Lemma iter_symStepBOpt_none (p : positive) : Pos.iter symStepBOpt None p = None.
Proof. induction p as [p IH | p IH |]; cbn [Pos.iter]; rewrite ?IH; reflexivity. Qed.

Lemma symRunB_sound (steps : positive) :
  forall {m0 m rm : Mode} {sl0 sl rsl : list SymLTok} {sr0 sr rsr : list SymRTok},
    SymReached m0 sl0 sr0 m sl sr ->
    Pos.iter symStepBOpt (Some (m, sl, sr)) steps = Some (rm, rsl, rsr) ->
    SymReached m0 sl0 sr0 rm rsl rsr.
Proof.
  induction steps as [p IH | p IH |]; intros m0 m rm sl0 sl rsl sr0 sr rsr hpre hr;
    cbn [Pos.iter] in hr.
  - destruct (Pos.iter symStepBOpt (Some (m, sl, sr)) p) as [[[m1 sl1] sr1] |] eqn:hp1;
      [| rewrite iter_symStepBOpt_none in hr; discriminate].
    destruct (Pos.iter symStepBOpt (Some (m1, sl1, sr1)) p) as [[[m2 sl2] sr2] |] eqn:hp2;
      [| discriminate].
    exact (symReached_trans (IH _ _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ _ hpre hp1) hp2)
             (symStepB_sound hr)).
  - destruct (Pos.iter symStepBOpt (Some (m, sl, sr)) p) as [[[m1 sl1] sr1] |] eqn:hp1;
      [| rewrite iter_symStepBOpt_none in hr; discriminate].
    exact (IH _ _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ _ hpre hp1) hr).
  - exact (symReached_trans hpre (symStepB_sound hr)).
Qed.

Lemma checkSymB_sound {steps : positive} {m m' : Mode} {sl sl' : list SymLTok} {sr sr' : list SymRTok}
  (h : checkSymB steps m sl sr m' sl' sr' = true) :
  SymReached m sl sr m' sl' sr'.
Proof.
  unfold checkSymB, symRunB in h.
  destruct (Pos.iter symStepBOpt (Some (m, sl, sr)) steps) as [[[rm rsl] rsr] |] eqn:hrun;
    [| discriminate].
  apply andb_prop in h. destruct h as [h hsr].
  apply andb_prop in h. destruct h as [hm hsl].
  rewrite <- (eq_of_beqMode hm), <- (eq_of_beqSymLList rsl sl' hsl), <- (eq_of_beqSymRList rsr sr' hsr).
  exact (symRunB_sound steps (symReached_refl m sl sr) hrun).
Qed.

(* ========================================================================= *)
(* Section 11: Layer-2 Symbolic Proofs & 7 Quadratic Countdown Eras          *)
(* ========================================================================= *)

Definition era2Mid176L : list SymLTok :=
  [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
   SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
   SLC (LD 7); SLC (LD 3); SLC (LD 7); SLC (LD 3); SLC (L0 0); SLC (LD 5);
   SLC (LD 3); SLC (L0 3); SLC (LD1 0); SLC (L0 0); SLC (LD1 0);
   SLC (LD 7); SLC (LD 7); SM3 9].

Lemma era2Head_chk :
  checkSymB 176%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
     SLC (L0 3); SLC (LD 9); SLC (LD 7); SM3 10]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0 era2Mid176L
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era2Tail_chk :
  checkSymB 3635%positive MB0 era2Mid176L
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 7;
     SLC (L0 3); SLC (LD 9); SLC (LD 7); SM3 0]
    [SRC (R0 9); SRC (R1 0); SMR 19; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era3a_chk :
  checkSymB 6683%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 1;
     SLC (LD 7); SLC (LD 3); SLC (LD1 7); SLC (LD 9); SLC (L0 3); SLC (LD1 1); SM4 44]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 8;
     SLC (LD 7); SLC (LD 3); SLC (LD1 7); SLC (LD 9); SLC (L0 3); SLC (LD1 1); SM4 0]
    [SRC (R0 9); SRC (R1 0); SMR 35; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era3b_chk :
  checkSymB 1071%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
     SLC (LD 7); SLC (L0 0); SLC (LD1 1); SM4 7]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 3;
     SLC (LD 7); SLC (L0 0); SLC (LD1 1); SM4 0]
    [SRC (R0 9); SRC (R1 0); SMR 6; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era3c_chk :
  checkSymB 1071%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
     SLC (LD 7); SLC (LD 3); SLC (LD1 3); SLC (LD 5); SLC (LD1 3); SM4 7]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 3;
     SLC (LD 7); SLC (LD 3); SLC (LD1 3); SLC (LD 5); SLC (LD1 3); SM4 0]
    [SRC (R0 9); SRC (R1 0); SMR 6; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era4a_chk :
  checkSymB 135%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 1;
     SLC (LD 7); SLC (LD 3); SLC (LD1 10); SLC (LD 4); SLC (LD1 0);
     SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0)]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 0;
     SLC (LD 7); SLC (LD 3); SLC (LD1 10); SLC (LD 4); SLC (LD1 0);
     SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0); SM4P 1]
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era4b_chk :
  checkSymB 135%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
     SLC (LD 7); SLC (LD 3); SLC (LD1 1); SLC (LD 4); SLC (L0 4);
     SLC (LD 3); SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0)]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 1;
     SLC (LD 7); SLC (LD 3); SLC (LD1 1); SLC (LD 4); SLC (L0 4);
     SLC (LD 3); SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0); SM4P 1]
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era4aEnd_chk :
  checkSymB 988%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SLC (M2L 0);
     SLC (LD 7); SLC (LD 3); SLC (LD1 10); SLC (LD 4); SLC (LD1 0);
     SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0)]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 2); SLC (L0 1); SLC (LD 5); SLC (LD1 0); SLC (L0 2); SLC (LD1 0);
     SLC (L0 0); SLC (LD 7); SLC (L0 1); SLC (LD1 0); SLC (L0 0); SLC (LD 7);
     SLC (L0 2); SLC (LD1 0); SLC (L0 4); SLC (LD1 0); SLC (L0 2); SLC (LD1 0);
     SLC (L0 2); SLC (LD1 0); SM4P 5]
    [SRC (R0 4); SMR 2; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era4bEnd_chk :
  checkSymB 987%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SLC (M2L 1);
     SLC (LD 7); SLC (LD 3); SLC (LD1 1); SLC (LD 4); SLC (L0 4);
     SLC (LD 3); SLC (L0 0); SLC (LD 3); SLC (L0 0); SLC (LD1 0)]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 2); SLC (L0 1); SLC (LD 5); SLC (LD1 0); SLC (L0 2); SLC (LD1 0);
     SLC (L0 0); SLC (LD1 1); SLC (LD 9); SLC (L0 0); SLC (LD 7); SLC (LD1 1);
     SLC (LD 9); SLC (L0 0); SLC (LD 7); SLC (L0 2); SLC (LD 3); SLC (L0 0);
     SLC (LD 3); SLC (L0 0); SLC (LD1 0); SM4P 5]
    [SRC (R0 4); SMR 3; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma postMR11Head_chk :
  checkSymB 4241%positive MB0
    [SLC (LD 2); SLC (L0 1); SM3 16]
    [SRC (R0 4); SRC (MR11 0); SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SLC (M2L 2);
     SLC (LD 7); SLC (LD 3); SLC (LD 7); SLC (LD 3); SLC (L0 0); SLC (LD 5);
     SLC (LD 3); SLC (L0 3); SLC (LD1 0); SLC (L0 0); SLC (LD1 0);
     SLC (LD 7); SLC (LD 7); SM3 9]
    [SRC (R0 9); SRC (R1 0); SRC (MR11 10); SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era1_loop :
  forall (k : N) (aft : list LTok),
    encodeBase (Core MB0 (LD 2 :: L0 1 :: aft) (rc4Of (k + 1))) -[ tm ]->*
    encodeBase (Core MB0 (LD 2 :: L0 1 :: pushM3L k aft) (rc4Of 0)).
Proof.
  intro k; pattern k; apply N.peano_ind.
  - intro aft; exact (era1_step_concrete 0 aft).
  - intros m IH aft.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era1_step_concrete (m + 1) aft) as h1.
    pose proof (IH (pushM3L 0 aft)) as h2.
    rewrite (pushM3L_pushM3L m 0 aft) in h2.
    replace (m + 1 + 0) with (m + 1) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era2_step_concrete (mr d2 v3 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era2MidTop ++ (M3L (v3 + 10) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 7) :: era2MidTop ++ (M3L v3 :: rest))) (rc6Of (mr + 19))).
Proof.
  pose proof (symReached_trans (checkSymB_sound era2Head_chk) (checkSymB_sound era2Tail_chk) mr d2 v3 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v3 + 0) with v3 in hr by lia.
  exact hr.
Qed.

Lemma era2_loop :
  forall (q' mr d2 rem : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era2MidTop ++ (M3L (rem + 10 * (q' + 1)) :: rest))) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2 + 5 * (q' + 1)) :: era2MidTop ++ (M3L rem :: rest))) (rc6Of (mr + 19 * (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr d2 rem rest.
    change (0 + 1) with 1.
    replace (10 * 1) with 10 by lia.
    replace (d2 + 2 + 5 * 1) with (d2 + 7) by lia.
    replace (mr + 19 * 1) with (mr + 19) by lia.
    exact (era2_step_concrete mr d2 rem rest).
  - intros m IH mr d2 rem rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era2_step_concrete mr d2 (rem + 10 * (m + 1)) rest) as h1.
    pose proof (IH (mr + 19) (d2 + 5) rem rest) as h2.
    replace (rem + 10 * (m + 1) + 10) with (rem + 10 * (m + 1 + 1)) in h1 by lia.
    replace (d2 + 7) with (d2 + 5 + 2) in h1 by lia.
    replace (d2 + 5 + 2 + 5 * (m + 1)) with (d2 + 2 + 5 * (m + 1 + 1)) in h2 by lia.
    replace (mr + 19 + 19 * (m + 1)) with (mr + 19 * (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era3a_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 1) :: era3aMidTop ++ (M4L (v4 + 44) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 8) :: era3aMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 35))).
Proof.
  pose proof (checkSymB_sound era3a_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era3a_loop :
  forall (q' mr d2 rem : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 1) :: era3aMidTop ++ (M4L (rem + 44 * (q' + 1)) :: rest))) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 1 + 7 * (q' + 1)) :: era3aMidTop ++ (M4L rem :: rest))) (rc6Of (mr + 35 * (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr d2 rem rest.
    change (0 + 1) with 1.
    replace (44 * 1) with 44 by lia.
    replace (d2 + 1 + 7 * 1) with (d2 + 8) by lia.
    replace (mr + 35 * 1) with (mr + 35) by lia.
    exact (era3a_step_concrete mr d2 rem rest).
  - intros m IH mr d2 rem rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era3a_step_concrete mr d2 (rem + 44 * (m + 1)) rest) as h1.
    pose proof (IH (mr + 35) (d2 + 7) rem rest) as h2.
    replace (rem + 44 * (m + 1) + 44) with (rem + 44 * (m + 1 + 1)) in h1 by lia.
    replace (d2 + 8) with (d2 + 7 + 1) in h1 by lia.
    replace (d2 + 7 + 1 + 7 * (m + 1)) with (d2 + 1 + 7 * (m + 1 + 1)) in h2 by lia.
    replace (mr + 35 + 35 * (m + 1)) with (mr + 35 * (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era3b_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3bMidTop ++ (M4L (v4 + 7) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 3) :: era3bMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 6))).
Proof.
  pose proof (checkSymB_sound era3b_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era3b_loop :
  forall (q' mr d2 rem : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3bMidTop ++ (M4L (rem + 7 * (q' + 1)) :: rest))) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2 + (q' + 1)) :: era3bMidTop ++ (M4L rem :: rest))) (rc6Of (mr + 6 * (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr d2 rem rest.
    change (0 + 1) with 1.
    replace (7 * 1) with 7 by lia.
    replace (d2 + 2 + 1) with (d2 + 3) by lia.
    replace (mr + 6 * 1) with (mr + 6) by lia.
    exact (era3b_step_concrete mr d2 rem rest).
  - intros m IH mr d2 rem rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era3b_step_concrete mr d2 (rem + 7 * (m + 1)) rest) as h1.
    pose proof (IH (mr + 6) (d2 + 1) rem rest) as h2.
    replace (rem + 7 * (m + 1) + 7) with (rem + 7 * (m + 1 + 1)) in h1 by lia.
    replace (d2 + 3) with (d2 + 1 + 2) in h1 by lia.
    replace (d2 + 1 + 2 + (m + 1)) with (d2 + 2 + (m + 1 + 1)) in h2 by lia.
    replace (mr + 6 + 6 * (m + 1)) with (mr + 6 * (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era3c_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3cMidTop ++ (M4L (v4 + 7) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 3) :: era3cMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 6))).
Proof.
  pose proof (checkSymB_sound era3c_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era3c_loop :
  forall (q' mr d2 rem : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3cMidTop ++ (M4L (rem + 7 * (q' + 1)) :: rest))) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2 + (q' + 1)) :: era3cMidTop ++ (M4L rem :: rest))) (rc6Of (mr + 6 * (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr d2 rem rest.
    change (0 + 1) with 1.
    replace (7 * 1) with 7 by lia.
    replace (d2 + 2 + 1) with (d2 + 3) by lia.
    replace (mr + 6 * 1) with (mr + 6) by lia.
    exact (era3c_step_concrete mr d2 rem rest).
  - intros m IH mr d2 rem rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era3c_step_concrete mr d2 (rem + 7 * (m + 1)) rest) as h1.
    pose proof (IH (mr + 6) (d2 + 1) rem rest) as h2.
    replace (rem + 7 * (m + 1) + 7) with (rem + 7 * (m + 1 + 1)) in h1 by lia.
    replace (d2 + 3) with (d2 + 1 + 2) in h1 by lia.
    replace (d2 + 1 + 2 + (m + 1)) with (d2 + 2 + (m + 1 + 1)) in h2 by lia.
    replace (mr + 6 + 6 * (m + 1)) with (mr + 6 * (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era4a_step_concrete (mr v2 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 1) :: era4aMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L v2 :: era4aMidTop ++ pushM4L 1 rest)) (rc6Of (mr + 1))).
Proof.
  pose proof (checkSymB_sound era4a_chk mr v2 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v2 + 0) with v2 in hr by lia.
  exact hr.
Qed.

Lemma era4a_loop :
  forall (q' mr : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (q' + 1) :: era4aMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L 0 :: era4aMidTop ++ pushM4L (2 * q' + 1) rest)) (rc6Of (mr + (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr rest.
    change (2 * 0 + 1) with 1.
    exact (era4a_step_concrete mr 0 rest).
  - intros m IH mr rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era4a_step_concrete mr (m + 1) rest) as h1.
    pose proof (IH (mr + 1) (pushM4L 1 rest)) as h2.
    rewrite (pushM4L_pushM4L (2 * m + 1) 1 rest) in h2.
    replace (2 * m + 1 + 1 + 1) with (2 * (m + 1) + 1) in h2 by lia.
    replace (mr + 1 + (m + 1)) with (mr + (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era4b_step_concrete (mr v2 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 2) :: era4bMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 1) :: era4bMidTop ++ pushM4L 1 rest)) (rc6Of (mr + 1))).
Proof.
  pose proof (checkSymB_sound era4b_chk mr v2 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma era4b_loop :
  forall (q' mr : N) (rest : list LTok),
    encodeBase (Core MB0 (h10Top ++ (M2L (q' + 2) :: era4bMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
    encodeBase (Core MB0 (h10Top ++ (M2L 1 :: era4bMidTop ++ pushM4L (2 * q' + 1) rest)) (rc6Of (mr + (q' + 1)))).
Proof.
  intro q'; pattern q'; apply N.peano_ind.
  - intros mr rest.
    change (2 * 0 + 1) with 1; change (0 + 2) with 2; change (0 + 1) with 1.
    exact (era4b_step_concrete mr 0 rest).
  - intros m IH mr rest.
    replace (N.succ m) with (m + 1) by lia.
    pose proof (era4b_step_concrete mr (m + 1) rest) as h1.
    pose proof (IH (mr + 1) (pushM4L 1 rest)) as h2.
    replace (m + 1 + 1) with (m + 2) in h1 by lia.
    rewrite (pushM4L_pushM4L (2 * m + 1) 1 rest) in h2.
    replace (2 * m + 1 + 1 + 1) with (2 * (m + 1) + 1) in h2 by lia.
    replace (mr + 1 + (m + 1)) with (mr + (m + 1 + 1)) in h2 by lia.
    exact (rs_trans h1 h2).
Qed.

Lemma era4aEnd_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L 0 :: era4aMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (era4aEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 2))).
Proof.
  pose proof (checkSymB_sound era4aEnd_chk mr 0 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma era4bEnd_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L 1 :: era4bMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (era4bEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 3))).
Proof.
  pose proof (checkSymB_sound era4bEnd_chk mr 0 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma postMR11_concrete (m3Rem : N) (rest : list LTok) :
  encodeBase (Core MB0 (LD 2 :: L0 1 :: M3L (m3Rem + 16) :: rest) (rc4Of 0)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L 7 :: era2MidTop ++ (M3L m3Rem :: rest))) (rc6Of 28)).
Proof.
  pose proof (checkSymB_sound postMR11Head_chk 0 0 m3Rem 0 rest) as hr1.
  pose proof (checkSymB_sound era2Tail_chk 9 0 m3Rem 0 rest) as hr2.
  cbn [era2Mid176L evalSymL evalSymR] in hr1, hr2.
  replace (m3Rem + 0) with m3Rem in hr2 by lia.
  exact (rs_trans hr1 hr2).
Qed.

(* ========================================================================= *)
(* Section 12: stepV3, stepNext, Pos.iter Soundness & Halting Theorem        *)
(* ========================================================================= *)

Definition popMRTail (r : list RTok) : option N :=
  match popMR11 r with
  | Some (mr, rTail) => if beqRList rTail capTailR then Some mr else None
  | None => None
  end.

Definition tryRC6Era2 (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era2MidTop afterM2 with
  | Some afterMid =>
    if 2 <=? m2 then
      match popM3L afterMid with
      | Some (m3, rest) =>
        let q := m3 / 10 in
        if 1 <=? q then
          let rem := m3 mod 10 in
          Some (Core MB0 (h10Top ++ (M2L (m2 + 5 * q) :: era2MidTop ++ (M3L rem :: rest)))
            (rc6Of (mr + 19 * q)))
        else None
      | None => None
      end
    else None
  | None => None
  end.

Definition tryRC6Era3a (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era3aMidTop afterM2 with
  | Some afterMid =>
    if 1 <=? m2 then
      match popM4L afterMid with
      | Some (m4, rest) =>
        let q := m4 / 44 in
        if 1 <=? q then
          let rem := m4 mod 44 in
          Some (Core MB0 (h10Top ++ (M2L (m2 + 7 * q) :: era3aMidTop ++ (M4L rem :: rest)))
            (rc6Of (mr + 35 * q)))
        else None
      | None => None
      end
    else None
  | None => None
  end.

Definition tryRC6Era3b (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era3bMidTop afterM2 with
  | Some afterMid =>
    if 2 <=? m2 then
      match popM4L afterMid with
      | Some (m4, rest) =>
        let q := m4 / 7 in
        if 1 <=? q then
          let rem := m4 mod 7 in
          Some (Core MB0 (h10Top ++ (M2L (m2 + q) :: era3bMidTop ++ (M4L rem :: rest)))
            (rc6Of (mr + 6 * q)))
        else None
      | None => None
      end
    else None
  | None => None
  end.

Definition tryRC6Era3c (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era3cMidTop afterM2 with
  | Some afterMid =>
    if 2 <=? m2 then
      match popM4L afterMid with
      | Some (m4, rest) =>
        let q := m4 / 7 in
        if 1 <=? q then
          let rem := m4 mod 7 in
          Some (Core MB0 (h10Top ++ (M2L (m2 + q) :: era3cMidTop ++ (M4L rem :: rest)))
            (rc6Of (mr + 6 * q)))
        else None
      | None => None
      end
    else None
  | None => None
  end.

Definition tryRC6Era4a (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era4aMidTop afterM2 with
  | None => None
  | Some rest =>
    if m2 =? 0 then
      Some (Core MB0 (era4aEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 2)))
    else
      let q' := m2 - 1 in
      Some (Core MB0 (h10Top ++ (M2L 0 :: era4aMidTop ++ pushM4L (2 * q' + 1) rest))
        (rc6Of (mr + m2)))
  end.

Definition tryRC6Era4b (mr m2 : N) (afterM2 : list LTok) : option BaseState :=
  match stripLPrefix era4bMidTop afterM2 with
  | None => None
  | Some rest =>
    if m2 =? 0 then None
    else if m2 =? 1 then
      Some (Core MB0 (era4bEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 3)))
    else
      let q' := m2 - 2 in
      Some (Core MB0 (h10Top ++ (M2L 1 :: era4bMidTop ++ pushM4L (2 * q' + 1) rest))
        (rc6Of (mr + (q' + 1))))
  end.

Definition tryRC6All (mr : N) (afterH10 : list LTok) : option BaseState :=
  match popM2L afterH10 with
  | None => None
  | Some (m2, afterM2) =>
    match tryRC6Era2 mr m2 afterM2 with
    | Some res => Some res
    | None =>
      match tryRC6Era3a mr m2 afterM2 with
      | Some res => Some res
      | None =>
        match tryRC6Era3b mr m2 afterM2 with
        | Some res => Some res
        | None =>
          match tryRC6Era3c mr m2 afterM2 with
          | Some res => Some res
          | None =>
            match tryRC6Era4a mr m2 afterM2 with
            | Some res => Some res
            | None => tryRC6Era4b mr m2 afterM2
            end
          end
        end
      end
    end
  end.

Definition stepRC6H10 (mr : N) (afterH10 : list LTok) : BaseState :=
  match tryRC6All mr afterH10 with
  | Some res => res
  | None => Core MB0 (LD 5 :: afterH10) (bridgeH10OutTop ++ (MR11 mr :: capTailR))
  end.

Definition stepCapBridgeB0 (l : list LTok) (r : list RTok) : option BaseState :=
  match stripLPrefix [L0 0; LD1 5; LD 5] l with
  | None => None
  | Some rest =>
    match opt_bind (stripRPrefix bridge0aPfx r) popMRTail with
    | Some mr => Some (Core MB0 (h10Top ++ rest) (rc6Of (mr + 1)))
    | None =>
      match opt_bind (stripRPrefix bridge1Pfx r) popMRTail with
      | Some mr => Some (Core MB0 (LD 5 :: rest) (bridge1OutTop ++ (MR11 mr :: capTailR)))
      | None =>
        match opt_bind (stripRPrefix bridge2Pfx r) popMRTail with
        | Some mr => Some (Core MB0 (LD 5 :: rest) (bridge2OutTop ++ (MR11 mr :: capTailR)))
        | None =>
          match opt_bind (stripRPrefix bridge3Pfx r) popMRTail with
          | Some mr => Some (Core MB0 (LD 5 :: rest) (bridge3OutTop ++ (MR11 mr :: capTailR)))
          | None => None
          end
        end
      end
    end
  end.

Definition tryRC6TopB0 (l : list LTok) (r : list RTok) : option BaseState :=
  match opt_bind (stripRPrefix [R0 9; R1 0] r) popMRTail, stripLPrefix h10Top l with
  | Some mr, Some afterH10 => Some (stepRC6H10 mr afterH10)
  | _, _ => None
  end.

Definition tryRC4B0 (l : list LTok) (r : list RTok) : option BaseState :=
  match opt_bind (popR0Eq 4 r) popMRTail, stripLPrefix [LD 2; L0 1] l with
  | Some mr, Some afterLD2L01 =>
    if mr =? 0 then
      match popM3L afterLD2L01 with
      | Some (m3, rest) =>
        if 16 <=? m3 then
          let m3Rem := m3 - 16 in
          Some (Core MB0 (h10Top ++ (M2L 7 :: era2MidTop ++ (M3L m3Rem :: rest))) (rc6Of 28))
        else None
      | None => None
      end
    else
      Some (Core MB0 (LD 2 :: L0 1 :: pushM3L (mr - 1) afterLD2L01) (rc4Of 0))
  | _, _ => None
  end.

Definition stepV3 (m : Mode) (l0 : list LTok) (r : list RTok) : BaseState :=
  let l := normB0W3 m l0 r in
  match m with
  | MDL => stepDL l r
  | MB0 =>
    match tryRC6TopB0 l r with
    | Some res => res
    | None =>
      match tryRC4B0 l r with
      | Some res => res
      | None =>
        match stepCapBridgeB0 l r with
        | Some res => res
        | None => stepCoreRaw MB0 l r
        end
      end
    end
  end.

Definition stepNext (s : BaseState) : BaseState :=
  match s with
  | Init0 => Core MB0 [L0 0] []
  | Halt r => Halt r
  | Core m l r => stepV3 m l r
  end.

Lemma popMRTail_some {r : list RTok} {mr : N} (h : popMRTail r = Some mr) :
  r = MR11 mr :: capTailR.
Proof.
  unfold popMRTail in h.
  destruct (popMR11 r) as [[k rTail] |] eqn:hm; [| discriminate].
  destruct (beqRList rTail capTailR) eqn:hb; [| discriminate].
  inversion h; subst.
  rewrite (popMR11_some hm), (eq_of_beqRList rTail capTailR hb). reflexivity.
Qed.

Lemma stripRPrefix_bind_popMRTail {pfx r : list RTok} {mr : N}
  (h : opt_bind (stripRPrefix pfx r) popMRTail = Some mr) :
  r = pfx ++ (MR11 mr :: capTailR).
Proof.
  destruct (stripRPrefix pfx r) as [rAfter |] eqn:hs; [cbn [opt_bind] in h | discriminate].
  rewrite (stripRPrefix_some pfx r rAfter hs), (popMRTail_some h). reflexivity.
Qed.

Lemma popR0Eq4_bind_popMRTail {r : list RTok} {mr : N}
  (h : opt_bind (popR0Eq 4 r) popMRTail = Some mr) :
  r = rc4Of mr.
Proof.
  destruct (popR0Eq 4 r) as [rAfter |] eqn:hs; [cbn [opt_bind] in h | discriminate].
  rewrite (popR0Eq_some hs), (popMRTail_some h). reflexivity.
Qed.

Lemma tryRC6Era2_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era2 mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era2 in h.
  destruct (stripLPrefix era2MidTop afterM2) as [afterMid |] eqn:hs; [| discriminate].
  destruct (2 <=? m2) eqn:hm2; [| discriminate].
  destruct (popM3L afterMid) as [[m3 rest] |] eqn:hm3; [| discriminate].
  destruct (1 <=? m3 / 10) eqn:hq; [| discriminate].
  apply N.leb_le in hm2. apply N.leb_le in hq.
  injection h as <-.
  set (d2 := m2 - 2). set (q' := m3 / 10 - 1).
  assert (ha : afterM2 = era2MidTop ++ (M3L (m3 mod 10 + 10 * (q' + 1)) :: rest)).
  { rewrite (stripLPrefix_some era2MidTop afterM2 afterMid hs), (popM3L_some hm3).
    assert (hm3eq : m3 = m3 mod 10 + 10 * (q' + 1)) by (unfold q'; lia).
    rewrite <- hm3eq; reflexivity. }
  rewrite ha.
  replace m2 with (d2 + 2) by (unfold d2; lia).
  replace (m3 / 10) with (q' + 1) by (unfold q'; lia).
  exact (era2_loop q' mr d2 (m3 mod 10) rest).
Qed.

Lemma tryRC6Era3a_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3a mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era3a in h.
  destruct (stripLPrefix era3aMidTop afterM2) as [afterMid |] eqn:hs; [| discriminate].
  destruct (1 <=? m2) eqn:hm2; [| discriminate].
  destruct (popM4L afterMid) as [[m4 rest] |] eqn:hm4; [| discriminate].
  destruct (1 <=? m4 / 44) eqn:hq; [| discriminate].
  apply N.leb_le in hm2. apply N.leb_le in hq.
  injection h as <-.
  set (d2 := m2 - 1). set (q' := m4 / 44 - 1).
  assert (ha : afterM2 = era3aMidTop ++ (M4L (m4 mod 44 + 44 * (q' + 1)) :: rest)).
  { rewrite (stripLPrefix_some era3aMidTop afterM2 afterMid hs), (popM4L_some hm4).
    assert (hm4eq : m4 = m4 mod 44 + 44 * (q' + 1)) by (unfold q'; lia).
    rewrite <- hm4eq; reflexivity. }
  rewrite ha.
  replace m2 with (d2 + 1) by (unfold d2; lia).
  replace (m4 / 44) with (q' + 1) by (unfold q'; lia).
  exact (era3a_loop q' mr d2 (m4 mod 44) rest).
Qed.

Lemma tryRC6Era3b_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3b mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era3b in h.
  destruct (stripLPrefix era3bMidTop afterM2) as [afterMid |] eqn:hs; [| discriminate].
  destruct (2 <=? m2) eqn:hm2; [| discriminate].
  destruct (popM4L afterMid) as [[m4 rest] |] eqn:hm4; [| discriminate].
  destruct (1 <=? m4 / 7) eqn:hq; [| discriminate].
  apply N.leb_le in hm2. apply N.leb_le in hq.
  injection h as <-.
  set (d2 := m2 - 2). set (q' := m4 / 7 - 1).
  assert (ha : afterM2 = era3bMidTop ++ (M4L (m4 mod 7 + 7 * (q' + 1)) :: rest)).
  { rewrite (stripLPrefix_some era3bMidTop afterM2 afterMid hs), (popM4L_some hm4).
    assert (hm4eq : m4 = m4 mod 7 + 7 * (q' + 1)) by (unfold q'; lia).
    rewrite <- hm4eq; reflexivity. }
  rewrite ha.
  replace m2 with (d2 + 2) by (unfold d2; lia).
  replace (m4 / 7) with (q' + 1) by (unfold q'; lia).
  exact (era3b_loop q' mr d2 (m4 mod 7) rest).
Qed.

Lemma tryRC6Era3c_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3c mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era3c in h.
  destruct (stripLPrefix era3cMidTop afterM2) as [afterMid |] eqn:hs; [| discriminate].
  destruct (2 <=? m2) eqn:hm2; [| discriminate].
  destruct (popM4L afterMid) as [[m4 rest] |] eqn:hm4; [| discriminate].
  destruct (1 <=? m4 / 7) eqn:hq; [| discriminate].
  apply N.leb_le in hm2. apply N.leb_le in hq.
  injection h as <-.
  set (d2 := m2 - 2). set (q' := m4 / 7 - 1).
  assert (ha : afterM2 = era3cMidTop ++ (M4L (m4 mod 7 + 7 * (q' + 1)) :: rest)).
  { rewrite (stripLPrefix_some era3cMidTop afterM2 afterMid hs), (popM4L_some hm4).
    assert (hm4eq : m4 = m4 mod 7 + 7 * (q' + 1)) by (unfold q'; lia).
    rewrite <- hm4eq; reflexivity. }
  rewrite ha.
  replace m2 with (d2 + 2) by (unfold d2; lia).
  replace (m4 / 7) with (q' + 1) by (unfold q'; lia).
  exact (era3c_loop q' mr d2 (m4 mod 7) rest).
Qed.

Lemma tryRC6Era4a_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era4a mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era4a in h.
  destruct (stripLPrefix era4aMidTop afterM2) as [rest |] eqn:hs; [| discriminate].
  rewrite (stripLPrefix_some era4aMidTop afterM2 rest hs).
  destruct (m2 =? 0) eqn:hm2.
  - apply N.eqb_eq in hm2; subst m2. injection h as <-.
    exact (era4aEnd_concrete mr rest).
  - apply N.eqb_neq in hm2. injection h as <-.
    replace m2 with ((m2 - 1) + 1) by lia.
    replace (m2 - 1 + 1 - 1) with (m2 - 1) by lia.
    exact (era4a_loop (m2 - 1) mr rest).
Qed.

Lemma tryRC6Era4b_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era4b mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Era4b in h.
  destruct (stripLPrefix era4bMidTop afterM2) as [rest |] eqn:hs; [| discriminate].
  rewrite (stripLPrefix_some era4bMidTop afterM2 rest hs).
  destruct (m2 =? 0) eqn:hm20; [discriminate |].
  destruct (m2 =? 1) eqn:hm21.
  - apply N.eqb_eq in hm21; subst m2. injection h as <-.
    exact (era4bEnd_concrete mr rest).
  - apply N.eqb_neq in hm20. apply N.eqb_neq in hm21. injection h as <-.
    replace m2 with ((m2 - 2) + 2) at 1 by lia.
    exact (era4b_loop (m2 - 2) mr rest).
Qed.

Lemma tryRC6All_sound {mr : N} {afterH10 : list LTok} {bs' : BaseState}
  (h : tryRC6All mr afterH10 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ afterH10) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6All in h.
  destruct (popM2L afterH10) as [[m2 afterM2] |] eqn:hm2; [| discriminate].
  rewrite (popM2L_some hm2).
  destruct (tryRC6Era2 mr m2 afterM2) as [res |] eqn:h2; [injection h as <-; exact (tryRC6Era2_sound h2) |].
  destruct (tryRC6Era3a mr m2 afterM2) as [res |] eqn:h3a; [injection h as <-; exact (tryRC6Era3a_sound h3a) |].
  destruct (tryRC6Era3b mr m2 afterM2) as [res |] eqn:h3b; [injection h as <-; exact (tryRC6Era3b_sound h3b) |].
  destruct (tryRC6Era3c mr m2 afterM2) as [res |] eqn:h3c; [injection h as <-; exact (tryRC6Era3c_sound h3c) |].
  destruct (tryRC6Era4a mr m2 afterM2) as [res |] eqn:h4a; [injection h as <-; exact (tryRC6Era4a_sound h4a) |].
  exact (tryRC6Era4b_sound h).
Qed.

Lemma stepRC6H10_sound (mr : N) (afterH10 : list LTok) :
  encodeBase (Core MB0 (h10Top ++ afterH10) (rc6Of mr)) -[ tm ]->*
  encodeBase (stepRC6H10 mr afterH10).
Proof.
  unfold stepRC6H10.
  destruct (tryRC6All mr afterH10) as [bs' |] eqn:hall.
  - exact (tryRC6All_sound hall).
  - exact (bridgeH10_concrete mr afterH10).
Qed.

Lemma stepCapBridgeB0_sound {l : list LTok} {r : list RTok} {bs' : BaseState}
  (h : stepCapBridgeB0 l r = Some bs') :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase bs'.
Proof.
  unfold stepCapBridgeB0 in h.
  destruct (stripLPrefix [L0 0; LD1 5; LD 5] l) as [rest |] eqn:hl; [| discriminate].
  rewrite (stripLPrefix_some [L0 0; LD1 5; LD 5] l rest hl).
  destruct (opt_bind (stripRPrefix bridge0aPfx r) popMRTail) as [mr |] eqn:hb0.
  - injection h as <-. rewrite (stripRPrefix_bind_popMRTail hb0).
    exact (bridge0a_concrete mr rest).
  - destruct (opt_bind (stripRPrefix bridge1Pfx r) popMRTail) as [mr |] eqn:hb1.
    + injection h as <-. rewrite (stripRPrefix_bind_popMRTail hb1).
      exact (bridge1_concrete mr rest).
    + destruct (opt_bind (stripRPrefix bridge2Pfx r) popMRTail) as [mr |] eqn:hb2.
      * injection h as <-. rewrite (stripRPrefix_bind_popMRTail hb2).
        exact (bridge2_concrete mr rest).
      * destruct (opt_bind (stripRPrefix bridge3Pfx r) popMRTail) as [mr |] eqn:hb3; [| discriminate].
        injection h as <-. rewrite (stripRPrefix_bind_popMRTail hb3).
        exact (bridge3_concrete mr rest).
Qed.

Lemma tryRC6TopB0_sound {l : list LTok} {r : list RTok} {bs' : BaseState}
  (h : tryRC6TopB0 l r = Some bs') :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6TopB0 in h.
  destruct (opt_bind (stripRPrefix [R0 9; R1 0] r) popMRTail) as [mr |] eqn:hr6; [| discriminate].
  destruct (stripLPrefix h10Top l) as [afterH10 |] eqn:hl10; [| discriminate].
  injection h as <-.
  rewrite (stripRPrefix_bind_popMRTail hr6), (stripLPrefix_some h10Top l afterH10 hl10).
  exact (stepRC6H10_sound mr afterH10).
Qed.

Lemma tryRC4B0_sound {l : list LTok} {r : list RTok} {bs' : BaseState}
  (h : tryRC4B0 l r = Some bs') :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC4B0 in h.
  destruct (opt_bind (popR0Eq 4 r) popMRTail) as [mr |] eqn:hr4; [| discriminate].
  destruct (stripLPrefix [LD 2; L0 1] l) as [afterLD2L01 |] eqn:hl2; [| discriminate].
  rewrite (popR0Eq4_bind_popMRTail hr4).
  destruct (mr =? 0) eqn:hmr0.
  - apply N.eqb_eq in hmr0; subst mr.
    destruct (popM3L afterLD2L01) as [[m3 rest] |] eqn:hm3; [| discriminate].
    destruct (16 <=? m3) eqn:hle; [| discriminate].
    apply N.leb_le in hle. injection h as <-.
    rewrite (stripLPrefix_some [LD 2; L0 1] l afterLD2L01 hl2), (popM3L_some hm3).
    replace m3 with ((m3 - 16) + 16) at 1 by lia.
    exact (postMR11_concrete (m3 - 16) rest).
  - apply N.eqb_neq in hmr0. injection h as <-.
    rewrite (stripLPrefix_some [LD 2; L0 1] l afterLD2L01 hl2).
    replace mr with ((mr - 1) + 1) at 1 by lia.
    exact (era1_loop (mr - 1) afterLD2L01).
Qed.

Lemma stepV3_sound (m : Mode) (l0 : list LTok) (r : list RTok) :
  encodeBase (Core m l0 r) -[ tm ]->* encodeBase (stepV3 m l0 r).
Proof.
  rewrite <- (encodeBase_core_congr m (eL_normB0W3 m l0 r) eq_refl).
  unfold stepV3.
  destruct m.
  - destruct (tryRC6TopB0 (normB0W3 MB0 l0 r) r) as [bs' |] eqn:h6;
      [exact (tryRC6TopB0_sound h6) |].
    destruct (tryRC4B0 (normB0W3 MB0 l0 r) r) as [bs' |] eqn:h4;
      [exact (tryRC4B0_sound h4) |].
    destruct (stepCapBridgeB0 (normB0W3 MB0 l0 r) r) as [bs' |] eqn:hcb;
      [exact (stepCapBridgeB0_sound hcb) |].
    exact (stepCoreRaw_sound_B0 (normB0W3 MB0 l0 r) r).
  - exact (stepDL_sound (normB0W3 MDL l0 r) r).
Qed.

Lemma stepNext_sound (s : BaseState) :
  encodeBase s -[ tm ]->* encodeBase (stepNext s).
Proof.
  destruct s as [| m l r | r].
  - cbn [stepNext].
    refine (chkWin_eq true true 1%nat A true [] [] B true [S1] []
      (const S0) (const S0) (fun _ => eq_refl) (fun _ => eq_refl) eq_refl _ eq_refl).
    cbn [encodeBase encodeCore].
    change (eL [L0 0]) with (S1 >> (S0 >> const S0)).
    rewrite zero_cons_def. reflexivity.
  - exact (stepV3_sound m l r).
  - apply rs_refl.
Qed.

Lemma iter_stepNext_sound (p : positive) :
  forall s : BaseState,
    encodeBase s -[ tm ]->* encodeBase (Pos.iter stepNext s p).
Proof.
  induction p as [p IH | p IH |]; intro s; cbn [Pos.iter].
  - exact (rs_trans (IH s) (rs_trans (IH (Pos.iter stepNext s p)) (stepNext_sound _))).
  - exact (rs_trans (IH s) (IH (Pos.iter stepNext s p))).
  - exact (stepNext_sound s).
Qed.

Definition isHalted (s : BaseState) : bool :=
  match s with
  | Halt _ => true
  | _ => false
  end.

Lemma traj_halted : isHalted (Pos.iter stepNext Init0 467147%positive) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.


Lemma halt_internal : halts tm c0.
Proof.
  pose proof (iter_stepNext_sound 467147%positive Init0) as hreach.
  pose proof traj_halted as hchk.
  destruct (Pos.iter stepNext Init0 467147%positive) as [| ? ? ? | r]; try discriminate.
  exact (evstep_to_halts hreach eq_refl).
Qed.

End Internal.

Theorem halt : halts tm c0.
Proof. exact Internal.halt_internal. Qed.
