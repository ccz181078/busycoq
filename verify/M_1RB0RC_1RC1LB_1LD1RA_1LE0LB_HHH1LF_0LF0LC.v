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

Fixpoint firstSome {T U} (f : T -> option U) (xs : list T) : option U :=
  match xs with
  | [] => None
  | x :: tl => match f x with Some y => Some y | None => firstSome f tl end
  end.

Lemma firstSome_sound {T U} (f : T -> option U) (P : U -> Prop) xs y :
  Forall (fun x => forall z, f x = Some z -> P z) xs ->
  firstSome f xs = Some y -> P y.
Proof.
  induction 1 as [|x xs hx _ IH]; cbn [firstSome]; [discriminate |].
  destruct (f x) as [z|] eqn:h; [intros [= <-]; now apply hx | exact IH].
Qed.

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

(* Both finite windows and stacks with powers use the same ordinary TM step.
   Their readers differ only in which front cells they expose. *)
Definition orient (q : Q) (d : bool) (l r : side) : Q * tape :=
  if d then l {{q}}> r else l <{{q}} r.

Definition View (T : Type) := (Q * bool * T * T)%type.

Definition readStep {T} (readL readR : T -> option (Sym * T))
  (push : Sym -> T -> T) (st : View T) : option (View T) :=
  let '(q, d, l, r) := st in
  let head := if d then opt_bind (readR r) (fun '(a, rt) => Some (a, l, rt))
                 else opt_bind (readL l) (fun '(a, lt) => Some (a, lt, r)) in
  opt_bind head (fun '(a, lt, rt) =>
    match tm (q, a) with
    | Some (w, R, q') => Some (q', true, push w lt, rt)
    | Some (w, L, q') => Some (q', false, lt, push w rt)
    | None => None
    end).

Definition reads {T} (eval : T -> side) (read : T -> option (Sym * T)) :=
  forall x a tl, read x = Some (a, tl) -> eval x = a >> eval tl.

Definition pushes {T} (eval : T -> side) (push : Sym -> T -> T) :=
  forall a tl, eval (push a tl) = a >> eval tl.

Definition evalView {T} (evalL evalR : T -> side) (st : View T) : Q * tape :=
  let '(q, d, l, r) := st in orient q d (evalL l) (evalR r).

Lemma readStep_sound {T} readL readR push (evalL evalR : T -> side)
  (hl : reads evalL readL) (hr : reads evalR readR)
  (pl : pushes evalL push) (pr : pushes evalR push) st out :
  readStep readL readR push st = Some out ->
  evalView evalL evalR st -[ tm ]-> evalView evalL evalR out.
Proof.
  destruct st as [[[q d] l] r]. unfold readStep. destruct d.
  - destruct (readR r) as [[a rt]|] eqn:h; [|discriminate].
    cbn [opt_bind evalView]. rewrite (hr _ _ _ h).
    destruct (tm (q, a)) as [[[w dir] q']|] eqn:ht; [|discriminate].
    destruct dir; intros [= <-]; cbn [evalView]; [rewrite pr | rewrite pl];
      [exact (step_left ht) | exact (step_right ht)].
  - destruct (readL l) as [[a lt]|] eqn:h; [|discriminate].
    cbn [opt_bind evalView]. rewrite (hl _ _ _ h).
    destruct (tm (q, a)) as [[[w dir] q']|] eqn:ht; [|discriminate].
    destruct dir; intros [= <-]; cbn [evalView]; [rewrite pr | rewrite pl];
      [exact (step_left ht) | exact (step_right ht)].
Qed.

Definition evalWin (l r : side) (q : Q) (dR : bool) (ls rs : list Sym) : Q * tape :=
  orient q dR (ls *> l) (rs *> r).

Definition readWin (blank : bool) (xs : list Sym) : option (Sym * list Sym) :=
  match xs with
  | a :: tl => Some (a, tl)
  | [] => if blank then Some (S0, []) else None
  end.

Lemma readWin_reads b s (h : b = true -> s = const S0) :
  reads (fun xs => xs *> s) (readWin b).
Proof.
  intros [|x xs] a tl.
  - destruct b; [|discriminate]. intros [= <- <-].
    specialize (h eq_refl); subst s. exact (eq_sym zero_cons_def).
  - intros [= <- <-]. reflexivity.
Qed.

Definition stepWin (bL bR : bool) := readStep (readWin bL) (readWin bR) (@cons Sym).

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

Lemma stepWin_sound {bL bR : bool} {l r : side}
  (hL : bL = true -> l = const S0) (hR : bR = true -> r = const S0)
  {q q' : Q} {dR dR' : bool} {ls rs ls' rs' : list Sym}
  (hs : stepWin bL bR (q, dR, ls, rs) = Some (q', dR', ls', rs')) :
  evalWin l r q dR ls rs -[ tm ]-> evalWin l r q' dR' ls' rs'.
Proof.
  exact (readStep_sound (readWin bL) (readWin bR) (@cons Sym)
    (fun xs => xs *> l) (fun xs => xs *> r)
    (readWin_reads _ _ hL) (readWin_reads _ _ hR)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) _ _ hs).
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

(* [Some m] is a completed macro; [None] hands off to the DL fold.
   The outer option can also fail when a symbolic stack is opaque. *)
Definition B0Prep (L R : Type) := (option Mode * list L * list R)%type.

Record B0Ops (L R : Type) := {
  b0ReadL : list L -> option (option (LHead * list L));
  b0Bump : nat -> list L -> option (list L);
  b0Peel : N -> list L -> list L;
  b0Zeros : N -> list L -> list L;
  b0Add : N -> list R -> option (list R);
  b0PushR0 : N -> list R -> list R;
  b0LitL : LTok -> L;
  b0LitR : RTok -> R
}.
Arguments b0ReadL {L R}.
Arguments b0Bump {L R}.
Arguments b0Peel {L R}.
Arguments b0Zeros {L R}.
Arguments b0Add {L R}.
Arguments b0PushR0 {L R}.
Arguments b0LitL {L R}.
Arguments b0LitR {L R}.

Definition b0Q0 {L R} (ops : B0Ops L R) (l : list L) (r : list R) :
  option (B0Prep L R) :=
  match b0ReadL ops l with
  | None => None
  | Some None => Some (Some MDL, [], b0LitR ops (R0 0) :: r)
  | Some (Some (LHL0 v, rest)) =>
    opt_bind (b0Add ops 1 r) (fun r' => Some (Some MB0, b0Peel ops v rest, r'))
  | Some (Some (LHLD v, rest)) =>
    opt_bind (b0Add ops (v + 2) r) (fun r' => Some (Some MB0, rest, r'))
  end.

Definition b0Positive {L R} (ops : B0Ops L R) (isR1 : bool) (dp : N)
  (l : list L) (r : list R) : option (B0Prep L R) :=
  let q := dp / 2 in
  if dp mod 2 =? 1 then
    opt_bind (b0Bump ops 2%nat l) (fun l2 =>
      if isR1 then Some (Some MB0, b0LitL ops (LD 0) :: b0Zeros ops q l2, r)
      else match r with
      | [] =>
        opt_bind (b0Bump ops 2%nat (b0Zeros ops (q + 1) l2))
          (fun l4 => Some (Some MDL, l4, [b0LitR ops (R0 0)]))
      | _ :: _ =>
        opt_bind (b0Add ops 1 r) (fun r' => Some (Some MB0, b0Zeros ops q l2, r'))
      end)
  else
    opt_bind (if isR1 then Some (b0PushR0 ops 2 r) else b0Add ops 2 r) (fun r' =>
      if q =? 0 then b0Q0 ops l r'
      else opt_bind (b0Bump ops 2%nat l) (fun l2 =>
        if q =? 1 then Some (Some MB0, l2, r')
        else Some (None, b0Zeros ops (q - 2) l2, b0LitR ops (R1 0) :: r'))).

Fixpoint bumpLN (n : nat) (l : list LTok) : list LTok :=
  match n with O => l | S k => bumpLN k (bumpL l) end.

Definition plainB0 : B0Ops LTok RTok :=
  {| b0ReadL := fun l => Some (unconsL l); b0Bump := fun n l => Some (bumpLN n l);
     b0Peel := peelL0; b0Zeros := pushZeros; b0Add := fun n r => Some (addR n r);
     b0PushR0 := pushR0; b0LitL := fun t => t; b0LitR := fun t => t |}.

Definition enterB0 (l : list LTok) (r : list RTok) (p : option (B0Prep LTok RTok)) :=
  match p with
  | Some (Some m, l', r') => Core m l' r'
  | Some (None, l', r') => Core MDL l' r'
  | None => Core MB0 l r
  end.

Definition stepB0Pos (isR1 : bool) (dp : N) (l : list LTok) (r : list RTok) : BaseState :=
  match b0Positive plainB0 isR1 dp l r with
  | Some (None, l', r') => foldDL2 l' r'
  | p => enterB0 l r p
  end.

Ltac reduce_plain_b0 :=
  cbn [plainB0 b0ReadL b0Bump b0Peel b0Zeros b0Add b0PushR0 b0LitL b0LitR bumpLN opt_bind enterB0].

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

Lemma stepB0Prepare_sound (isR1 : bool) (dp : N) (l : list LTok) (rRest : list RTok)
  (r : list RTok)
  (hr : eR r = eR ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: rRest)) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (enterB0 l rRest (b0Positive plainB0 isR1 dp l rRest)).
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
  unfold b0Positive; reduce_plain_b0; fold l2.
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
        reduce_plain_b0. cbn [encodeBase encodeCore].
        rewrite !eL_bumpL, (eL_pushZeros (q + 1)), (eL_pushZeros q).
        replace (q + 1) with (1 + q) by lia.
        rewrite (repBlock_add wL0 1 q), repBlock_1, Str_app_assoc.
        change (eR [R0 0]) with (S1 >> (S0 >> const S0)).
        rewrite zero_cons_def. reflexivity.
      * eapply rs_trans; [exact h2q |].
        refine (chkWin_eq false false 6%nat A true [] [S1; S1; S0; S1] B false [S0] [S1; S1; S1]
          (eL (pushZeros q l2)) (tailAfter1R r1 rs) (@no_false _) (@no_false _) _ _ eq_refl).
        -- rewrite (eR_cons_one r1 rs). reflexivity.
        -- reduce_plain_b0. cbn [encodeBase encodeCore].
           rewrite (eR_addR 1 (r1 :: rs)), (eR_cons_one r1 rs), <- evalWin_b0_flip. reflexivity.
  - apply N.eqb_neq in hrem.
    set (q := dp / 2).
    set (rNew := if isR1 then pushR0 2 rRest else addR 2 rRest).
    assert (hnew : (if isR1 then Some (pushR0 2 rRest) else Some (addR 2 rRest)) = Some rNew)
      by (destruct isR1; reflexivity).
    rewrite hnew. cbn [opt_bind].
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
      rewrite hstart0. cut (enterB0 l rRest (b0Q0 plainB0 l rNew) = stepB0OddQ0 l rNew).
      * intro he. rewrite he. exact (stepB0OddQ0_sound l rNew rTail hrNew).
      * unfold b0Q0, stepB0OddQ0. reduce_plain_b0.
        destruct (unconsL l) as [[[? | ?] ?] |]; reflexivity.
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
        -- reduce_plain_b0. cbn [encodeBase encodeCore]. unfold l2.
           rewrite !eL_bumpL, hrNew. reflexivity.
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
        exact (rs_trans h2q h7).
Qed.

Lemma stepB0Pos_sound (isR1 : bool) (dp : N) (l : list LTok) (rRest r : list RTok)
  (hr : eR r = eR ((if isR1 then R1 (dp + 1) else R0 (dp + 1)) :: rRest)) :
  encodeBase (Core MB0 l r) -[ tm ]->* encodeBase (stepB0Pos isR1 dp l rRest).
Proof.
  pose proof (stepB0Prepare_sound isR1 dp l rRest r hr) as hs.
  unfold stepB0Pos.
  destruct (b0Positive plainB0 isR1 dp l rRest) as [[[[m |] l'] r'] |].
  - exact hs.
  - exact (foldDL2_sound _ l' r' hs).
  - exact hs.
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
(* Section 7: Physical Block Checker & Parameterized Phase Transitions      *)
(* ========================================================================= *)

Definition opt_map {T U : Type} (f : T -> U) (x : option T) : option U :=
  match x with
  | Some a => Some (f a)
  | None => None
  end.

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

Lemma symReached_trans
  {m0 m1 m2 : Mode} {sl0 sl1 sl2 : list SymLTok} {sr0 sr1 sr2 : list SymRTok}
  (h1 : SymReached m0 sl0 sr0 m1 sl1 sr1)
  (h2 : SymReached m1 sl1 sr1 m2 sl2 sr2) :
  SymReached m0 sl0 sr0 m2 sl2 sr2.
Proof.
  intros vr v2 v3 v4 rest.
  exact (rs_trans (h1 vr v2 v3 v4 rest) (h2 vr v2 v3 v4 rest)).
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

(* A hole denotes a whole power, not bits on which a transition can branch. *)
Inductive BAtom := Bit (b : Sym) | Power (var : nat) (word : list Sym).
Definition Stack := list BAtom.
Definition Vals := nat -> N.
Definition BCfg := (Q * bool * Stack * Stack)%type.

Fixpoint pile (val : Vals) (xs : Stack) (outside : side) : side :=
  match xs with
  | [] => outside
  | Bit b :: tl => b >> pile val tl outside
  | Power i w :: tl => repBlock w (val i) *> pile val tl outside
  end.

Definition blockCfg (val : Vals) (outside : side) (st : BCfg) : Q * tape :=
  evalView (fun l => pile val l outside) (fun r => pile val r (const S0)) st.

Lemma pile_bits val (w : list Sym) xs outside :
  pile val (List.map Bit w ++ xs) outside = w *> pile val xs outside.
Proof. induction w; cbn [List.map app pile Str_app]; now rewrite ?IHw. Qed.

Lemma slide_power (x u w : list Sym) (H : x ++ u = w ++ x) :
  forall n s, x *> (repBlock u n *> s) = repBlock w n *> (x *> s).
Proof.
  intro n; induction n as [| n IH] using N.peano_ind; intro s; [reflexivity |].
  replace (N.succ n) with (n + 1) by lia.
  rewrite !repBlock_succ_left, !Str_app_assoc.
  rewrite <- (Str_app_assoc x u), H, Str_app_assoc, IH. reflexivity.
Qed.

Fixpoint stripBits (p : list Sym) (xs : Stack) : option Stack :=
  match p, xs with
  | [], _ => Some xs
  | a :: tl, Bit b :: more => if sym_eqb a b then stripBits tl more else None
  | _, _ => None
  end.

Lemma stripBits_sound p xs out : stripBits p xs = Some out -> xs = List.map Bit p ++ out.
Proof.
  revert xs. induction p as [| a p IH]; intros xs h.
  - cbn [stripBits] in h. now injection h as ->.
  - destruct xs as [| [b |] rest]; try discriminate.
    cbn [stripBits] in h.
    destruct a, b; try discriminate; cbn [sym_eqb] in h; now rewrite (IH _ h).
Qed.

Fixpoint findPower (fuel : nat) (xs : Stack) : option (list Sym * nat * list Sym * Stack) :=
  match xs with
  | [] => None
  | Power i w :: rest => Some ([], i, w, rest)
  | Bit b :: tl =>
    match fuel with
    | O => None
    | S k => opt_map (fun '(gap, i, w, rest) => (b :: gap, i, w, rest)) (findPower k tl)
    end
  end.

Lemma findPower_sound fuel xs gap i w rest :
  findPower fuel xs = Some (gap, i, w, rest) ->
  xs = List.map Bit gap ++ Power i w :: rest.
Proof.
  revert xs gap. induction fuel as [| k IH]; intros [| [b | v t] tl] gap h; try discriminate;
    try (injection h as <- <- <- <-; reflexivity).
  cbn [findPower] in h.
  destruct (findPower k tl) as [[[[g j] u] ts] |] eqn:hf; try discriminate.
  injection h as <- <- <- <-. cbn [List.map app]. now rewrite (IH _ _ hf).
Qed.

Definition alignPower (pre w : list Sym) (xs : Stack) : option (nat * Stack) :=
  opt_bind (stripBits pre xs) (fun after =>
    opt_bind (findPower (2 * length w)%nat after) (fun '(gap, i, u, rest) =>
      if list_sym_eqb (gap ++ u) (w ++ gap)
      then Some (i, List.map Bit gap ++ rest)
      else None)).

Lemma alignPower_sound pre w xs i out val outside :
  alignPower pre w xs = Some (i, out) ->
  pile val xs outside = pre *> (repBlock w (val i) *> pile val out outside).
Proof.
  unfold alignPower.
  destruct (stripBits pre xs) as [after |] eqn:hp; cbn [opt_bind]; [| discriminate].
  destruct (findPower (2 * length w)%nat after) as [[[[gap j] u] rest] |] eqn:hf;
    cbn [opt_bind]; [| discriminate].
  destruct (list_sym_eqb (gap ++ u) (w ++ gap)) eqn:hw; [| discriminate].
  intros [= <- <-]. rewrite (stripBits_sound _ _ _ hp), (findPower_sound _ _ _ _ _ _ hf).
  rewrite !pile_bits. cbn [pile]. now rewrite (slide_power _ _ _ (list_sym_eqb_eq _ _ hw)).
Qed.

Record MovePower := mkMove {
  fromRight : bool;
  preL : list Sym;
  preR : list Sym;
  sourceWord : list Sym;
  destWord : list Sym
}.

Definition moves :=
  [mkMove false (List.tl pLA) (S0 :: pRA) uM vM;
   mkMove true [] (S0 :: pRB) vM wM;
   mkMove false (List.tl pL2A) (S0 :: r1_9Bits) uM2 vM2;
   mkMove true [] (S0 :: pRB) vM2 wM2].

Definition move_spec (m : MovePower) : Prop :=
  forall k l r,
  if fromRight m then
    evalWin l (repBlock (sourceWord m) k *> r) B true (preL m) (preR m) -[ tm ]->*
    evalWin (repBlock (destWord m) k *> l) r B true (preL m) (preR m)
  else
    evalWin (repBlock (sourceWord m) k *> l) r B true (preL m) (preR m) -[ tm ]->*
    evalWin l (repBlock (destWord m) k *> r) B true (preL m) (preR m).

Lemma moves_sound : Forall move_spec moves.
Proof.
  repeat apply Forall_cons. 5: constructor.
  - exact (walkWordLeft 448 B false pLA uM pRA vM motifA_body).
  - exact (walkWordRight 494 B false [S0] wM pRB vM motifB_body).
  - exact (walkWordLeft 670 B false pL2A uM2 r1_9Bits vM2 motif2A_body).
  - exact (walkWordRight 368 B false [S0] wM2 pRB vM2 motif2B_body).
Qed.

Definition movePower (m : MovePower) (l r : Stack) : option (Stack * Stack) :=
  let pl := preL m in let pr := preR m in
  let u := sourceWord m in let v := destWord m in
  if fromRight m then
    opt_bind (stripBits pl l) (fun lt =>
      opt_map (fun '(i, rt) => (List.map Bit pl ++ Power i v :: lt, List.map Bit pr ++ rt))
        (alignPower pr u r))
  else
    opt_bind (stripBits pr r) (fun rt =>
      opt_map (fun '(i, lt) => (List.map Bit pl ++ lt, List.map Bit pr ++ Power i v :: rt))
        (alignPower pl u l)).

Lemma movePower_sound m (hs : move_spec m) l r l' r' :
  movePower m l r = Some (l', r') ->
  forall val outside, blockCfg val outside (B, true, l, r) -[ tm ]->*
    blockCfg val outside (B, true, l', r').
Proof.
  unfold movePower, move_spec in *. cbv zeta. destruct (fromRight m).
  - destruct (stripBits (preL m) l) as [lt |] eqn:hl; [| discriminate].
    cbn [opt_bind].
    destruct (alignPower (preR m) (sourceWord m) r) as [[i rt] |] eqn:hr; [| discriminate].
    intros [= <- <-] val outside.
    cbn [blockCfg evalView]. rewrite (stripBits_sound _ _ _ hl), !pile_bits,
      (alignPower_sound _ _ _ _ _ val _ hr).
    exact (hs (val i) (pile val lt outside) (pile val rt (const S0))).
  - destruct (stripBits (preR m) r) as [rt |] eqn:hr; [| discriminate].
    cbn [opt_bind].
    destruct (alignPower (preL m) (sourceWord m) l) as [[i lt] |] eqn:hl; [| discriminate].
    intros [= <- <-] val outside.
    cbn [blockCfg evalView]. rewrite (stripBits_sound _ _ _ hr), !pile_bits,
      (alignPower_sound _ _ _ _ _ val _ hl).
    exact (hs (val i) (pile val lt outside) (pile val rt (const S0))).
Qed.

Definition firstMove (ms : list MovePower) (l r : Stack) :=
  firstSome (fun m => movePower m l r) ms.

Lemma firstMove_sound ms (hs : Forall move_spec ms) l r l' r' :
  firstMove ms l r = Some (l', r') ->
  forall val outside, blockCfg val outside (B, true, l, r) -[ tm ]->*
    blockCfg val outside (B, true, l', r').
Proof.
  unfold firstMove. intro h.
  refine (firstSome_sound _ (fun '(a, b) => forall val outside,
    blockCfg val outside (B, true, l, r) -[ tm ]->*
    blockCfg val outside (B, true, a, b)) ms (l', r') _ h).
  clear h. induction hs as [|m ms hm _ IH]; [constructor | constructor].
  - intros [a b]. exact (movePower_sound m hm l r a b).
  - exact IH.
Qed.

Definition readBit (d : bool) (xs : Stack) : option (Sym * Stack) :=
  match xs with
  | Bit b :: tl => Some (b, tl)
  | [] => if d then Some (S0, []) else None
  | _ => None
  end.

Lemma readBit_reads val outside b (h : b = true -> outside = const S0) :
  reads (fun xs => pile val xs outside) (readBit b).
Proof.
  intros [|[x|] xs] a tl; try discriminate.
  - destruct b; [|discriminate]. intros [= <- <-].
    specialize (h eq_refl); subst outside. exact (eq_sym zero_cons_def).
  - intros [= <- <-]. reflexivity.
Qed.

Definition blockRaw := readStep (readBit false) (readBit true) (fun a xs => Bit a :: xs).

Lemma blockRaw_sound st out : blockRaw st = Some out ->
  forall val outside, blockCfg val outside st -[ tm ]->* blockCfg val outside out.
Proof.
  intros h val outside. eapply evstep_step; [|apply rs_refl].
  exact (readStep_sound (readBit false) (readBit true) (fun a xs => Bit a :: xs)
    (fun xs => pile val xs outside) (fun xs => pile val xs (const S0))
    (readBit_reads _ _ _ (@no_false _)) (readBit_reads _ _ _ (fun _ => eq_refl))
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) _ _ h).
Qed.

Definition faceRight (st : BCfg) : option BCfg :=
  let '(q, d, l, r) := st in
  if d then Some st else
  match l with Bit b :: lt => Some (q, true, lt, Bit b :: r) | _ => None end.

Lemma faceRight_sound st st' val outside :
  faceRight st = Some st' -> blockCfg val outside st = blockCfg val outside st'.
Proof.
  destruct st as [[[q d] l] r]. destruct d; [intros [= <-]; reflexivity |].
  destruct l as [| [] l]; try discriminate. intros [= <-]. reflexivity.
Qed.

Definition blockStep (st : BCfg) : option BCfg :=
  let '(q, _, _, _) := st in
  match q with
  | B =>
    match faceRight st with
    | Some (_, _, l, r) =>
      match firstMove moves l r with
      | Some (l', r') => Some (B, true, l', r')
      | None => blockRaw st
      end
    | None => blockRaw st
    end
  | _ => blockRaw st
  end.

Lemma blockStep_sound st out : blockStep st = Some out ->
  forall val outside, blockCfg val outside st -[ tm ]->* blockCfg val outside out.
Proof.
  destruct st as [[[q d] l] r]; destruct q; try (apply blockRaw_sound).
  destruct d.
  - cbn [blockStep faceRight].
    destruct (firstMove moves l r) as [[lt rt] |] eqn:h; [| apply blockRaw_sound].
    intros [= <-]. exact (firstMove_sound _ moves_sound _ _ _ _ h).
  - destruct l as [| [b |] l]; try apply blockRaw_sound.
    cbn [blockStep faceRight].
    destruct (firstMove moves l (Bit b :: r)) as [[lt rt] |] eqn:h; [| apply blockRaw_sound].
    intros [= <-]. exact (firstMove_sound _ moves_sound _ _ _ _ h).
Qed.

(* Compare at an endpoint with holes pushed away from the head. *)
Fixpoint slideHole i (w : list Sym) (xs : Stack) : Stack :=
  match w, xs with
  | a :: ws, Bit b :: tl =>
    if sym_eqb a b then Bit b :: slideHole i (ws ++ [a]) tl else Power i w :: xs
  | _, _ => Power i w :: xs
  end.

Lemma slideHole_sound i xs val outside :
  forall w, pile val (slideHole i w xs) outside = pile val (Power i w :: xs) outside.
Proof.
  induction xs as [| [b | j u] tl IH]; intros [| a w]; try reflexivity.
  destruct a, b; cbn [slideHole sym_eqb]; try reflexivity;
    cbn [pile]; rewrite IH; cbn [pile];
    exact (slide_power [_] (w ++ [_]) (_ :: w) eq_refl _ _).
Qed.

Fixpoint normHoles (xs : Stack) : Stack :=
  match xs with
  | [] => []
  | Bit b :: tl => Bit b :: normHoles tl
  | Power i w :: tl => slideHole i w (normHoles tl)
  end.

Lemma normHoles_sound xs val outside :
  pile val (normHoles xs) outside = pile val xs outside.
Proof.
  induction xs as [| [] tl IH]; cbn [normHoles]; try rewrite slideHole_sound;
    cbn [pile]; now rewrite ?IH.
Qed.

Fixpoint trimBlank (xs : Stack) : Stack :=
  match xs with
  | [] => []
  | a :: tl =>
    let more := trimBlank tl in
    match a, more with Bit S0, [] => [] | _, _ => a :: more end
  end.

Lemma trimBlank_sound xs val :
  pile val (trimBlank xs) (const S0) = pile val xs (const S0).
Proof.
  induction xs as [| [[|] |] tl IH]; cbn [trimBlank pile]; try (now rewrite ?IH).
  destruct (trimBlank tl) as [| a rest]; cbn [pile] in *.
  - rewrite <- IH. symmetry. apply zero_cons_def.
  - now rewrite IH.
Qed.

Definition atomEq a b :=
  match a, b with
  | Bit x, Bit y => sym_eqb x y
  | Power i x, Power j y => if Nat.eqb i j then list_sym_eqb x y else false
  | _, _ => false
  end.

Lemma atomEq_sound a b : atomEq a b = true -> a = b.
Proof.
  destruct a, b; try discriminate; cbn [atomEq].
  - destruct b, b0; cbn [sym_eqb]; congruence.
  - destruct (Nat.eqb var var0) eqn:h; try discriminate.
    apply Nat.eqb_eq in h. intros hw. now rewrite h, (list_sym_eqb_eq _ _ hw).
Qed.

Fixpoint stackEq (a b : Stack) : bool :=
  match a, b with
  | [], [] => true
  | x :: l, y :: r => if atomEq x y then stackEq l r else false
  | _, _ => false
  end.

Lemma stackEq_sound a b : stackEq a b = true -> a = b.
Proof.
  revert b. induction a as [| x l IH]; intros [| y r]; try discriminate; [reflexivity |].
  cbn [stackEq]. destruct (atomEq x y) eqn:h; try discriminate.
  intros hr. now rewrite (atomEq_sound _ _ h), (IH _ hr).
Qed.

Definition endpoint (st : BCfg) : option BCfg :=
  opt_map (fun '(q, d, l, r) => (q, d, normHoles l, normHoles (trimBlank r))) (faceRight st).

Lemma endpoint_sound st out val outside :
  endpoint st = Some out -> blockCfg val outside st = blockCfg val outside out.
Proof.
  unfold endpoint. destruct (faceRight st) as [[[[q d] l] r] |] eqn:h; [| discriminate].
  intros [= <-]. rewrite (faceRight_sound _ _ val outside h).
  cbn [blockCfg evalView]. now rewrite !normHoles_sound, trimBlank_sound.
Qed.

Definition blockEq (st out : BCfg) : bool :=
  match endpoint st, endpoint out with
  | Some (q, d, l, r), Some (q', d', l', r') =>
    q_eqb q q' && Bool.eqb d d' && stackEq l l' && stackEq r r'
  | _, _ => false
  end.

Lemma blockEq_sound st out val outside :
  blockEq st out = true -> blockCfg val outside st = blockCfg val outside out.
Proof.
  unfold blockEq.
  destruct (endpoint st) as [[[[q d] l] r] |] eqn:h; [| discriminate].
  destruct (endpoint out) as [[[[q' d'] l'] r'] |] eqn:h'; [| discriminate].
  rewrite !Bool.andb_true_iff. intros [[[hq hd] hl] hr].
  destruct (q_eqb_spec q q'); [| discriminate].
  apply Bool.eqb_prop in hd. apply stackEq_sound in hl, hr. subst.
  now rewrite (endpoint_sound _ _ _ _ h), (endpoint_sound _ _ _ _ h').
Qed.

Definition blockOptStep (a : option BCfg) := opt_bind a blockStep.

Definition blockReach (a b : option BCfg) : Prop :=
  forall out, b = Some out -> exists st, a = Some st /\
  forall val outside, blockCfg val outside st -[ tm ]->* blockCfg val outside out.

Lemma blockReach_trans a b c : blockReach a b -> blockReach b c -> blockReach a c.
Proof.
  intros hab hbc out ho. destruct (hbc _ ho) as [mid [hm h2]].
  destruct (hab _ hm) as [st [hs h1]].
  exists st. split; [exact hs |]. intros val outside. eapply rs_trans; [apply h1 | apply h2].
Qed.

Lemma blockReach_iter p a : blockReach a (Pos.iter blockOptStep a p).
Proof.
  revert a. induction p as [p IH | p IH |]; intro a; cbn [Pos.iter].
  - eapply blockReach_trans; [apply IH |]. eapply blockReach_trans; [apply IH |].
    destruct (Pos.iter blockOptStep (Pos.iter blockOptStep a p) p) as [st |]; [| discriminate].
    intros out h. exists st. split; [reflexivity |]. now apply blockStep_sound.
  - eapply blockReach_trans; apply IH.
  - destruct a as [st |]; [| discriminate].
    intros out h. exists st. split; [reflexivity |]. now apply blockStep_sound.
Qed.

(* The stage boundaries still use the old names for the physical words. *)
Definition wordL (t : LTok) : list Sym :=
  match t with
  | L0 k => repBlock wL0 (k + 1)
  | LD d => repBlock [S1] (d + 2) ++ [S0]
  | LD1 k => repBlock wLD1 (k + 1)
  | ML8 k => repBlock uM (k + 1)
  | M2L k => repBlock uM2 (k + 1)
  | M3L k => repBlock wM3 (k + 1)
  | M4L k => repBlock wM4 (k + 1)
  end.

Definition wordR (t : RTok) : list Sym :=
  match t with
  | R0 d => repBlock [S1] (d + 1) ++ [S0]
  | R1 d => repBlock [S1] (d + 1) ++ [S0; S0]
  | R02 k => repBlock wLD1 (k + 1)
  | MR11 k => repBlock vM (k + 1)
  | M2R k => repBlock vM2 (k + 1)
  end.

Definition emitPower i w d (tl : Stack) :=
  List.map Bit (repBlock w (d + 1)) ++ Power i w :: tl.

Fixpoint encodeHoleL (ts : list SymLTok) : Stack :=
  match ts with
  | [] => []
  | t :: tl =>
    let rest := encodeHoleL tl in
    match t with
    | SLC a => List.map Bit (wordL a) ++ rest
    | SM2 d => emitPower 1%nat uM2 d rest
    | SM3 d => emitPower 2%nat wM3 d rest
    | SM4 d => emitPower 3%nat wM4 d rest
    | SM3P d => List.map Bit (repBlock wM3 (d + 1)) ++ rest
    | SM4P d => List.map Bit (repBlock wM4 (d + 1)) ++ rest
    end
  end.

Fixpoint encodeHoleR (ts : list SymRTok) : Stack :=
  match ts with
  | [] => []
  | t :: tl =>
    let rest := encodeHoleR tl in
    match t with
    | SRC a => List.map Bit (wordR a) ++ rest
    | SMR d => emitPower 0%nat vM d rest
    | SM2R d => emitPower 1%nat vM2 d rest
    end
  end.

Definition stageVals vr v2 v3 v4 : Vals :=
  fun i => match i with O => vr | S O => v2 | S (S O) => v3 | _ => v4 end.

Lemma emitPower_sound val i w d tl outside :
  pile val (emitPower i w d tl) outside =
  repBlock w (val i + d + 1) *> pile val tl outside.
Proof.
  unfold emitPower. rewrite pile_bits. cbn [pile].
  replace (val i + d + 1) with (d + 1 + val i) by lia.
  now rewrite (repBlock_add w (d + 1) (val i)), Str_app_assoc.
Qed.

Lemma encodeHoleL_sound ts vr v2 v3 v4 rest :
  pile (stageVals vr v2 v3 v4) (encodeHoleL ts) (eL rest) =
  eL (evalSymL v2 v3 v4 ts rest).
Proof.
  induction ts as [| [] tl IH]; cbn [encodeHoleL evalSymL]; [reflexivity | ..];
    rewrite ?emitPower_sound, ?pile_bits, IH; cbn [stageVals];
    rewrite ?eL_pushM3L, ?eL_pushM4L; try reflexivity.
  destruct t; cbn [wordL eL]; now rewrite ?Str_app_assoc.
Qed.

Lemma encodeHoleR_sound ts vr v2 v3 v4 :
  pile (stageVals vr v2 v3 v4) (encodeHoleR ts) (const S0) = eR (evalSymR vr v2 ts).
Proof.
  induction ts as [| [] tl IH]; cbn [encodeHoleR evalSymR]; [reflexivity | ..];
    rewrite ?emitPower_sound, ?pile_bits, IH; cbn [stageVals]; try reflexivity.
  destruct t; cbn [wordR eR]; now rewrite ?Str_app_assoc.
Qed.

Definition symBlockCfg m sl sr : BCfg :=
  let l := encodeHoleL sl in let r := encodeHoleR sr in
  match m with MB0 => (B, true, l, Bit S0 :: r) | MDL => (D, false, l, r) end.

Lemma symBlockCfg_sound m sl sr vr v2 v3 v4 rest :
  blockCfg (stageVals vr v2 v3 v4) (eL rest) (symBlockCfg m sl sr) =
  encodeBase (Core m (evalSymL v2 v3 v4 sl rest) (evalSymR vr v2 sr)).
Proof.
  destruct m; cbn [symBlockCfg blockCfg evalView pile];
    now rewrite encodeHoleL_sound, encodeHoleR_sound.
Qed.

(* Replay fixed bits by the TM table and opaque powers by the four moves.
   Only the endpoints are translated from the driver's RLE vocabulary. *)
Definition checkHoles (p : positive) m sl sr m' sl' sr' : bool :=
  match Pos.iter blockOptStep (Some (symBlockCfg m sl sr)) p with
  | Some out => blockEq out (symBlockCfg m' sl' sr')
  | None => false
  end.

Lemma checkHoles_sound {p m sl sr m' sl' sr'} :
  checkHoles p m sl sr m' sl' sr' = true -> SymReached m sl sr m' sl' sr'.
Proof.
  unfold checkHoles.
  destruct (Pos.iter _ _ _) as [out |] eqn:h; [| discriminate].
  intros he vr v2 v3 v4 rest.
  destruct (blockReach_iter p _ _ h) as [st [[= <-] hr]].
  rewrite <- !symBlockCfg_sound, <- (blockEq_sound _ _ _ _ he).
  apply hr.
Qed.


Definition capTailSym : list SymRTok := [SRC (R02 0); SRC (R1 3); SRC (R02 0)].

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
  checkHoles 5648%positive MB0
    [SLC (LD 2); SLC (L0 1)]
    (SRC (R0 4) :: SMR 1 :: capTailSym)
    MB0
    [SLC (LD 2); SLC (L0 1); SM3P 0]
    (SRC (R0 4) :: SMR 0 :: capTailSym) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era1_step_sym :
  SymReached MB0
    [SLC (LD 2); SLC (L0 1)]
    (SRC (R0 4) :: SMR 1 :: capTailSym)
    MB0
    [SLC (LD 2); SLC (L0 1); SM3P 0]
    (SRC (R0 4) :: SMR 0 :: capTailSym).
Proof. exact (checkHoles_sound era1_step_raw). Qed.

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
  checkHoles 814%positive MB0
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
  pose proof (checkHoles_sound bridgeH10_raw mr 0 0 0 afterH10) as hr.
  rewrite evalSymL_map_c_nil, evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge0a_raw :
  checkHoles 2726%positive MB0
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
  pose proof (checkHoles_sound bridge0a_raw mr 0 0 0 rest) as hr.
  rewrite evalSymL_map_c_nil, evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge1_raw :
  checkHoles 3022%positive MB0
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
  pose proof (checkHoles_sound bridge1_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge2_raw :
  checkHoles 3258%positive MB0
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
  pose proof (checkHoles_sound bridge2_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma bridge3_raw :
  checkHoles 3586%positive MB0
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
  pose proof (checkHoles_sound bridge3_raw mr 0 0 0 rest) as hr.
  rewrite !evalSymR_map_c in hr.
  cbn [evalSymL evalSymR capTailSym] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Record CapBridge := {
  bridgeInR : list RTok;
  bridgeOutL : list LTok;
  bridgeOutR : list RTok;
  bridgeDelta : N
}.

Definition capBridgeL := [L0 0; LD1 5; LD 5].
Definition capBridges :=
  [Build_CapBridge bridge0aPfx h10Top [R0 9; R1 0] 1;
   Build_CapBridge bridge1Pfx [LD 5] bridge1OutTop 0;
   Build_CapBridge bridge2Pfx [LD 5] bridge2OutTop 0;
   Build_CapBridge bridge3Pfx [LD 5] bridge3OutTop 0].
Definition CapBridgeSound (lp : list LTok) (b : CapBridge) :=
  forall n rest,
  encodeBase (Core MB0 (lp ++ rest) (bridgeInR b ++ (MR11 n :: capTailR))) -[ tm ]->*
  encodeBase (Core MB0 (bridgeOutL b ++ rest) (bridgeOutR b ++ (MR11 (n + bridgeDelta b) :: capTailR))).

Lemma capBridges_sound : Forall (CapBridgeSound capBridgeL) capBridges.
Proof.
  repeat constructor; unfold CapBridgeSound; intros; cbn [capBridgeL bridgeInR bridgeOutL bridgeOutR bridgeDelta];
    rewrite ?N.add_0_r.
  - apply bridge0a_concrete.
  - apply bridge1_concrete.
  - apply bridge2_concrete.
  - apply bridge3_concrete.
Qed.

Definition era2Mid176L : list SymLTok :=
  [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
   SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
   SLC (LD 7); SLC (LD 3); SLC (LD 7); SLC (LD 3); SLC (L0 0); SLC (LD 5);
   SLC (LD 3); SLC (L0 3); SLC (LD1 0); SLC (L0 0); SLC (LD1 0);
   SLC (LD 7); SLC (LD 7); SM3 9].

Lemma era2Head_chk :
  checkHoles 27410%positive MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 2;
     SLC (L0 3); SLC (LD 9); SLC (LD 7); SM3 10]
    [SRC (R0 9); SRC (R1 0); SMR 0; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0 era2Mid176L
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era2Tail_chk :
  checkHoles 1358450%positive MB0 era2Mid176L
    [SRC (R0 9); SRC (R1 0); SMR 1; SRC (R02 0); SRC (R1 3); SRC (R02 0)]
    MB0
    [SLC (LD 7); SLC (LD 3); SLC (LD 5); SLC (LD 7); SLC (LD 3); SLC (LD1 1);
     SLC (LD 5); SLC (LD 3); SLC (LD1 8); SLC (LD 5); SM2 7;
     SLC (L0 3); SLC (LD 9); SLC (LD 7); SM3 0]
    [SRC (R0 9); SRC (R1 0); SMR 19; SRC (R02 0); SRC (R1 3); SRC (R02 0)] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma era3a_chk :
  checkHoles 3711112%positive MB0
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
  checkHoles 228490%positive MB0
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
  checkHoles 247174%positive MB0
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
  checkHoles 23916%positive MB0
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
  checkHoles 25992%positive MB0
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
  checkHoles 60862%positive MB0
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
  checkHoles 78718%positive MB0
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
  checkHoles 394169%positive MB0
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
  pose proof (symReached_trans (checkHoles_sound era2Head_chk) (checkHoles_sound era2Tail_chk) mr d2 v3 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v3 + 0) with v3 in hr by lia.
  exact hr.
Qed.

(* Each pass consumes one stride of the active digit and adds fixed
   increments to the other two. No tape representation is needed here. *)
Lemma affine_countdown (cfg : N -> N -> N -> Q * tape) (dr da db : N)
  (next : forall r a b, cfg r a (b + db) -[ tm ]->* cfg (r + dr) (a + da) b) :
  forall n r a b, cfg r a (b + db * n) -[ tm ]->* cfg (r + dr * n) (a + da * n) b.
Proof.
  intro n; induction n as [| n IH] using N.peano_ind; intros r a b.
  - rewrite !N.mul_0_r, !N.add_0_r. apply rs_refl.
  - rewrite !N.mul_succ_r.
    replace (b + (db * n + db)) with (b + db * n + db) by lia.
    replace (r + (dr * n + dr)) with (r + dr + dr * n) by lia.
    replace (a + (da * n + da)) with (a + da + da * n) by lia.
    exact (rs_trans (next r a (b + db * n)) (IH (r + dr) (a + da) b)).
Qed.

Lemma era3a_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 1) :: era3aMidTop ++ (M4L (v4 + 44) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 8) :: era3aMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 35))).
Proof.
  pose proof (checkHoles_sound era3a_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era3b_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3bMidTop ++ (M4L (v4 + 7) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 3) :: era3bMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 6))).
Proof.
  pose proof (checkHoles_sound era3b_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era3c_step_concrete (mr d2 v4 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 2) :: era3cMidTop ++ (M4L (v4 + 7) :: rest))) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (d2 + 3) :: era3cMidTop ++ (M4L v4 :: rest))) (rc6Of (mr + 6))).
Proof.
  pose proof (checkHoles_sound era3c_chk mr d2 0 v4 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v4 + 0) with v4 in hr by lia.
  exact hr.
Qed.

Lemma era4a_step_concrete (mr v2 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 1) :: era4aMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L v2 :: era4aMidTop ++ pushM4L 1 rest)) (rc6Of (mr + 1))).
Proof.
  pose proof (checkHoles_sound era4a_chk mr v2 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  replace (v2 + 0) with v2 in hr by lia.
  exact hr.
Qed.

(* The other countdown grows a suffix by all the blocks produced by
   successive calls. pushM4L's argument is the run length minus one. *)
Lemma grow_M4_countdown (cfg : N -> N -> list LTok -> Q * tape)
  (next : forall r n rest, cfg r (n + 1) rest -[ tm ]->* cfg (r + 1) n (pushM4L 1 rest)) :
  forall n r rest, cfg r (n + 1) rest -[ tm ]->* cfg (r + (n + 1)) 0 (pushM4L (2 * n + 1) rest).
Proof.
  intro n; induction n as [| n IH] using N.peano_ind; intros r rest.
  - exact (next r 0 rest).
  - rewrite <- N.add_1_r.
    pose proof (IH (r + 1) (pushM4L 1 rest)) as hr.
    rewrite pushM4L_pushM4L in hr.
    replace (2 * n + 1 + 1 + 1) with (2 * (n + 1) + 1) in hr by lia.
    replace (r + 1 + (n + 1)) with (r + (n + 1 + 1)) in hr by lia.
    exact (rs_trans (next r (n + 1) rest) hr).
Qed.

Lemma era4b_step_concrete (mr v2 : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 2) :: era4bMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L (v2 + 1) :: era4bMidTop ++ pushM4L 1 rest)) (rc6Of (mr + 1))).
Proof.
  pose proof (checkHoles_sound era4b_chk mr v2 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma era4aEnd_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L 0 :: era4aMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (era4aEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 2))).
Proof.
  pose proof (checkHoles_sound era4aEnd_chk mr 0 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma era4bEnd_concrete (mr : N) (rest : list LTok) :
  encodeBase (Core MB0 (h10Top ++ (M2L 1 :: era4bMidTop ++ rest)) (rc6Of mr)) -[ tm ]->*
  encodeBase (Core MB0 (era4bEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 3))).
Proof.
  pose proof (checkHoles_sound era4bEnd_chk mr 0 0 0 rest) as hr.
  cbn [evalSymL evalSymR] in hr.
  replace (mr + 0) with mr in hr by lia.
  exact hr.
Qed.

Lemma postMR11_concrete (m3Rem : N) (rest : list LTok) :
  encodeBase (Core MB0 (LD 2 :: L0 1 :: M3L (m3Rem + 16) :: rest) (rc4Of 0)) -[ tm ]->*
  encodeBase (Core MB0 (h10Top ++ (M2L 7 :: era2MidTop ++ (M3L m3Rem :: rest))) (rc6Of 28)).
Proof.
  pose proof (checkHoles_sound postMR11Head_chk 0 0 m3Rem 0 rest) as hr1.
  pose proof (checkHoles_sound era2Tail_chk 9 0 m3Rem 0 rest) as hr2.
  cbn [era2Mid176L evalSymL evalSymR] in hr1, hr2.
  replace (m3Rem + 0) with m3Rem in hr2 by lia.
  exact (rs_trans hr1 hr2).
Qed.

(* ========================================================================= *)
(* Section 8: Countdown Driver & Halting Theorem                          *)
(* ========================================================================= *)

Definition popMRTail (r : list RTok) : option N :=
  match popMR11 r with
  | Some (mr, rTail) => if beqRList rTail capTailR then Some mr else None
  | None => None
  end.

Definition rc6Frame (mid : list LTok) (mr m2 : N) (afterM2 : list LTok) : BaseState :=
  Core MB0 (h10Top ++ (M2L m2 :: mid ++ afterM2)) (rc6Of mr).

Definition tryRC6Affine (mid : list LTok) (digit : N -> LTok)
  (pop : list LTok -> option (N * list LTok)) (offset dr da stride mr m2 : N)
  (afterM2 : list LTok) : option BaseState :=
  opt_bind (stripLPrefix mid afterM2) (fun afterMid =>
    if offset <=? m2 then
      opt_bind (pop afterMid) (fun '(v, rest) =>
        let q := v / stride in
        if 1 <=? q then
          Some (rc6Frame mid (mr + dr * q) (m2 + da * q) (digit (v mod stride) :: rest))
        else None)
    else None).

Definition tryRC6Era2 := tryRC6Affine era2MidTop M3L popM3L 2 19 5 10.
Definition tryRC6Era3a := tryRC6Affine era3aMidTop M4L popM4L 1 35 7 44.
Definition tryRC6Era3b := tryRC6Affine era3bMidTop M4L popM4L 2 6 1 7.
Definition tryRC6Era3c := tryRC6Affine era3cMidTop M4L popM4L 2 6 1 7.

Definition era4aExit mr rest :=
  Core MB0 (era4aEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 2)).
Definition era4bExit mr rest :=
  Core MB0 (era4bEndOutTop ++ pushM4L 5 rest) (rc4Of (mr + 3)).

Definition tryRC6Grow mid offset exit mr m2 afterM2 : option BaseState :=
  opt_bind (stripLPrefix mid afterM2) (fun rest =>
    if m2 <? offset then None
    else if m2 =? offset then Some (exit mr rest)
    else
      let n := m2 - offset - 1 in
      Some (rc6Frame mid (mr + (n + 1)) offset (pushM4L (2 * n + 1) rest))).

Definition tryRC6Era4a := tryRC6Grow era4aMidTop 0 era4aExit.
Definition tryRC6Era4b := tryRC6Grow era4bMidTop 1 era4bExit.

Definition rc6Phases :=
  [tryRC6Era2; tryRC6Era3a; tryRC6Era3b; tryRC6Era3c; tryRC6Era4a; tryRC6Era4b].

Definition tryRC6All (mr : N) (afterH10 : list LTok) : option BaseState :=
  opt_bind (popM2L afterH10) (fun '(m2, afterM2) =>
    firstSome (fun phase => phase mr m2 afterM2) rc6Phases).

Definition stepRC6H10 (mr : N) (afterH10 : list LTok) : BaseState :=
  match tryRC6All mr afterH10 with
  | Some res => res
  | None => Core MB0 (LD 5 :: afterH10) (bridgeH10OutTop ++ (MR11 mr :: capTailR))
  end.

Definition tryCapBridge rest r b :=
  opt_bind (opt_bind (stripRPrefix (bridgeInR b) r) popMRTail) (fun k =>
    Some (Core MB0 (bridgeOutL b ++ rest)
      (bridgeOutR b ++ (MR11 (k + bridgeDelta b) :: capTailR)))).

Definition stepCapBridgeB0 (l : list LTok) (r : list RTok) : option BaseState :=
  opt_bind (stripLPrefix capBridgeL l) (fun rest =>
    firstSome (tryCapBridge rest r) capBridges).

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

Lemma tryRC6Affine_sound (mid : list LTok) (digit : N -> LTok)
  (pop : list LTok -> option (N * list LTok)) (offset dr da stride : N)
  (pop_ok : forall xs v rest, pop xs = Some (v, rest) -> xs = digit v :: rest)
  (stride_ok : stride <> 0)
  (next : forall r a b rest,
    encodeBase (rc6Frame mid r (a + offset) (digit (b + stride) :: rest)) -[ tm ]->*
    encodeBase (rc6Frame mid (r + dr) (a + da + offset) (digit b :: rest)))
  {mr m2 afterM2 bs'} :
  tryRC6Affine mid digit pop offset dr da stride mr m2 afterM2 = Some bs' ->
  encodeBase (rc6Frame [] mr m2 afterM2) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Affine. intro h.
  destruct (stripLPrefix mid afterM2) as [xs |] eqn:hs; cbn [opt_bind] in h; [| discriminate].
  destruct (offset <=? m2) eqn:hb; [| discriminate].
  destruct (pop xs) as [[v rest] |] eqn:hp; cbn [opt_bind] in h; [| discriminate].
  set (q := v / stride) in h.
  destruct (1 <=? q); [| discriminate]. injection h as <-.
  apply N.leb_le in hb.
  rewrite (stripLPrefix_some mid afterM2 xs hs), (pop_ok xs v rest hp).
  pose (C := fun r a b => encodeBase (rc6Frame mid r (a + offset) (digit b :: rest))).
  pose proof (affine_countdown C dr da stride (fun r a b => next r a b rest)
    q mr (m2 - offset) (v mod stride)) as hr.
  unfold C, rc6Frame in hr.
  replace (v mod stride + stride * q) with v in hr
    by (unfold q; pose proof (N.div_mod v stride stride_ok); lia).
  replace (m2 - offset + offset) with m2 in hr by lia.
  replace (m2 - offset + da * q + offset) with (m2 + da * q) in hr by lia.
  exact hr.
Qed.

Lemma tryRC6Era2_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era2 mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era2. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Affine_sound; [intros; now apply popM3L_some | discriminate |].
  intros r a b rest. unfold rc6Frame.
  replace (a + 5 + 2) with (a + 7) by lia.
  exact (era2_step_concrete r a b rest).
Qed.

Lemma tryRC6Era3a_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3a mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era3a. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Affine_sound; [intros; now apply popM4L_some | discriminate |].
  intros r a b rest. unfold rc6Frame.
  replace (a + 7 + 1) with (a + 8) by lia.
  exact (era3a_step_concrete r a b rest).
Qed.

Lemma tryRC6Era3b_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3b mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era3b. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Affine_sound; [intros; now apply popM4L_some | discriminate |].
  intros r a b rest. unfold rc6Frame.
  replace (a + 1 + 2) with (a + 3) by lia.
  exact (era3b_step_concrete r a b rest).
Qed.

Lemma tryRC6Era3c_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era3c mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era3c. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Affine_sound; [intros; now apply popM4L_some | discriminate |].
  intros r a b rest. unfold rc6Frame.
  replace (a + 1 + 2) with (a + 3) by lia.
  exact (era3c_step_concrete r a b rest).
Qed.

Lemma tryRC6Grow_sound mid offset exit
  (next : forall r m rest,
    encodeBase (rc6Frame mid r (m + 1 + offset) rest) -[ tm ]->*
    encodeBase (rc6Frame mid (r + 1) (m + offset) (pushM4L 1 rest)))
  (last : forall r rest,
    encodeBase (rc6Frame mid r offset rest) -[ tm ]->* encodeBase (exit r rest))
  {mr m2 afterM2 bs'} :
  tryRC6Grow mid offset exit mr m2 afterM2 = Some bs' ->
  encodeBase (rc6Frame [] mr m2 afterM2) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6Grow. intro h.
  destruct (stripLPrefix mid afterM2) as [rest |] eqn:hs; cbn [opt_bind] in h; [| discriminate].
  destruct (m2 <? offset) eqn:hb; [discriminate |].
  rewrite (stripLPrefix_some mid afterM2 rest hs).
  destruct (m2 =? offset) eqn:he.
  - apply N.eqb_eq in he; subst. injection h as <-. exact (last mr rest).
  - apply N.ltb_ge in hb. apply N.eqb_neq in he. injection h as <-.
    pose (C := fun r n xs => encodeBase (rc6Frame mid r (n + offset) xs)).
    pose proof (grow_M4_countdown C next (m2 - offset - 1) mr rest) as hr.
    unfold C in hr. replace (m2 - offset - 1 + 1 + offset) with m2 in hr by lia.
    exact hr.
Qed.

Lemma tryRC6Era4a_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era4a mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era4a. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Grow_sound; [| exact era4aEnd_concrete].
  intros r a rest. unfold rc6Frame.
  rewrite !N.add_0_r.
  exact (era4a_step_concrete r a rest).
Qed.

Lemma tryRC6Era4b_sound {mr m2 : N} {afterM2 : list LTok} {bs' : BaseState}
  (h : tryRC6Era4b mr m2 afterM2 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  revert h. unfold tryRC6Era4b. change (encodeBase (Core MB0 (h10Top ++ (M2L m2 :: afterM2)) (rc6Of mr)))
    with (encodeBase (rc6Frame [] mr m2 afterM2)).
  apply tryRC6Grow_sound; [| exact era4bEnd_concrete].
  intros r a rest. unfold rc6Frame.
  replace (a + 1 + 1) with (a + 2) by lia.
  exact (era4b_step_concrete r a rest).
Qed.

Lemma tryRC6All_sound {mr : N} {afterH10 : list LTok} {bs' : BaseState}
  (h : tryRC6All mr afterH10 = Some bs') :
  encodeBase (Core MB0 (h10Top ++ afterH10) (rc6Of mr)) -[ tm ]->* encodeBase bs'.
Proof.
  unfold tryRC6All in h. revert h.
  destruct (popM2L afterH10) as [[m2 afterM2] |] eqn:hm2; [| discriminate].
  rewrite (popM2L_some hm2). intro h.
  refine (firstSome_sound _ (fun z => encodeBase (rc6Frame [] mr m2 afterM2) -[ tm ]->*
    encodeBase z) rc6Phases bs' _ h). unfold rc6Phases.
  repeat constructor; intros z hz;
    first [exact (tryRC6Era2_sound hz) | exact (tryRC6Era3a_sound hz) |
      exact (tryRC6Era3b_sound hz) | exact (tryRC6Era3c_sound hz) |
      exact (tryRC6Era4a_sound hz) | exact (tryRC6Era4b_sound hz)].
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
  revert h. unfold stepCapBridgeB0.
  destruct (stripLPrefix capBridgeL l) as [rest |] eqn:hl; [| discriminate].
  rewrite (stripLPrefix_some capBridgeL l rest hl). intro h.
  refine (firstSome_sound _ (fun z => encodeBase (Core MB0 (capBridgeL ++ rest) r) -[ tm ]->*
    encodeBase z) capBridges bs' _ h).
  pose proof capBridges_sound as hs. rewrite Forall_forall in *.
  intros b hin z. unfold tryCapBridge.
  destruct (opt_bind (stripRPrefix (bridgeInR b) r) popMRTail) as [k |] eqn:hr; [| discriminate].
  intros [= <-]. rewrite (stripRPrefix_bind_popMRTail hr).
  exact (hs b hin k rest).
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


Lemma checked_iter_halts (p : positive) (s : BaseState) :
  isHalted (Pos.iter stepNext s p) = true -> halts tm (encodeBase s).
Proof.
  pose proof (iter_stepNext_sound p s) as hr.
  destruct (Pos.iter stepNext s p); intro h; try discriminate.
  exact (evstep_to_halts hr eq_refl).
Qed.

Lemma halt_internal : halts tm c0.
Proof. exact (checked_iter_halts 467147%positive Init0 traj_halted). Qed.

End Internal.

Theorem halt : halts tm c0.
Proof. exact Internal.halt_internal. Qed.
