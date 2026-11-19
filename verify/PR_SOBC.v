(* Classification: SOBC.
   Consolidated from busycoq PR #19, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat Bool List String Streams.

Module TM1.
Import BusyCoq.Individual62.

Import Lia PeanoNat Bool List String Streams.

Import ListNotations.

Open Scope sym.

Open Scope list.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD : Type :=
  | W0 : LD
  | W1 : LD.

Definition encWord (d : LD) : list Sym :=
  match d with
  | W0 => [S1; S0; S0]
  | W1 => [S1; S1; S1]
  end.

Fixpoint encList (xs : list LD) : list Sym :=
  match xs with
  | [] => []
  | d :: xs' => encWord d ++ encList xs'
  end.

Lemma encList_app (x y : list LD) :
  encList (x ++ y) = encList x ++ encList y.
Proof.
  induction x as [| d xs IH]; [reflexivity |].
  cbn [app encList]. rewrite IH, app_assoc. reflexivity.
Qed.

Definition Lmp (x : list LD) : side :=
  encList x *> ([S1; S1; S1; S1; S1; S1] *> 0inf).

Arguments Lmp _ : simpl never.

Lemma Lmp_nil :
  Lmp [] = [S1; S1; S1; S1; S1; S1] *> 0inf.
Proof. reflexivity. Qed.

Lemma Lmp_cons (d : LD) (xs : list LD) :
  Lmp (d :: xs) = encWord d *> Lmp xs.
Proof.
  unfold Lmp. cbn [encList]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma Lmp_W0 (xs : list LD) :
  Lmp (W0 :: xs) = S1 >> S0 >> S0 >> Lmp xs.
Proof. rewrite Lmp_cons. reflexivity. Qed.

Lemma Lmp_W1 (xs : list LD) :
  Lmp (W1 :: xs) = S1 >> S1 >> S1 >> Lmp xs.
Proof. rewrite Lmp_cons. reflexivity. Qed.

Lemma Lmp_hd (x : list LD) : hd (Lmp x) = S1.
Proof. destruct x as [| [] xs]; reflexivity. Qed.

Lemma Lmp_cons_tl (x : list LD) : S1 >> tl (Lmp x) = Lmp x.
Proof. rewrite <- (Lmp_hd x), <- Cons_unfold. reflexivity. Qed.

Definition RC (m : nat) : side :=
  [S1] *> ((([S0; S1; S1] ^^ m) *> ([S0; S1] *> 0inf))).

Definition cfgL (l r : side) : Q * tape :=
  l {{E}}> ([S1; S0; S1; S0] *> r).

Definition cfgR (l r : side) : Q * tape :=
  l {{C}}> ([S1; S1] *> r).

Definition cfgC (l r : side) : Q * tape :=
  l {{C}}> ([S1] *> r).

Lemma zeros_app_0inf (k : nat) : ([S0] ^^ k) *> 0inf = 0inf.
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [lpow app Str_app]. rewrite IH, <- const_unfold. reflexivity.
Qed.

Record CCfg : Type := mkCCfg {
  cc_q : Q;
  cc_cur : Sym;
  cc_l : list Sym;
  cc_r : list Sym
}.

Definition evalCCfg (r_tail : side) (c : CCfg) : Q * tape :=
  (cc_q c;; (cc_l c *> 0inf) {{cc_cur c}} (cc_r c *> r_tail)).

Definition cstep (c : CCfg) : option CCfg :=
  match tm (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    match cc_l c with
    | [] => Some (mkCCfg q' S0 [] (w :: cc_r c))
    | b :: ls => Some (mkCCfg q' b ls (w :: cc_r c))
    end
  | Some (w, R, q') =>
    match cc_r c with
    | [] => None
    | b :: rs => Some (mkCCfg q' b (w :: cc_l c) rs)
    end
  end.

Lemma cstep_sound (c c' : CCfg) (r_tail : side) :
  cstep c = Some c' -> evalCCfg r_tail c --> evalCCfg r_tail c'.
Proof.
  unfold cstep.
  destruct (tm (cc_q c, cc_cur c)) as [[[w d] q'] |] eqn:Htm; [| intros; discriminate].
  destruct d.
  - destruct (cc_l c) as [| b ls] eqn:Hl; intros H; inversion H; subst; clear H;
      unfold evalCCfg; cbn [cc_q cc_cur cc_l cc_r]; rewrite Hl; cbn [Str_app].
    + change (q';; 0inf {{S0}} (w >> (cc_r c *> r_tail)))
        with (q';; move_left (0inf {{w}} (cc_r c *> r_tail))).
      exact (step_left Htm).
    + change (q';; (ls *> 0inf) {{b}} (w >> (cc_r c *> r_tail)))
        with (q';; move_left ((b >> (ls *> 0inf)) {{w}} (cc_r c *> r_tail))).
      exact (step_left Htm).
  - destruct (cc_r c) as [| b rs] eqn:Hr; intros H; [discriminate |];
      inversion H; subst; clear H;
      unfold evalCCfg; cbn [cc_q cc_cur cc_l cc_r]; rewrite Hr; cbn [Str_app].
    change (q';; (w >> (cc_l c *> 0inf)) {{b}} (rs *> r_tail))
      with (q';; move_right ((cc_l c *> 0inf) {{w}} (b >> (rs *> r_tail)))).
    exact (step_right Htm).
Qed.

Fixpoint cmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | 0 => Some c
  | S n' =>
    match cstep c with
    | None => None
    | Some c1 => cmultiStep n' c1
    end
  end.

Lemma cmultiStep_sound (n : nat) : forall (c c' : CCfg) (r_tail : side),
  cmultiStep n c = Some c' -> evalCCfg r_tail c -->* evalCCfg r_tail c'.
Proof.
  induction n as [| n IH]; intros c c' r_tail H.
  - cbn [cmultiStep] in H. inversion H; subst. apply evstep_refl.
  - cbn [cmultiStep] in H.
    destruct (cstep c) as [c1 |] eqn:H1; [| discriminate].
    eapply evstep_step; [apply (cstep_sound c c1 r_tail H1) | apply (IH c1 c' r_tail H)].
Qed.

Ltac norm_lmp :=
  unfold cfgL, cfgR, cfgC, RC;
  repeat rewrite Lmp_W0;
  repeat rewrite Lmp_W1;
  try rewrite Lmp_nil;
  autorewrite with tape_pre;
  cbn [lpow app Str_app hd tl];
  autorewrite with tape_post;
  repeat rewrite Lmp_hd;
  repeat rewrite Lmp_cons_tl.

Tactic Notation "run_steps" integer(n) :=
  norm_lmp;
  do n (step; repeat rewrite Lmp_hd; repeat rewrite Lmp_cons_tl);
  norm_lmp;
  finish.

Lemma LInc_w0_1 (xs : list LD) (r : side) :
  cfgL (Lmp (W0 :: xs)) ([S1] *> r) -->* cfgL (Lmp xs) ([S1; S0; S1; S1] *> r).
Proof. run_steps 19. Qed.

Lemma LInc_w10 (xs : list LD) (r : side) :
  cfgL (Lmp (W1 :: W0 :: xs)) ([S1] *> r) -->* cfgR (Lmp (W1 :: W1 :: xs)) ([S0; S1; S1] *> r).
Proof. run_steps 40. Qed.

Lemma LInc_w11_1 (xs : list LD) (r : side) :
  cfgL (Lmp (W1 :: W1 :: xs)) ([S1] *> r) -->* cfgL (Lmp xs) ([S1; S0; S1; S0; S1; S0; S1] *> r).
Proof. run_steps 6. Qed.

Lemma RInc_w0 (xs : list LD) (r : side) :
  cfgR (Lmp xs) ([S0; S1; S1] *> r) -->* cfgR (Lmp (W0 :: xs)) r.
Proof. run_steps 3. Qed.

Lemma RInc_w11 (xs' : list LD) (r : side) :
  cfgR (Lmp xs') ([S0; S1; S1; S0; S1; S0; S1; S0; S1] *> r) -->*
    cfgR (Lmp (W1 :: W0 :: xs')) ([S0; S1; S1] *> r).
Proof. run_steps 28. Qed.

Lemma RC_turn_48 (x : list LD) :
  cfgR (Lmp x) ([S0; S1] *> 0inf) -->* cfgL (Lmp x) (RC 1).
Proof. run_steps 48. Qed.

Lemma lov_nil_48 (r : side) :
  cfgL (Lmp []) ([S1] *> r) -->* cfgC (Lmp [W0; W0]) r.
Proof. run_steps 48. Qed.

Lemma lov_w0_7 (u : list LD) (r : side) :
  cfgC (Lmp u) ([S0; S1; S1] *> r) -->* cfgC (Lmp (W1 :: u)) r.
Proof. run_steps 7. Qed.

Lemma lov_w11_0_28 (x : list LD) (r : side) :
  cfgC (Lmp (W0 :: x)) ([S0; S1; S0; S1; S0; S1] *> r) -->*
    cfgC (Lmp (W0 :: W0 :: W1 :: x)) r.
Proof. run_steps 28. Qed.

Lemma lov_w11_1_start (z : list LD) (r : side) :
  cfgC (Lmp (W1 :: z)) ([S0; S1; S0; S1; S0; S1] *> r) -->*
    cfgL (Lmp z) ([S1; S0; S1; S1; S0; S1] *> r).
Proof. run_steps 13. Qed.

Lemma lov_w11_1_end (z' : list LD) (r : side) :
  cfgR (Lmp z') ([S0; S1; S1; S0; S1; S1; S0; S1] *> r) -->*
    cfgC (Lmp (W0 :: W0 :: W0 :: z')) r.
Proof. run_steps 9. Qed.

Lemma lov_finish_13 (y : list LD) :
  cfgC (Lmp (W1 :: y)) ([S0; S1] *> 0inf) -->* cfgL (Lmp y) (RC 0).
Proof. run_steps 13. Qed.

Inductive LInc : list LD -> list LD -> Prop :=
  | LInc_c_w0 xs xs' : LInc xs xs' -> LInc (W0 :: xs) (W0 :: xs')
  | LInc_c_w10 xs : LInc (W1 :: W0 :: xs) (W1 :: W1 :: xs)
  | LInc_c_w11 xs xs' : LInc xs xs' -> LInc (W1 :: W1 :: xs) (W1 :: W0 :: xs').

Lemma LInc_append {x x' : list LD} (h : LInc x x') (s : list LD) :
  LInc (x ++ s) (x' ++ s).
Proof.
  induction h as [xs xs' _ IH | xs | xs xs' _ IH].
  - cbn [app]. exact (LInc_c_w0 _ _ IH).
  - cbn [app]. exact (LInc_c_w10 (xs ++ s)).
  - cbn [app]. exact (LInc_c_w11 _ _ IH).
Qed.

Lemma LInc_pow_11_10 (m : nat) (xs : list LD) :
  LInc (([W1; W1] ^^ m) ++ (W1 :: W0 :: xs))
       (([W1; W0] ^^ m) ++ (W1 :: W1 :: xs)).
Proof.
  induction m as [| m IH]; cbn [lpow app].
  - exact (LInc_c_w10 xs).
  - exact (LInc_c_w11 _ _ IH).
Qed.

Lemma pow_W1_odd (m : nat) (s : list LD) :
  ([W1] ^^ (2 * m + 1)) ++ s = ([W1; W1] ^^ m) ++ (W1 :: s).
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * S m + 1) with (2 + (2 * m + 1)) by lia.
    rewrite lpow_add, <- app_assoc, IH. reflexivity.
Qed.

Lemma LInc_step {x x' : list LD} (h : LInc x x') : forall (r : side),
  cfgL (Lmp x) ([S1] *> r) -->* cfgR (Lmp x') ([S0; S1; S1] *> r).
Proof.
  induction h as [xs xs' _ IH | xs | xs xs' _ IH]; intro r.
  - eapply evstep_trans; [apply LInc_w0_1 |].
    change ([S1; S0; S1; S1] *> r) with ([S1] *> ([S0; S1; S1] *> r)).
    eapply evstep_trans; [apply IH |].
    apply RInc_w0.
  - apply LInc_w10.
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply IH |].
    change ([S0; S1; S1] *> ([S0; S1; S0; S1; S0; S1] *> r))
      with ([S0; S1; S1; S0; S1; S0; S1; S0; S1] *> r).
    apply RInc_w11.
Qed.

Lemma RC_return (m : nat) : forall (x : list LD),
  cfgR (Lmp x) (([S0; S1; S1] ^^ m) *> ([S0; S1] *> 0inf)) -->* cfgL (Lmp x) (RC (m + 1)).
Proof.
  induction m as [| m IH]; intro x.
  - cbn [lpow Str_app]. replace (0 + 1) with 1 by lia. apply RC_turn_48.
  - cbn [lpow]. rewrite Str_app_assoc.
    eapply evstep_trans; [apply RInc_w0 |].
    eapply evstep_trans; [apply IH |].
    unfold RC.
    eapply evstep_trans; [apply LInc_w0_1 |].
    replace (S m + 1) with (S (m + 1)) by lia.
    change ([S1; S0; S1; S1] *> (([S0; S1; S1] ^^ (m + 1)) *> ([S0; S1] *> 0inf)))
      with ([S1] *> ([S0; S1; S1] *> (([S0; S1; S1] ^^ (m + 1)) *> ([S0; S1] *> 0inf)))).
    rewrite <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma LInc_RC {x x' : list LD} (h : LInc x x') (m : nat) :
  cfgL (Lmp x) (RC m) -->* cfgL (Lmp x') (RC (m + 2)).
Proof.
  unfold RC at 1.
  eapply evstep_trans; [apply (LInc_step h) |].
  replace (m + 2) with (S m + 1) by lia.
  exact (RC_return (S m) x').
Qed.

Inductive LIncs : nat -> list LD -> list LD -> Prop :=
  | LIncs_zero x : LIncs 0 x x
  | LIncs_succ n x y z : LInc x y -> LIncs n y z -> LIncs (S n) x z.

Lemma LIncs_RC {n : nat} {x x' : list LD} (h : LIncs n x x') : forall (m : nat),
  cfgL (Lmp x) (RC m) -->* cfgL (Lmp x') (RC (m + 2 * n)).
Proof.
  induction h as [x | n x y z h1 _ IH]; intro m.
  - replace (m + 2 * 0) with m by lia. apply evstep_refl.
  - replace (m + 2 * S n) with ((m + 2) + 2 * n) by lia.
    eapply evstep_trans; [apply (LInc_RC h1 m) | apply (IH (m + 2))].
Qed.

Lemma LIncs_w0 {n : nat} {xs xs' : list LD} (h : LIncs n xs xs') :
  LIncs n (W0 :: xs) (W0 :: xs').
Proof.
  induction h as [xs | n x y z h1 _ IH].
  - exact (LIncs_zero (W0 :: xs)).
  - exact (LIncs_succ _ _ _ _ (LInc_c_w0 _ _ h1) IH).
Qed.

Lemma LIncs_w11 {n : nat} {xs xs' : list LD} (h : LIncs n xs xs') :
  LIncs (2 * n) (W1 :: W1 :: xs) (W1 :: W1 :: xs').
Proof.
  induction h as [xs | n x y z h1 _ IH].
  - exact (LIncs_zero (W1 :: W1 :: xs)).
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    exact (LIncs_succ _ _ _ _ (LInc_c_w11 _ _ h1)
            (LIncs_succ _ _ _ _ (LInc_c_w10 y) IH)).
Qed.

Lemma LIncs_w10 {n : nat} {xs xs' : list LD} (h : LIncs n xs xs') :
  LIncs (2 * n + 1) (W1 :: W0 :: xs) (W1 :: W1 :: xs').
Proof.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  exact (LIncs_succ _ _ _ _ (LInc_c_w10 xs) (LIncs_w11 h)).
Qed.

Inductive LIncsP : nat -> list LD -> list LD -> Prop :=
  | LIncsP_nil : LIncsP 0 [] []
  | LIncsP_w0 n xs xs' : LIncsP n xs xs' -> LIncsP n (W0 :: xs) (W0 :: xs')
  | LIncsP_w10 n xs xs' : LIncsP n xs xs' -> LIncsP (2 * n + 1) (W1 :: W0 :: xs) (W1 :: W1 :: xs')
  | LIncsP_w11 n xs xs' : LIncsP n xs xs' -> LIncsP (2 * n) (W1 :: W1 :: xs) (W1 :: W1 :: xs').

Lemma LIncsP_to_LIncs {n : nat} {x x' : list LD} (h : LIncsP n x x') : LIncs n x x'.
Proof.
  induction h as [| n xs xs' _ IH | n xs xs' _ IH | n xs xs' _ IH].
  - exact (LIncs_zero []).
  - exact (LIncs_w0 IH).
  - exact (LIncs_w10 IH).
  - exact (LIncs_w11 IH).
Qed.

Lemma LIncsP_append {m : nat} {a a' : list LD} (ha : LIncsP m a a') :
  forall {n : nat} {b b' : list LD}, LIncsP n b b' -> exists k, LIncsP k (a ++ b) (a' ++ b').
Proof.
  induction ha as [| m xs xs' _ IH | m xs xs' _ IH | m xs xs' _ IH]; intros n b b' hb.
  - exists n. exact hb.
  - destruct (IH _ _ _ hb) as [k hk]. exists k. exact (LIncsP_w0 _ _ _ hk).
  - destruct (IH _ _ _ hb) as [k hk]. exists (2 * k + 1). exact (LIncsP_w10 _ _ _ hk).
  - destruct (IH _ _ _ hb) as [k hk]. exists (2 * k). exact (LIncsP_w11 _ _ _ hk).
Qed.

Lemma LIncsP_pow_10 (k : nat) : forall {n : nat} {xs xs' : list LD},
  LIncsP n xs xs' ->
  exists m, LIncsP m (([W1; W0] ^^ k) ++ xs) (([W1; W1] ^^ k) ++ xs').
Proof.
  induction k as [| k IH]; intros n xs xs' h.
  - exists n. exact h.
  - destruct (IH _ _ _ h) as [m hm].
    exists (2 * m + 1). cbn [lpow app]. exact (LIncsP_w10 _ _ _ hm).
Qed.

Lemma LIncsP_pow9_bound {n : nat} {xs xs' : list LD} (h : LIncsP n xs xs') :
  LIncsP (512 * n + 511)
    (([W1; W0] ^^ 9) ++ xs)
    (([W1; W1] ^^ 9) ++ xs').
Proof.
  pose proof (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _
    (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _
    (LIncsP_w10 _ _ _ h))))))))) as H9.
  replace (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * n + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    with (512 * n + 511) in H9 by lia.
  exact H9.
Qed.

Lemma LIncsP_pow10_bound {n : nat} {xs xs' : list LD} (h : LIncsP n xs xs') :
  LIncsP (2 * (512 * n + 511) + 1)
    (([W1; W0] ^^ 10) ++ xs)
    (([W1; W1] ^^ 10) ++ xs').
Proof.
  pose proof (LIncsP_w10 _ _ _ (LIncsP_pow9_bound h)) as H10.
  exact H10.
Qed.

Inductive LOv2 : list LD -> list LD -> list LD -> Prop :=
  | LOv2_nil u : LOv2 [] u u
  | LOv2_w0 xs u u' : LOv2 xs u u' -> LOv2 (W0 :: xs) u (W1 :: u')
  | LOv2_w11_0 xs u x :
      LOv2 xs u (W0 :: x) ->
      LOv2 (W1 :: W1 :: xs) u (W0 :: W0 :: W1 :: x)
  | LOv2_w11_1 xs u z z' :
      LOv2 xs u (W1 :: z) -> LInc z z' ->
      LOv2 (W1 :: W1 :: xs) u (W0 :: W0 :: W0 :: z').

Lemma LOv2_append {a b u v w : list LD} (ha : LOv2 a v w) (hb : LOv2 b u v) :
  LOv2 (a ++ b) u w.
Proof.
  revert hb.
  induction ha as [v | xs v u' _ IH | xs v x _ IH | xs v z z' _ IH hz]; intro hb.
  - exact hb.
  - exact (LOv2_w0 _ _ _ (IH hb)).
  - exact (LOv2_w11_0 _ _ _ (IH hb)).
  - exact (LOv2_w11_1 _ _ _ _ (IH hb) hz).
Qed.

Lemma LOv2_suffix {w u y : list LD} (h : LOv2 w u y) (s : list LD) :
  LOv2 w (u ++ s) (y ++ s).
Proof.
  induction h as [u | xs u u' _ IH | xs u x _ IH | xs u z z' _ IH hz].
  - exact (LOv2_nil (u ++ s)).
  - exact (LOv2_w0 _ _ _ IH).
  - exact (LOv2_w11_0 _ _ _ IH).
  - exact (LOv2_w11_1 _ _ _ _ IH (LInc_append hz s)).
Qed.

Lemma LOv2_pow_11 (k : nat) (s : list LD) :
  LOv2 ([W1; W1] ^^ k)
    ([W0; W0; W1; W0] ++ s)
    ([W0; W0; W1; W0] ++ (([W1; W0] ^^ k) ++ s)).
Proof.
  induction k as [| k IH]; cbn [lpow app].
  - exact (LOv2_nil _).
  - exact (LOv2_w11_0 _ _ _ IH).
Qed.

Lemma LOv2_correct_aux {w u y : list LD} (h : LOv2 w u y) (hu : u = [W0; W0]) :
  forall (r : side),
    cfgL (Lmp w) ([S1] *> r) -->* cfgC (Lmp y) r.
Proof.
  revert hu.
  induction h as [u | xs u u' _ IH | xs u x _ IH | xs u z z' _ IH hz]; intros hu r.
  - subst u. apply lov_nil_48.
  - eapply evstep_trans; [apply LInc_w0_1 |].
    change ([S1; S0; S1; S1] *> r) with ([S1] *> ([S0; S1; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) | apply lov_w0_7].
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) | apply lov_w11_0_28].
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) |].
    eapply evstep_trans; [apply lov_w11_1_start |].
    change ([S1; S0; S1; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (LInc_step hz) |].
    change ([S0; S1; S1] *> ([S0; S1; S1; S0; S1] *> r))
      with ([S0; S1; S1; S0; S1; S1; S0; S1] *> r).
    apply lov_w11_1_end.
Qed.

Lemma LOv2_correct {w y : list LD} (h : LOv2 w [W0; W0] y) (r : side) :
  cfgL (Lmp w) ([S1] *> r) -->* cfgC (Lmp y) r.
Proof. apply (LOv2_correct_aux h eq_refl). Qed.

Lemma lpow_succ_r {A : Type} (l : list A) (m : nat) :
  l ^^ (S m) = (l ^^ m) ++ l.
Proof.
  replace (S m) with (m + 1) by lia.
  rewrite lpow_add. cbn [lpow app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma lov_w0_iter (m : nat) : forall (y : list LD) (r : side),
  cfgC (Lmp y) (([S0; S1; S1] ^^ m) *> r) -->*
    cfgC (Lmp (([W1] ^^ m) ++ y)) r.
Proof.
  induction m as [| m IH]; intros y r.
  - cbn [lpow Str_app app]. apply evstep_refl.
  - rewrite lpow_succ_r, Str_app_assoc.
    eapply evstep_trans; [apply IH |].
    cbn [lpow app].
    apply lov_w0_7.
Qed.

Lemma full_overflow_step {w y : list LD} (m : nat) (h : LOv2 w [W0; W0] y) :
  cfgL (Lmp w) (RC (m + 1)) -->* cfgL (Lmp (([W1] ^^ m) ++ y)) (RC 0).
Proof.
  unfold RC at 1.
  eapply evstep_trans; [apply (LOv2_correct h) |].
  replace (m + 1) with (S m) by lia.
  eapply evstep_trans; [apply (lov_w0_iter (S m)) |].
  cbn [lpow app].
  apply lov_finish_13.
Qed.

Lemma round_step {X X' Y Z : list LD} (m : nat)
    (h1 : LIncsP m X X')
    (h2 : LOv2 X' [W0; W0] Y)
    (h3 : LInc (([W1] ^^ (2 * m + 1)) ++ Y) Z) :
  cfgL (Lmp X) (RC 2) -->* cfgL (Lmp Z) (RC 2).
Proof.
  pose proof (LIncs_RC (LIncsP_to_LIncs h1) 2) as H_incs.
  replace (2 + 2 * m) with ((2 * m + 1) + 1) in H_incs by lia.
  eapply evstep_trans; [exact H_incs |].
  eapply evstep_trans; [apply (full_overflow_step (2 * m + 1) h2) |].
  apply (LInc_RC h3 0).
Qed.

Lemma list_LD_ind2 (P : list LD -> Prop)
    (Hnil : P [])
    (Hw0 : forall xs, P xs -> P (W0 :: xs))
    (Hw1_nil : P [W1])
    (Hw10 : forall xs, P xs -> P (W1 :: W0 :: xs))
    (Hw11 : forall xs, P xs -> P (W1 :: W1 :: xs)) :
  forall x, P x.
Proof.
  assert (Hboth : forall x, P x /\ (forall d, P (d :: x))).
  { induction x as [| d1 xs [IH1 IH2]].
    - split; [exact Hnil | intros []; [exact (Hw0 [] Hnil) | exact Hw1_nil]].
    - split; [exact (IH2 d1) |].
      intros []; [exact (Hw0 (d1 :: xs) (IH2 d1)) |].
      destruct d1; [exact (Hw10 xs IH1) | exact (Hw11 xs IH1)]. }
  intro x. apply (proj1 (Hboth x)).
Qed.

Fixpoint lincFinite (x : list LD) : option (list LD) :=
  match x with
  | [] => None
  | W0 :: xs => option_map (cons W0) (lincFinite xs)
  | [W1] => None
  | W1 :: W0 :: xs => Some (W1 :: W1 :: xs)
  | W1 :: W1 :: xs => option_map (fun ys => W1 :: W0 :: ys) (lincFinite xs)
  end.

Lemma lincFinite_sound (x : list LD) : forall x',
  lincFinite x = Some x' -> LInc x x'.
Proof.
  induction x as [| xs IH | | xs _ | xs IH] using list_LD_ind2; intros x' H; cbn [lincFinite] in H.
  - discriminate.
  - destruct (lincFinite xs) as [xs' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LInc_c_w0 _ _ (IH _ eq_refl)).
  - discriminate.
  - inversion H; subst. exact (LInc_c_w10 xs).
  - destruct (lincFinite xs) as [xs' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LInc_c_w11 _ _ (IH _ eq_refl)).
Qed.

Fixpoint lincspFinite (x : list LD) : option (list LD) :=
  match x with
  | [] => Some []
  | W0 :: xs => option_map (cons W0) (lincspFinite xs)
  | [W1] => None
  | W1 :: W0 :: xs => option_map (fun ys => W1 :: W1 :: ys) (lincspFinite xs)
  | W1 :: W1 :: xs => option_map (fun ys => W1 :: W1 :: ys) (lincspFinite xs)
  end.

Fixpoint lincspCount (x : list LD) : nat :=
  match x with
  | [] => 0
  | W0 :: xs => lincspCount xs
  | [W1] => 0
  | W1 :: W0 :: xs => 2 * lincspCount xs + 1
  | W1 :: W1 :: xs => 2 * lincspCount xs
  end.

Lemma lincspFinite_sound (x : list LD) : forall x',
  lincspFinite x = Some x' -> LIncsP (lincspCount x) x x'.
Proof.
  induction x as [| xs IH | | xs IH | xs IH] using list_LD_ind2; intros x' H;
    cbn [lincspFinite lincspCount] in *.
  - inversion H; subst. exact LIncsP_nil.
  - destruct (lincspFinite xs) as [xs' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LIncsP_w0 _ _ _ (IH _ eq_refl)).
  - discriminate.
  - destruct (lincspFinite xs) as [xs' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LIncsP_w10 _ _ _ (IH _ eq_refl)).
  - destruct (lincspFinite xs) as [xs' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LIncsP_w11 _ _ _ (IH _ eq_refl)).
Qed.

Fixpoint lov2Finite (w u : list LD) : option (list LD) :=
  match w with
  | [] => Some u
  | W0 :: xs => option_map (cons W1) (lov2Finite xs u)
  | [W1] => None
  | W1 :: W0 :: _ => None
  | W1 :: W1 :: xs =>
    match lov2Finite xs u with
    | Some (W0 :: x) => Some (W0 :: W0 :: W1 :: x)
    | Some (W1 :: z) => option_map (fun z' => W0 :: W0 :: W0 :: z') (lincFinite z)
    | _ => None
    end
  end.

Lemma lov2Finite_sound (w : list LD) : forall u y,
  lov2Finite w u = Some y -> LOv2 w u y.
Proof.
  induction w as [| xs IH | | xs _ | xs IH] using list_LD_ind2; intros u y H;
    cbn [lov2Finite] in H.
  - inversion H; subst. exact (LOv2_nil _).
  - destruct (lov2Finite xs u) as [u' |] eqn:Hxs; cbn [option_map] in H; [| discriminate].
    inversion H; subst. exact (LOv2_w0 _ _ _ (IH _ _ Hxs)).
  - discriminate.
  - discriminate.
  - destruct (lov2Finite xs u) as [[| [] tail] |] eqn:Hxs; [discriminate | | | discriminate].
    + inversion H; subst. exact (LOv2_w11_0 _ _ _ (IH _ _ Hxs)).
    + destruct (lincFinite tail) as [z' |] eqn:Hz; cbn [option_map] in H; [| discriminate].
      inversion H; subst.
      exact (LOv2_w11_1 _ _ _ _ (IH _ _ Hxs) (lincFinite_sound _ _ Hz)).
Qed.

Definition opt_get_nil (o : option (list LD)) : list LD :=
  match o with
  | Some xs => xs
  | None => []
  end.

Definition ux2 : list LD :=
  [W1; W1; W0; W1; W0; W0; W1; W1; W0; W0; W0; W0; W1; W1].

Definition x2 : list LD := ([W1; W0] ^^ 9) ++ ux2.

Definition u0_tail : list LD :=
  [W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1;
   W0; W0; W0; W0; W0; W0; W0; W0; W1; W0; W1; W0; W0; W1; W1].

Definition u0 : list LD := W1 :: W1 :: u0_tail.

Definition c_init_104 : CCfg := mkCCfg A S0 [] ([S0] ^^ 104).

Definition c_x2 : CCfg :=
  mkCCfg E S1
    [S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0;
     S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S1; S1;
     S1; S0; S0; S1; S1; S1; S1; S0; S0; S1; S0; S0; S1; S1; S1; S1; S1; S1; S1; S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0;
     S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S1]
    [S0; S1; S0; S1; S0; S1; S1; S0; S1; S1; S0; S1].

Lemma init_to_x2 : c0 -->* cfgL (Lmp x2) (RC 2).
Proof.
  assert (Heq1 : c0 = evalCCfg 0inf c_init_104).
  { unfold c0, evalCCfg, c_init_104. cbn [cc_q cc_cur cc_l cc_r Str_app].
    rewrite zeros_app_0inf. reflexivity. }
  assert (Heq2 : evalCCfg 0inf c_x2 = cfgL (Lmp x2) (RC 2)) by reflexivity.
  assert (Hsteps : cmultiStep (6 * 901) c_init_104 = Some c_x2) by (vm_compute; reflexivity).
  rewrite Heq1, <- Heq2.
  exact (cmultiStep_sound (6 * 901) c_init_104 c_x2 0inf Hsteps).
Qed.

Definition ux2' : list LD := Eval vm_compute in opt_get_nil (lincspFinite ux2).

Lemma x2_to_x3 :
  exists m3, 511 <= m3 /\
    cfgL (Lmp x2) (RC 2) -->* cfgL (Lmp (([W1; W0] ^^ m3) ++ u0)) (RC 2).
Proof.
  assert (H_ux2 : LIncsP (lincspCount ux2) ux2 ux2')
    by (apply (lincspFinite_sound ux2 ux2'); vm_compute; reflexivity).
  pose proof (LIncsP_pow9_bound H_ux2) as H_9.
  set (x2' := ([W1; W1] ^^ 9) ++ ux2').
  assert (H_ov : LOv2 x2' [W0; W0] (W0 :: u0_tail))
    by (apply (lov2Finite_sound x2' [W0; W0] (W0 :: u0_tail)); vm_compute; reflexivity).
  set (m3 := 512 * lincspCount ux2 + 511).
  exists m3. split; [unfold m3; lia |].
  assert (H_inc : LInc (([W1] ^^ (2 * m3 + 1)) ++ (W0 :: u0_tail))
                       (([W1; W0] ^^ m3) ++ u0)).
  { rewrite (pow_W1_odd m3 (W0 :: u0_tail)).
    exact (LInc_pow_11_10 m3 u0_tail). }
  exact (round_step m3 H_9 H_ov H_inc).
Qed.

Definition stepBuffer (b : list LD) : option (list LD) :=
  match lincspFinite b with
  | None => None
  | Some bp =>
    match lov2Finite bp [W0; W0; W1; W0] with
    | Some (W0 :: x) => Some (W1 :: x)
    | Some (W1 :: z) => option_map (cons W0) (lincFinite z)
    | _ => None
    end
  end.

Fixpoint checkBuffer (r : nat) (b : list LD) : bool :=
  match r with
  | 0 =>
    match lincspFinite b with
    | Some _ => true
    | None => false
    end
  | S r' =>
    match stepBuffer b with
    | Some b' => checkBuffer r' b'
    | None => false
    end
  end.

Definition IsBuffer (r : nat) (b : list LD) : Prop := checkBuffer r b = true.

Lemma checkBuffer_mono (r : nat) : forall (b : list LD),
  checkBuffer (S r) b = true -> checkBuffer r b = true.
Proof.
  induction r as [| r IH]; intros b H.
  - cbn [checkBuffer] in *. unfold stepBuffer in H.
    destruct (lincspFinite b); [reflexivity | discriminate].
  - cbn [checkBuffer] in H |- *.
    destruct (stepBuffer b) as [b' |]; [exact (IH b' H) | discriminate].
Qed.

Lemma isBuffer_le {k r : nat} (hkr : k <= r) : forall {b : list LD},
  IsBuffer r b -> IsBuffer k b.
Proof.
  induction r as [| r IH] in k, hkr |- *; intros b hb.
  - assert (k = 0) by lia; subst k; exact hb.
  - destruct (Nat.eq_dec k (S r)) as [-> | Hneq].
    + exact hb.
    + apply (IH k ltac:(lia) b (checkBuffer_mono r b hb)).
Qed.

Lemma isBuffer_8_B1 : IsBuffer 8 [W1; W1; W0].
Proof. vm_compute. reflexivity. Qed.

Lemma stepBuffer_spec {r : nat} {b : list LD} (hb : IsBuffer (S r) b) :
  exists (n : nat) (bp b' : list LD),
    LIncsP n b bp /\
    IsBuffer r b' /\
    forall (s : list LD),
      LOv2 ([W1; W1; W1; W1] ++ bp)
        ([W0; W0; W1; W0] ++ s)
        ([W0; W0; W1; W0] ++ (b' ++ s)).
Proof.
  unfold IsBuffer in hb; cbn [checkBuffer] in hb.
  destruct (stepBuffer b) as [b' |] eqn:Hs; [| discriminate].
  unfold stepBuffer in Hs.
  destruct (lincspFinite b) as [bp |] eqn:Hlp; [| discriminate].
  destruct (lov2Finite bp [W0; W0; W1; W0]) as [[| [] tail] |] eqn:Hov;
    [discriminate | | | discriminate].
  - inversion Hs; subst b'; clear Hs.
    exists (lincspCount b), bp, (W1 :: tail).
    split; [exact (lincspFinite_sound b bp Hlp) |].
    split; [exact hb |].
    intro s.
    pose proof (LOv2_suffix (lov2Finite_sound bp _ _ Hov) s) as Hov_s.
    cbn [app] in Hov_s |- *.
    exact (LOv2_w11_0 _ _ _ (LOv2_w11_0 _ _ _ Hov_s)).
  - destruct (lincFinite tail) as [z' |] eqn:Hz; cbn [option_map] in Hs; [| discriminate].
    inversion Hs; subst b'; clear Hs.
    exists (lincspCount b), bp, (W0 :: z').
    split; [exact (lincspFinite_sound b bp Hlp) |].
    split; [exact hb |].
    intro s.
    pose proof (LOv2_suffix (lov2Finite_sound bp _ _ Hov) s) as Hov_s.
    pose proof (LInc_append (lincFinite_sound tail z' Hz) s) as Hz_s.
    cbn [app] in Hov_s |- *.
    exact (LOv2_w11_0 _ _ _ (LOv2_w11_1 _ _ _ _ Hov_s Hz_s)).
Qed.

Definition macroStepFinite (u : list LD) : option (list LD) :=
  match lincspFinite u with
  | None => None
  | Some up =>
    match lov2Finite up [W0; W0] with
    | Some (W0 :: x) => Some (W1 :: x)
    | Some (W1 :: z) => option_map (cons W0) (lincFinite z)
    | _ => None
    end
  end.

Lemma macroStepFinite_spec {u u' : list LD} (h : macroStepFinite u = Some u') :
  exists (n : nat) (up : list LD),
    LIncsP n u up /\
    LOv2 ([W1; W1; W1; W1] ++ up) [W0; W0] ([W0; W0; W1; W0] ++ u').
Proof.
  unfold macroStepFinite in h.
  destruct (lincspFinite u) as [up |] eqn:Hlp; [| discriminate].
  destruct (lov2Finite up [W0; W0]) as [[| [] tail] |] eqn:Hov;
    [discriminate | | | discriminate].
  - inversion h; subst u'; clear h.
    exists (lincspCount u), up.
    split; [exact (lincspFinite_sound u up Hlp) |].
    cbn [app].
    exact (LOv2_w11_0 _ _ _ (LOv2_w11_0 _ _ _ (lov2Finite_sound up _ _ Hov))).
  - destruct (lincFinite tail) as [z' |] eqn:Hz; cbn [option_map] in h; [| discriminate].
    inversion h; subst u'; clear h.
    exists (lincspCount u), up.
    split; [exact (lincspFinite_sound u up Hlp) |].
    cbn [app].
    exact (LOv2_w11_0 _ _ _ (LOv2_w11_1 _ _ _ _ (lov2Finite_sound up _ _ Hov)
            (lincFinite_sound tail z' Hz))).
Qed.

Inductive ChainTail (r : nat) : list LD -> Prop :=
  | CT_nil : ChainTail r ([W1; W0] ^^ (2 * r))
  | CT_pair T : ChainTail r T -> ChainTail r (W1 :: W0 :: T)
  | CT_buf B T :
      IsBuffer r B -> ChainTail r T ->
      ChainTail r (([W1; W0] ^^ (2 * r)) ++ (B ++ T)).

Lemma ChainTail_pow_pair (k : nat) : forall {r : nat} {T : list LD},
  ChainTail r T -> ChainTail r (([W1; W0] ^^ k) ++ T).
Proof.
  induction k as [| k IH]; intros r T h; cbn [lpow app].
  - exact h.
  - exact (CT_pair r _ (IH _ _ h)).
Qed.

Lemma ChainTail_step {r : nat} {T : list LD} (hT : ChainTail (S r) T)
    {u u' : list LD} (hu : macroStepFinite u = Some u') :
  exists (n : nat) (W' T' : list LD),
    LIncsP n (T ++ u) W' /\
    LOv2 W' [W0; W0] ([W0; W0; W1; W0] ++ (T' ++ u')) /\
    ChainTail r T'.
Proof.
  induction hT as [| T0 _ IH | B T0 hB _ IH].
  - destruct (macroStepFinite_spec hu) as [nu [up [h_up h_ovu]]].
    assert (H2 : (([W1; W0] ^^ (2 * S r)) ++ u) =
                 (([W1; W0] ^^ (2 * r)) ++ ([W1; W0; W1; W0] ++ u))).
    { replace (2 * S r) with (2 * r + 2) by lia.
      rewrite lpow_add, <- app_assoc. reflexivity. }
    rewrite H2.
    assert (Hlp2 : LIncsP (2 * (2 * nu + 1) + 1) ([W1; W0; W1; W0] ++ u) ([W1; W1; W1; W1] ++ up))
      by (cbn [app]; exact (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ h_up))).
    destruct (LIncsP_pow_10 (2 * r) Hlp2) as [n_all h_all].
    exists n_all, (([W1; W1] ^^ (2 * r)) ++ ([W1; W1; W1; W1] ++ up)), ([W1; W0] ^^ (2 * r)).
    split; [exact h_all |].
    split; [exact (LOv2_append (LOv2_pow_11 (2 * r) u') h_ovu) | exact (CT_nil r)].
  - destruct IH as [n0 [W0' [T0' [h_lp0 [h_ov0 h_ct0]]]]].
    exists (2 * n0 + 1), (W1 :: W1 :: W0'), (W1 :: W0 :: T0').
    cbn [app] in h_ov0 |- *.
    split; [exact (LIncsP_w10 _ _ _ h_lp0) |].
    split; [exact (LOv2_w11_0 _ _ _ h_ov0) | exact (CT_pair r _ h_ct0)].
  - destruct IH as [n0 [W0' [T0' [h_lp0 [h_ov0 h_ct0]]]]].
    destruct (stepBuffer_spec hB) as [nB [bp [B' [h_lpB [hB' h_ovB]]]]].
    assert (H2 : ((([W1; W0] ^^ (2 * S r)) ++ (B ++ T0)) ++ u) =
                 (([W1; W0] ^^ (2 * r)) ++ (([W1; W0; W1; W0] ++ B) ++ (T0 ++ u)))).
    { replace (2 * S r) with (2 * r + 2) by lia.
      rewrite lpow_add. repeat rewrite <- app_assoc. reflexivity. }
    rewrite H2.
    assert (HlpB2 : LIncsP (2 * (2 * nB + 1) + 1) ([W1; W0; W1; W0] ++ B) ([W1; W1; W1; W1] ++ bp))
      by (cbn [app]; exact (LIncsP_w10 _ _ _ (LIncsP_w10 _ _ _ h_lpB))).
    destruct (LIncsP_append HlpB2 h_lp0) as [n_mid h_mid].
    destruct (LIncsP_pow_10 (2 * r) h_mid) as [n_all h_all].
    exists n_all,
           (([W1; W1] ^^ (2 * r)) ++ (([W1; W1; W1; W1] ++ bp) ++ W0')),
           (([W1; W0] ^^ (2 * r)) ++ (B' ++ T0')).
    split; [exact h_all |].
    split; [| exact (CT_buf r _ _ hB' h_ct0)].
    pose proof (LOv2_append (h_ovB (T0' ++ u')) h_ov0) as h_ov_mid.
    pose proof (LOv2_append (LOv2_pow_11 (2 * r) (B' ++ (T0' ++ u'))) h_ov_mid) as h_ov_top.
    repeat rewrite <- app_assoc in h_ov_top.
    repeat rewrite <- app_assoc.
    exact h_ov_top.
Qed.

Lemma chain_round_step {r : nat} (hr : r <= 8) {T : list LD} (hT : ChainTail (S r) T)
    {u u' : list LD} (hu : macroStepFinite u = Some u') :
  exists T', ChainTail r T' /\
    cfgL (Lmp (([W1; W0] ^^ 10) ++ (T ++ u))) (RC 2) -->*
    cfgL (Lmp (([W1; W0] ^^ 10) ++ (T' ++ u'))) (RC 2).
Proof.
  destruct (ChainTail_step hT hu) as [n [W' [T0' [h_lp [h_ov h_ct0]]]]].
  pose proof (LIncsP_pow10_bound h_lp) as h_10.
  pose proof (LOv2_append (LOv2_pow_11 10 (T0' ++ u')) h_ov) as h_ov10.
  set (m := 2 * (512 * n + 511) + 1).
  set (B1 := [W1; W1; W0]).
  set (tail_rest := ([W1; W0] ^^ 11) ++ (T0' ++ u')).
  assert (h_inc : LInc (([W1] ^^ (2 * m + 1)) ++
                       ([W0; W0; W1; W0] ++ (([W1; W0] ^^ 10) ++ (T0' ++ u'))))
                       (([W1; W0] ^^ m) ++ (B1 ++ tail_rest))).
  { unfold B1, tail_rest.
    rewrite pow_W1_odd.
    exact (LInc_pow_11_10 m ([W0; W1; W0] ++ (([W1; W0] ^^ 10) ++ (T0' ++ u')))). }
  pose proof (round_step m h_10 h_ov10 h_inc) as h_step.
  assert (hm_split : m = 10 + ((m - 10 - 2 * r) + 2 * r)) by (unfold m; lia).
  set (T' := ([W1; W0] ^^ (m - 10 - 2 * r)) ++
             (([W1; W0] ^^ (2 * r)) ++ (B1 ++ (([W1; W0] ^^ 11) ++ T0')))).
  assert (hB1 : IsBuffer r B1) by (exact (isBuffer_le hr isBuffer_8_B1)).
  assert (h_ct_T' : ChainTail r T')
    by (exact (ChainTail_pow_pair (m - 10 - 2 * r)
                (CT_buf r _ _ hB1 (ChainTail_pow_pair 11 h_ct0)))).
  assert (h_eq : (([W1; W0] ^^ m) ++ (B1 ++ tail_rest)) =
                 (([W1; W0] ^^ 10) ++ (T' ++ u'))).
  { rewrite hm_split at 1. rewrite lpow_add, lpow_add.
    unfold T', tail_rest. repeat rewrite <- app_assoc. reflexivity. }
  rewrite h_eq in h_step.
  exists T'. split; [exact h_ct_T' | exact h_step].
Qed.

Fixpoint runU (k : nat) (u : list LD) : option (list LD) :=
  match k with
  | 0 => Some u
  | S k' =>
    match macroStepFinite u with
    | None => None
    | Some u1 => runU k' u1
    end
  end.

Lemma runU_steps (k : nat) : forall (r : nat), r + k <= 8 ->
  forall {T u u' : list LD},
    ChainTail (r + k) T ->
    runU k u = Some u' ->
    exists T', ChainTail r T' /\
      cfgL (Lmp (([W1; W0] ^^ 10) ++ (T ++ u))) (RC 2) -->*
      cfgL (Lmp (([W1; W0] ^^ 10) ++ (T' ++ u'))) (RC 2).
Proof.
  induction k as [| k IH]; intros r hrk T u u' hT hu; cbn [runU] in hu.
  - inversion hu; subst u'. replace (r + 0) with r in hT by lia.
    exists T. split; [exact hT | apply evstep_refl].
  - destruct (macroStepFinite u) as [u1 |] eqn:Hu1; [| discriminate].
    replace (r + S k) with (S (r + k)) in hT by lia.
    destruct (chain_round_step (ltac:(lia) : r + k <= 8) hT Hu1)
      as [T1 [hT1 h_step1]].
    destruct (IH r ltac:(lia) T1 u1 u' hT1 hu) as [T' [hT' h_step2]].
    exists T'. split; [exact hT' | eapply evstep_trans; [exact h_step1 | exact h_step2]].
Qed.

Inductive Only011 : list LD -> Prop :=
  | Only011_nil : Only011 []
  | Only011_w0 xs : Only011 xs -> Only011 (W0 :: xs)
  | Only011_w11 xs : Only011 xs -> Only011 (W1 :: W1 :: xs).

Lemma Only011_append {a b : list LD} (ha : Only011 a) (hb : Only011 b) :
  Only011 (a ++ b).
Proof.
  induction ha as [| xs _ IH | xs _ IH]; cbn [app].
  - exact hb.
  - exact (Only011_w0 _ IH).
  - exact (Only011_w11 _ IH).
Qed.

Lemma LIncsP_only011 {n : nat} {x x' : list LD} (h : LIncsP n x x') : Only011 x'.
Proof.
  induction h as [| n xs xs' _ IH | n xs xs' _ IH | n xs xs' _ IH].
  - exact Only011_nil.
  - exact (Only011_w0 _ IH).
  - exact (Only011_w11 _ IH).
  - exact (Only011_w11 _ IH).
Qed.

Fixpoint checkOnly011 (w : list LD) : bool :=
  match w with
  | [] => true
  | W0 :: xs => checkOnly011 xs
  | [W1] => false
  | W1 :: W0 :: _ => false
  | W1 :: W1 :: xs => checkOnly011 xs
  end.

Lemma checkOnly011_sound (w : list LD) :
  checkOnly011 w = true -> Only011 w.
Proof.
  induction w as [| xs IH | | xs _ | xs IH] using list_LD_ind2; intros H;
    cbn [checkOnly011] in H.
  - exact Only011_nil.
  - exact (Only011_w0 _ (IH H)).
  - discriminate.
  - discriminate.
  - exact (Only011_w11 _ (IH H)).
Qed.

Lemma Only011_skip {P : list LD} (hP : Only011 P) (s : list LD) :
  forall (r : side),
    exists r', cfgL (Lmp (P ++ s)) ([S1] *> r) -->* cfgL (Lmp s) ([S1] *> r').
Proof.
  induction hP as [| xs _ IH | xs _ IH]; intro r; cbn [app].
  - exists r. apply evstep_refl.
  - destruct (IH ([S0; S1; S1] *> r)) as [r' hr'].
    exists r'.
    eapply evstep_trans; [apply (LInc_w0_1 (xs ++ s) r) |].
    change ([S1; S0; S1; S1] *> r) with ([S1] *> ([S0; S1; S1] *> r)).
    exact hr'.
  - destruct (IH ([S0; S1; S0; S1; S0; S1] *> r)) as [r' hr'].
    exists r'.
    eapply evstep_trans; [apply (LInc_w11_1 (xs ++ s) r) |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    exact hr'.
Qed.

Lemma ChainTail_zero_lincsp {T : list LD} (hT : ChainTail 0 T) :
  exists n T', LIncsP n T T'.
Proof.
  induction hT as [| T0 _ IH | B T0 hB _ IH].
  - cbn [Nat.mul lpow]. exists 0, (@nil LD). exact LIncsP_nil.
  - destruct IH as [n [T' h]].
    exists (2 * n + 1), (W1 :: W1 :: T'). exact (LIncsP_w10 _ _ _ h).
  - destruct IH as [n [T' h]].
    cbn [Nat.mul lpow app].
    unfold IsBuffer in hB; cbn [checkBuffer] in hB.
    destruct (lincspFinite B) as [bp |] eqn:Hlp; [| discriminate].
    destruct (LIncsP_append (lincspFinite_sound B bp Hlp) h) as [k hk].
    exists k, (bp ++ T'). exact hk.
Qed.

Definition msb_13 : list LD :=
  [W0; W1; W1; W1; W1; W0; W0; W0; W1; W1; W0; W1; W1].

Definition u8 : list LD := Eval vm_compute in opt_get_nil (runU 8 u0).

Definition u8_pre' : list LD :=
  Eval vm_compute in firstn 38 (opt_get_nil (lincspFinite u8)).

Lemma runU_8_eq : runU 8 u0 = Some u8.
Proof. vm_compute. reflexivity. Qed.

Lemma u8_lincsp_eq : lincspFinite u8 = Some (u8_pre' ++ msb_13).
Proof. vm_compute. reflexivity. Qed.

Lemma u8_pre'_only011 : checkOnly011 u8_pre' = true.
Proof. vm_compute. reflexivity. Qed.

Definition c_msb_start : CCfg :=
  mkCCfg E S1 (encList msb_13 ++ [S1; S1; S1; S1; S1; S1]) [S0; S1; S0; S1].

Definition c_msb_halt : CCfg :=
  Eval vm_compute in
    match cmultiStep 896 c_msb_start with
    | Some c => c
    | None => c_msb_start
    end.

Lemma msb_13_halt (r : side) :
  halts tm (cfgL (Lmp msb_13) ([S1] *> r)).
Proof.
  assert (Hstart : cfgL (Lmp msb_13) ([S1] *> r) = evalCCfg r c_msb_start)
    by reflexivity.
  assert (H896 : cmultiStep 896 c_msb_start = Some c_msb_halt)
    by (vm_compute; reflexivity).
  rewrite Hstart.
  eapply halts_evstep; [| exact (cmultiStep_sound 896 c_msb_start c_msb_halt r H896)].
  apply halted_halts. reflexivity.
Qed.

Lemma step_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Theorem halt: halts tm c0.
Proof.
  destruct x2_to_x3 as [m3 [hm3 H23]].
  pose proof (step_trans init_to_x2 H23) as H_init_x3.
  assert (Hm3_split : m3 = 10 + ((m3 - 26) + 2 * 8)) by lia.
  set (T0 := ([W1; W0] ^^ (m3 - 26)) ++ ([W1; W0] ^^ (2 * 8))).
  assert (H_T0 : ChainTail (0 + 8) T0)
    by (exact (ChainTail_pow_pair (m3 - 26) (CT_nil 8))).
  assert (H_x3_eq : (([W1; W0] ^^ m3) ++ u0) =
                    (([W1; W0] ^^ 10) ++ (T0 ++ u0))).
  { rewrite Hm3_split at 1. rewrite lpow_add, lpow_add.
    unfold T0. repeat rewrite <- app_assoc. reflexivity. }
  rewrite H_x3_eq in H_init_x3.
  destruct (runU_steps 8 0 ltac:(lia) H_T0 runU_8_eq)
    as [T8 [H_T8 H_rounds]].
  pose proof (step_trans H_init_x3 H_rounds) as H_to_8.
  destruct (ChainTail_zero_lincsp H_T8) as [nT [T8' H_lpT]].
  pose proof (lincspFinite_sound u8 _ u8_lincsp_eq) as H_lpU.
  destruct (LIncsP_append H_lpT H_lpU) as [nTU H_lpTU].
  destruct (LIncsP_pow_10 10 H_lpTU) as [nAll H_lpAll].
  pose proof (LIncs_RC (LIncsP_to_LIncs H_lpAll) 2) as H_incs_final.
  pose proof (step_trans H_to_8 H_incs_final) as H_to_inc.
  assert (H_10T_only : Only011 (([W1; W1] ^^ 10) ++ T8')).
  { destruct (LIncsP_pow_10 10 H_lpT) as [n10T H10T].
    exact (LIncsP_only011 H10T). }
  set (P_all := (([W1; W1] ^^ 10) ++ T8') ++ u8_pre').
  assert (H_P_only : Only011 P_all)
    by (exact (Only011_append H_10T_only (checkOnly011_sound u8_pre' u8_pre'_only011))).
  assert (H_assoc : (([W1; W1] ^^ 10) ++ (T8' ++ (u8_pre' ++ msb_13))) =
                    P_all ++ msb_13).
  { unfold P_all. repeat rewrite <- app_assoc. reflexivity. }
  unfold RC in H_to_inc.
  rewrite H_assoc in H_to_inc.
  destruct (Only011_skip H_P_only msb_13
              ((([S0; S1; S1] ^^ (2 + 2 * nAll)) *> ([S0; S1] *> 0inf))))
    as [r' H_skip].
  pose proof (step_trans H_to_inc H_skip) as H_to_msb.
  eapply halts_evstep; [apply msb_13_halt | exact H_to_msb].
Qed.

End TM1.
Print Assumptions TM1.halt.



Module TM2.
Import BusyCoq.Individual62.

Import Lia PeanoNat Bool List String Streams.

Import ListNotations.

Open Scope sym.

Open Scope list.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation LD := TM1.LD.

Notation W0 := TM1.W0.

Notation W1 := TM1.W1.

Notation encWord := TM1.encWord.

Notation encList := TM1.encList.

Notation encList_app := TM1.encList_app.

Notation Lmp := TM1.Lmp.

Arguments Lmp _ : simpl never.

Notation Lmp_nil := TM1.Lmp_nil.

Notation Lmp_cons := TM1.Lmp_cons.

Notation Lmp_W0 := TM1.Lmp_W0.

Notation Lmp_W1 := TM1.Lmp_W1.

Notation Lmp_hd := TM1.Lmp_hd.

Notation Lmp_cons_tl := TM1.Lmp_cons_tl.

Notation RC := TM1.RC.

Definition cfgL (l r : side) : Q * tape :=
  l <{{D}} ([S0; S1; S0] *> r).

Definition cfgR (l r : side) : Q * tape :=
  l {{A}}> ([S1] *> r).

Notation zeros_app_0inf := TM1.zeros_app_0inf.

Notation CCfg := TM1.CCfg.

Notation mkCCfg := TM1.mkCCfg.

Notation cc_q := TM1.cc_q.

Notation cc_cur := TM1.cc_cur.

Notation cc_l := TM1.cc_l.

Notation cc_r := TM1.cc_r.

Notation evalCCfg := TM1.evalCCfg.

Definition cstep (c : CCfg) : option CCfg :=
  match tm (cc_q c, cc_cur c) with
  | None => None
  | Some (w, L, q') =>
    match cc_l c with
    | [] => Some (mkCCfg q' S0 [] (w :: cc_r c))
    | b :: ls => Some (mkCCfg q' b ls (w :: cc_r c))
    end
  | Some (w, R, q') =>
    match cc_r c with
    | [] => None
    | b :: rs => Some (mkCCfg q' b (w :: cc_l c) rs)
    end
  end.

Lemma cstep_sound (c c' : CCfg) (r_tail : side) :
  cstep c = Some c' -> evalCCfg r_tail c --> evalCCfg r_tail c'.
Proof.
  unfold cstep.
  destruct (tm (cc_q c, cc_cur c)) as [[[w d] q'] |] eqn:Htm; [| intros; discriminate].
  destruct d.
  - destruct (cc_l c) as [| b ls] eqn:Hl; intros H; inversion H; subst; clear H;
      unfold evalCCfg; cbn [cc_q cc_cur cc_l cc_r]; rewrite Hl; cbn [Str_app].
    + change (q';; 0inf {{S0}} (w >> (cc_r c *> r_tail)))
        with (q';; move_left (0inf {{w}} (cc_r c *> r_tail))).
      exact (step_left Htm).
    + change (q';; (ls *> 0inf) {{b}} (w >> (cc_r c *> r_tail)))
        with (q';; move_left ((b >> (ls *> 0inf)) {{w}} (cc_r c *> r_tail))).
      exact (step_left Htm).
  - destruct (cc_r c) as [| b rs] eqn:Hr; intros H; [discriminate |];
      inversion H; subst; clear H;
      unfold evalCCfg; cbn [cc_q cc_cur cc_l cc_r]; rewrite Hr; cbn [Str_app].
    change (q';; (w >> (cc_l c *> 0inf)) {{b}} (rs *> r_tail))
      with (q';; move_right ((cc_l c *> 0inf) {{w}} (b >> (rs *> r_tail)))).
    exact (step_right Htm).
Qed.

Fixpoint cmultiStep (n : nat) (c : CCfg) : option CCfg :=
  match n with
  | 0 => Some c
  | S n' =>
    match cstep c with
    | None => None
    | Some c1 => cmultiStep n' c1
    end
  end.

Lemma cmultiStep_sound (n : nat) : forall (c c' : CCfg) (r_tail : side),
  cmultiStep n c = Some c' -> evalCCfg r_tail c -->* evalCCfg r_tail c'.
Proof.
  induction n as [| n IH]; intros c c' r_tail H.
  - cbn [cmultiStep] in H. inversion H; subst. apply evstep_refl.
  - cbn [cmultiStep] in H.
    destruct (cstep c) as [c1 |] eqn:H1; [| discriminate].
    eapply evstep_step; [apply (cstep_sound c c1 r_tail H1) | apply (IH c1 c' r_tail H)].
Qed.

Ltac norm_lmp :=
  unfold cfgL, cfgR, RC;
  repeat rewrite Lmp_W0;
  repeat rewrite Lmp_W1;
  try rewrite Lmp_nil;
  autorewrite with tape_pre;
  cbn [lpow app Str_app hd tl];
  autorewrite with tape_post;
  repeat rewrite Lmp_hd;
  repeat rewrite Lmp_cons_tl.

Tactic Notation "run_steps" integer(n) :=
  norm_lmp;
  do n (step; repeat rewrite Lmp_hd; repeat rewrite Lmp_cons_tl);
  norm_lmp;
  finish.

Lemma LInc_w0_1 (xs : list LD) (r : side) :
  cfgL (Lmp (W0 :: xs)) ([S1] *> r) -->* cfgL (Lmp xs) ([S1; S0; S1; S1] *> r).
Proof. run_steps 19. Qed.

Lemma LInc_w10 (xs : list LD) (r : side) :
  cfgL (Lmp (W1 :: W0 :: xs)) ([S1] *> r) -->* cfgR (Lmp (W1 :: W1 :: xs)) ([S0; S1; S1] *> r).
Proof. run_steps 31. Qed.

Lemma LInc_w11_1 (xs : list LD) (r : side) :
  cfgL (Lmp (W1 :: W1 :: xs)) ([S1] *> r) -->* cfgL (Lmp xs) ([S1; S0; S1; S0; S1; S0; S1] *> r).
Proof. run_steps 12. Qed.

Lemma RInc_w0 (xs : list LD) (r : side) :
  cfgR (Lmp xs) ([S0; S1; S1] *> r) -->* cfgR (Lmp (W0 :: xs)) r.
Proof. run_steps 3. Qed.

Lemma RInc_w11 (xs' : list LD) (r : side) :
  cfgR (Lmp xs') ([S0; S1; S1; S0; S1; S0; S1; S0; S1] *> r) -->*
    cfgR (Lmp (W1 :: W0 :: xs')) ([S0; S1; S1] *> r).
Proof. run_steps 20. Qed.

Lemma RC_turn_25 (x : list LD) :
  cfgR (Lmp x) ([S0; S1] *> 0inf) -->* cfgL (Lmp x) (RC 0).
Proof. run_steps 25. Qed.

Lemma lov_nil_41 (r : side) :
  cfgL (Lmp []) ([S1] *> r) -->* (Lmp [W0; W0] {{A}}> r).
Proof. run_steps 41. Qed.

Lemma lov_w0_3 (u : list LD) (r : side) :
  (Lmp u {{A}}> ([S0; S1; S1] *> r)) -->* (Lmp (W1 :: u) {{A}}> r).
Proof. run_steps 3. Qed.

Lemma lov_w11_0_20 (x : list LD) (r : side) :
  (Lmp (W0 :: x) {{A}}> ([S0; S1; S0; S1; S0; S1] *> r)) -->*
    (Lmp (W0 :: W0 :: W1 :: x) {{A}}> r).
Proof. run_steps 20. Qed.

Lemma lov_w11_1_start (z : list LD) (r : side) :
  (Lmp (W1 :: z) {{A}}> ([S0; S1; S0; S1; S0; S1] *> r)) -->*
    cfgL (Lmp z) ([S1; S0; S1; S1; S0; S1] *> r).
Proof. run_steps 12. Qed.

Lemma lov_w11_1_end (z' : list LD) (r : side) :
  cfgR (Lmp z') ([S0; S1; S1; S0; S1; S1; S0; S1] *> r) -->*
    (Lmp (W0 :: W0 :: W0 :: z') {{A}}> r).
Proof. run_steps 9. Qed.

Lemma lov_finish_12 (y : list LD) :
  (Lmp (W1 :: y) {{A}}> ([S0; S1] *> 0inf)) -->* cfgL (Lmp y) (RC 0).
Proof. run_steps 12. Qed.

Notation LInc := TM1.LInc.

Notation LInc_c_w0 := TM1.LInc_c_w0.

Notation LInc_c_w10 := TM1.LInc_c_w10.

Notation LInc_c_w11 := TM1.LInc_c_w11.

Notation LInc_append := TM1.LInc_append.

Notation LInc_pow_11_10 := TM1.LInc_pow_11_10.

Notation pow_W1_odd := TM1.pow_W1_odd.

Lemma LInc_step {x x' : list LD} (h : LInc x x') : forall (r : side),
  cfgL (Lmp x) ([S1] *> r) -->* cfgR (Lmp x') ([S0; S1; S1] *> r).
Proof.
  induction h as [xs xs' _ IH | xs | xs xs' _ IH]; intro r.
  - eapply evstep_trans; [apply LInc_w0_1 |].
    change ([S1; S0; S1; S1] *> r) with ([S1] *> ([S0; S1; S1] *> r)).
    eapply evstep_trans; [apply IH |].
    apply RInc_w0.
  - apply LInc_w10.
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply IH |].
    change ([S0; S1; S1] *> ([S0; S1; S0; S1; S0; S1] *> r))
      with ([S0; S1; S1; S0; S1; S0; S1; S0; S1] *> r).
    apply RInc_w11.
Qed.

Lemma RC_return (m : nat) : forall (x : list LD),
  cfgR (Lmp x) (([S0; S1; S1] ^^ m) *> ([S0; S1] *> 0inf)) -->* cfgL (Lmp x) (RC m).
Proof.
  induction m as [| m IH]; intro x.
  - cbn [lpow Str_app]. apply RC_turn_25.
  - cbn [lpow]. rewrite Str_app_assoc.
    eapply evstep_trans; [apply RInc_w0 |].
    eapply evstep_trans; [apply IH |].
    unfold RC.
    eapply evstep_trans; [apply LInc_w0_1 |].
    change ([S1; S0; S1; S1] *> (([S0; S1; S1] ^^ m) *> ([S0; S1] *> 0inf)))
      with ([S1] *> ([S0; S1; S1] *> (([S0; S1; S1] ^^ m) *> ([S0; S1] *> 0inf)))).
    rewrite <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma LInc_RC {x x' : list LD} (h : LInc x x') (m : nat) :
  cfgL (Lmp x) (RC m) -->* cfgL (Lmp x') (RC (m + 1)).
Proof.
  unfold RC at 1.
  eapply evstep_trans; [apply (LInc_step h) |].
  replace (m + 1) with (S m) by lia.
  exact (RC_return (S m) x').
Qed.

Notation LIncs := TM1.LIncs.

Notation LIncs_zero := TM1.LIncs_zero.

Notation LIncs_succ := TM1.LIncs_succ.

Lemma LIncs_RC {n : nat} {x x' : list LD} (h : LIncs n x x') : forall (m : nat),
  cfgL (Lmp x) (RC m) -->* cfgL (Lmp x') (RC (m + n)).
Proof.
  induction h as [x | n x y z h1 _ IH]; intro m.
  - replace (m + 0) with m by lia. apply evstep_refl.
  - replace (m + S n) with ((m + 1) + n) by lia.
    eapply evstep_trans; [apply (LInc_RC h1 m) | apply (IH (m + 1))].
Qed.

Notation LIncs_w0 := TM1.LIncs_w0.

Notation LIncs_w11 := TM1.LIncs_w11.

Notation LIncs_w10 := TM1.LIncs_w10.

Notation LIncsP := TM1.LIncsP.

Notation LIncsP_nil := TM1.LIncsP_nil.

Notation LIncsP_w0 := TM1.LIncsP_w0.

Notation LIncsP_w10 := TM1.LIncsP_w10.

Notation LIncsP_w11 := TM1.LIncsP_w11.

Notation LIncsP_to_LIncs := TM1.LIncsP_to_LIncs.

Notation LIncsP_append := TM1.LIncsP_append.

Notation LIncsP_pow_10 := TM1.LIncsP_pow_10.

Notation LIncsP_pow10_bound := TM1.LIncsP_pow10_bound.

Notation LOv2 := TM1.LOv2.

Notation LOv2_nil := TM1.LOv2_nil.

Notation LOv2_w0 := TM1.LOv2_w0.

Notation LOv2_w11_0 := TM1.LOv2_w11_0.

Notation LOv2_w11_1 := TM1.LOv2_w11_1.

Notation LOv2_append := TM1.LOv2_append.

Notation LOv2_suffix := TM1.LOv2_suffix.

Notation LOv2_pow_11 := TM1.LOv2_pow_11.

Lemma LOv2_correct_aux {w u y : list LD} (h : LOv2 w u y) (hu : u = [W0; W0]) :
  forall (r : side),
    cfgL (Lmp w) ([S1] *> r) -->* (Lmp y {{A}}> r).
Proof.
  revert hu.
  induction h as [u | xs u u' _ IH | xs u x _ IH | xs u z z' _ IH hz]; intros hu r.
  - subst u. apply lov_nil_41.
  - eapply evstep_trans; [apply LInc_w0_1 |].
    change ([S1; S0; S1; S1] *> r) with ([S1] *> ([S0; S1; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) | apply lov_w0_3].
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) | apply lov_w11_0_20].
  - eapply evstep_trans; [apply LInc_w11_1 |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S0; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (IH hu) |].
    eapply evstep_trans; [apply lov_w11_1_start |].
    change ([S1; S0; S1; S1; S0; S1] *> r)
      with ([S1] *> ([S0; S1; S1; S0; S1] *> r)).
    eapply evstep_trans; [apply (LInc_step hz) |].
    change ([S0; S1; S1] *> ([S0; S1; S1; S0; S1] *> r))
      with ([S0; S1; S1; S0; S1; S1; S0; S1] *> r).
    apply lov_w11_1_end.
Qed.

Lemma LOv2_correct {w y : list LD} (h : LOv2 w [W0; W0] y) (r : side) :
  cfgL (Lmp w) ([S1] *> r) -->* (Lmp y {{A}}> r).
Proof. apply (LOv2_correct_aux h eq_refl). Qed.

Notation lpow_succ_r := TM1.lpow_succ_r.

Lemma lov_w0_iter (m : nat) : forall (y : list LD) (r : side),
  (Lmp y {{A}}> (([S0; S1; S1] ^^ m) *> r)) -->*
    (Lmp (([W1] ^^ m) ++ y) {{A}}> r).
Proof.
  induction m as [| m IH]; intros y r.
  - cbn [lpow Str_app app]. apply evstep_refl.
  - rewrite lpow_succ_r, Str_app_assoc.
    eapply evstep_trans; [apply IH |].
    cbn [lpow app].
    apply lov_w0_3.
Qed.

Lemma full_overflow_step {w y : list LD} (m : nat) (h : LOv2 w [W0; W0] y) :
  cfgL (Lmp w) (RC (m + 1)) -->* cfgL (Lmp (([W1] ^^ m) ++ y)) (RC 0).
Proof.
  unfold RC at 1.
  eapply evstep_trans; [apply (LOv2_correct h) |].
  replace (m + 1) with (S m) by lia.
  eapply evstep_trans; [apply (lov_w0_iter (S m)) |].
  cbn [lpow app].
  apply lov_finish_12.
Qed.

Lemma round_step {X X' Y Z : list LD} (m : nat)
    (h1 : LIncsP (2 * m + 1) X X')
    (h2 : LOv2 X' [W0; W0] Y)
    (h3 : LInc (([W1] ^^ (2 * m + 1)) ++ Y) Z) :
  cfgL (Lmp X) (RC 1) -->* cfgL (Lmp Z) (RC 1).
Proof.
  pose proof (LIncs_RC (LIncsP_to_LIncs h1) 1) as H_incs.
  replace (1 + (2 * m + 1)) with ((2 * m + 1) + 1) in H_incs by lia.
  eapply evstep_trans; [exact H_incs |].
  eapply evstep_trans; [apply (full_overflow_step (2 * m + 1) h2) |].
  apply (LInc_RC h3 0).
Qed.

Notation list_LD_ind2 := TM1.list_LD_ind2.

Notation lincFinite := TM1.lincFinite.

Notation lincFinite_sound := TM1.lincFinite_sound.

Notation lincspFinite := TM1.lincspFinite.

Notation lincspCount := TM1.lincspCount.

Notation lincspFinite_sound := TM1.lincspFinite_sound.

Notation lov2Finite := TM1.lov2Finite.

Notation lov2Finite_sound := TM1.lov2Finite_sound.

Notation opt_get_nil := TM1.opt_get_nil.

Definition x0 : list LD := [W1; W0; W0; W0; W1; W1; W1; W0].

Definition x1 : list LD :=
  [W1; W0; W1; W0; W1; W1; W0; W0; W1; W1; W0; W1; W0; W1; W0].

Definition ux2 : list LD :=
  [W1; W1; W0; W1; W0; W1; W0; W0; W1; W1; W0; W0; W0; W0; W1; W1; W1; W0].

Definition x2 : list LD := ([W1; W0] ^^ 25) ++ ux2.

Definition u0_tail : list LD :=
  [W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1;
   W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1;
   W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W1; W0; W0; W0; W0;
   W1; W1; W0; W0; W0; W0; W1; W1; W1; W1; W0; W1; W0; W1; W0].

Definition u0 : list LD := W1 :: W1 :: u0_tail.

Definition c_init_30 : CCfg := mkCCfg A S0 [] ([S0] ^^ 30).

Definition c_x0 : CCfg :=
  mkCCfg D S1
    [S1; S1; S1; S0; S0; S1; S0; S0; S1; S0; S0; S1; S1; S1; S1; S1; S1; S1; S1; S1; S1; S0; S0; S1; S1; S1; S1; S1; S1]
    [S0; S1; S0; S1; S0; S1; S1; S0; S1].

Lemma init_to_x0 : c0 -->* cfgL (Lmp x0) (RC 1).
Proof.
  assert (Heq1 : c0 = evalCCfg 0inf c_init_30).
  { unfold c0, evalCCfg, c_init_30. cbn [cc_q cc_cur cc_l cc_r Str_app].
    rewrite zeros_app_0inf. reflexivity. }
  assert (Heq2 : evalCCfg 0inf c_x0 = cfgL (Lmp x0) (RC 1)) by reflexivity.
  assert (Hsteps : cmultiStep 847 c_init_30 = Some c_x0) by (vm_compute; reflexivity).
  rewrite Heq1, <- Heq2.
  exact (cmultiStep_sound 847 c_init_30 c_x0 0inf Hsteps).
Qed.

Lemma x0_to_x1 : cfgL (Lmp x0) (RC 1) -->* cfgL (Lmp x1) (RC 1).
Proof.
  set (x0' := [W1; W1; W0; W0; W1; W1; W1; W1]).
  set (y0 := [W0; W0; W0; W1; W1; W0; W1; W0; W1; W0]).
  assert (H1 : LIncsP (2 * 2 + 1) x0 x0')
    by (apply (lincspFinite_sound x0 x0'); vm_compute; reflexivity).
  assert (H2 : LOv2 x0' [W0; W0] y0)
    by (apply (lov2Finite_sound x0' [W0; W0] y0); vm_compute; reflexivity).
  assert (H3 : LInc (([W1] ^^ (2 * 2 + 1)) ++ y0) x1)
    by (apply lincFinite_sound; vm_compute; reflexivity).
  exact (round_step 2 H1 H2 H3).
Qed.

Definition x1' : list LD := Eval vm_compute in opt_get_nil (lincspFinite x1).

Definition y1 : list LD := Eval vm_compute in opt_get_nil (lov2Finite x1' [W0; W0]).

Lemma x1_to_x2 : cfgL (Lmp x1) (RC 1) -->* cfgL (Lmp x2) (RC 1).
Proof.
  assert (H1 : LIncsP (2 * 25 + 1) x1 x1')
    by (apply (lincspFinite_sound x1 x1'); vm_compute; reflexivity).
  assert (H2 : LOv2 x1' [W0; W0] y1)
    by (apply (lov2Finite_sound x1' [W0; W0] y1); vm_compute; reflexivity).
  assert (H3 : LInc (([W1] ^^ (2 * 25 + 1)) ++ y1) x2)
    by (apply lincFinite_sound; vm_compute; reflexivity).
  exact (round_step 25 H1 H2 H3).
Qed.

Definition ux2' : list LD := Eval vm_compute in opt_get_nil (lincspFinite ux2).

Lemma x2_to_x3 :
  exists m3, 511 <= m3 /\
    cfgL (Lmp x2) (RC 1) -->* cfgL (Lmp (([W1; W0] ^^ m3) ++ u0)) (RC 1).
Proof.
  assert (H_ux2 : LIncsP (lincspCount ux2) ux2 ux2')
    by (apply (lincspFinite_sound ux2 ux2'); vm_compute; reflexivity).
  destruct (LIncsP_pow_10 15 H_ux2) as [n_suf H_suf].
  pose proof (LIncsP_pow10_bound H_suf) as H_10.
  assert (Hx2_eq : (([W1; W0] ^^ 10) ++ (([W1; W0] ^^ 15) ++ ux2)) = x2).
  { rewrite app_assoc, <- lpow_add. reflexivity. }
  set (x2' := ([W1; W1] ^^ 10) ++ (([W1; W1] ^^ 15) ++ ux2')).
  rewrite Hx2_eq in H_10.
  assert (H_ov : LOv2 x2' [W0; W0] (W0 :: u0_tail))
    by (apply (lov2Finite_sound x2' [W0; W0] (W0 :: u0_tail)); vm_compute; reflexivity).
  set (m3 := 512 * n_suf + 511).
  exists m3. split; [unfold m3; lia |].
  assert (H_inc : LInc (([W1] ^^ (2 * m3 + 1)) ++ (W0 :: u0_tail))
                       (([W1; W0] ^^ m3) ++ u0)).
  { rewrite (pow_W1_odd m3 (W0 :: u0_tail)).
    exact (LInc_pow_11_10 m3 u0_tail). }
  exact (round_step m3 H_10 H_ov H_inc).
Qed.

Notation stepBuffer := TM1.stepBuffer.

Notation checkBuffer := TM1.checkBuffer.

Notation IsBuffer := TM1.IsBuffer.

Notation checkBuffer_mono := TM1.checkBuffer_mono.

Notation isBuffer_le := TM1.isBuffer_le.

Lemma isBuffer_191_B1 : IsBuffer 191 [W1; W1; W0].
Proof. vm_compute. reflexivity. Qed.

Notation stepBuffer_spec := TM1.stepBuffer_spec.

Notation macroStepFinite := TM1.macroStepFinite.

Notation macroStepFinite_spec := TM1.macroStepFinite_spec.

Notation ChainTail := TM1.ChainTail.

Notation CT_nil := TM1.CT_nil.

Notation CT_pair := TM1.CT_pair.

Notation CT_buf := TM1.CT_buf.

Notation ChainTail_pow_pair := TM1.ChainTail_pow_pair.

Notation ChainTail_step := TM1.ChainTail_step.

Lemma chain_round_step {r : nat} (hr : r <= 191) {T : list LD} (hT : ChainTail (S r) T)
    {u u' : list LD} (hu : macroStepFinite u = Some u') :
  exists T', ChainTail r T' /\
    cfgL (Lmp (([W1; W0] ^^ 10) ++ (T ++ u))) (RC 1) -->*
    cfgL (Lmp (([W1; W0] ^^ 10) ++ (T' ++ u'))) (RC 1).
Proof.
  destruct (ChainTail_step hT hu) as [n [W' [T0' [h_lp [h_ov h_ct0]]]]].
  pose proof (LIncsP_pow10_bound h_lp) as h_10.
  pose proof (LOv2_append (LOv2_pow_11 10 (T0' ++ u')) h_ov) as h_ov10.
  set (m := 512 * n + 511).
  set (B1 := [W1; W1; W0]).
  set (tail_rest := ([W1; W0] ^^ 11) ++ (T0' ++ u')).
  assert (h_inc : LInc (([W1] ^^ (2 * m + 1)) ++
                       ([W0; W0; W1; W0] ++ (([W1; W0] ^^ 10) ++ (T0' ++ u'))))
                       (([W1; W0] ^^ m) ++ (B1 ++ tail_rest))).
  { unfold B1, tail_rest.
    rewrite pow_W1_odd.
    exact (LInc_pow_11_10 m ([W0; W1; W0] ++ (([W1; W0] ^^ 10) ++ (T0' ++ u')))). }
  pose proof (round_step m h_10 h_ov10 h_inc) as h_step.
  assert (hm_split : m = 10 + ((m - 10 - 2 * r) + 2 * r)) by (unfold m; lia).
  set (T' := ([W1; W0] ^^ (m - 10 - 2 * r)) ++
             (([W1; W0] ^^ (2 * r)) ++ (B1 ++ (([W1; W0] ^^ 11) ++ T0')))).
  assert (hB1 : IsBuffer r B1) by (exact (isBuffer_le hr isBuffer_191_B1)).
  assert (h_ct_T' : ChainTail r T')
    by (exact (ChainTail_pow_pair (m - 10 - 2 * r)
                (CT_buf r _ _ hB1 (ChainTail_pow_pair 11 h_ct0)))).
  assert (h_eq : (([W1; W0] ^^ m) ++ (B1 ++ tail_rest)) =
                 (([W1; W0] ^^ 10) ++ (T' ++ u'))).
  { rewrite hm_split at 1. rewrite lpow_add, lpow_add.
    unfold T', tail_rest. repeat rewrite <- app_assoc. reflexivity. }
  rewrite h_eq in h_step.
  exists T'. split; [exact h_ct_T' | exact h_step].
Qed.

Notation runU := TM1.runU.

Lemma runU_steps (k : nat) : forall (r : nat), r + k <= 191 ->
  forall {T u u' : list LD},
    ChainTail (r + k) T ->
    runU k u = Some u' ->
    exists T', ChainTail r T' /\
      cfgL (Lmp (([W1; W0] ^^ 10) ++ (T ++ u))) (RC 1) -->*
      cfgL (Lmp (([W1; W0] ^^ 10) ++ (T' ++ u'))) (RC 1).
Proof.
  induction k as [| k IH]; intros r hrk T u u' hT hu; cbn [runU] in hu.
  - inversion hu; subst u'. replace (r + 0) with r in hT by lia.
    exists T. split; [exact hT | apply evstep_refl].
  - destruct (macroStepFinite u) as [u1 |] eqn:Hu1; [| discriminate].
    replace (r + S k) with (S (r + k)) in hT by lia.
    destruct (chain_round_step (ltac:(lia) : r + k <= 191) hT Hu1)
      as [T1 [hT1 h_step1]].
    destruct (IH r ltac:(lia) T1 u1 u' hT1 hu) as [T' [hT' h_step2]].
    exists T'. split; [exact hT' | eapply evstep_trans; [exact h_step1 | exact h_step2]].
Qed.

Notation Only011 := TM1.Only011.

Notation Only011_nil := TM1.Only011_nil.

Notation Only011_w0 := TM1.Only011_w0.

Notation Only011_w11 := TM1.Only011_w11.

Notation Only011_append := TM1.Only011_append.

Notation LIncsP_only011 := TM1.LIncsP_only011.

Notation checkOnly011 := TM1.checkOnly011.

Notation checkOnly011_sound := TM1.checkOnly011_sound.

Lemma Only011_skip {P : list LD} (hP : Only011 P) (s : list LD) :
  forall (r : side),
    exists r', cfgL (Lmp (P ++ s)) ([S1; S0] *> r) -->* cfgL (Lmp s) ([S1; S0] *> r').
Proof.
  induction hP as [| xs _ IH | xs _ IH]; intro r; cbn [app].
  - exists r. apply evstep_refl.
  - destruct (IH ([S1; S1; S0] *> r)) as [r' hr'].
    exists r'.
    change ([S1; S0] *> r) with ([S1] *> ([S0] *> r)).
    eapply evstep_trans; [apply (LInc_w0_1 (xs ++ s) ([S0] *> r)) |].
    change ([S1; S0; S1; S1] *> ([S0] *> r)) with ([S1; S0] *> ([S1; S1; S0] *> r)).
    exact hr'.
  - destruct (IH ([S1; S0; S1; S0; S1; S0] *> r)) as [r' hr'].
    exists r'.
    change ([S1; S0] *> r) with ([S1] *> ([S0] *> r)).
    eapply evstep_trans; [apply (LInc_w11_1 (xs ++ s) ([S0] *> r)) |].
    change ([S1; S0; S1; S0; S1; S0; S1] *> ([S0] *> r))
      with ([S1; S0] *> ([S1; S0; S1; S0; S1; S0] *> r)).
    exact hr'.
Qed.

Notation ChainTail_zero_lincsp := TM1.ChainTail_zero_lincsp.

Definition msb_17 : list LD :=
  [W0; W1; W1; W0; W1; W1; W0; W1; W1; W0; W1; W1; W0; W1; W1; W1; W1].

Definition u191 : list LD := Eval vm_compute in opt_get_nil (runU 191 u0).

Definition u191_pre' : list LD :=
  Eval vm_compute in firstn 436 (opt_get_nil (lincspFinite u191)).

Lemma runU_191_eq : runU 191 u0 = Some u191.
Proof. vm_compute. reflexivity. Qed.

Lemma u191_lincsp_eq : lincspFinite u191 = Some (u191_pre' ++ msb_17).
Proof. vm_compute. reflexivity. Qed.

Lemma u191_pre'_only011 : checkOnly011 u191_pre' = true.
Proof. vm_compute. reflexivity. Qed.

Definition c_msb_start : CCfg :=
  mkCCfg D S1 (List.tl (encList msb_17 ++ [S1; S1; S1; S1; S1; S1])) [S0; S1; S0; S1; S0].

Definition c_msb_halt : CCfg :=
  Eval vm_compute in
    match cmultiStep 1356 c_msb_start with
    | Some c => c
    | None => c_msb_start
    end.

Lemma msb_17_halt (r : side) :
  halts tm (cfgL (Lmp msb_17) ([S1; S0] *> r)).
Proof.
  assert (Hstart : cfgL (Lmp msb_17) ([S1; S0] *> r) = evalCCfg r c_msb_start)
    by reflexivity.
  assert (H1356 : cmultiStep 1356 c_msb_start = Some c_msb_halt)
    by (vm_compute; reflexivity).
  rewrite Hstart.
  eapply halts_evstep; [| exact (cmultiStep_sound 1356 c_msb_start c_msb_halt r H1356)].
  apply halted_halts. reflexivity.
Qed.

Lemma step_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Theorem halt: halts tm c0.
Proof.
  pose proof (step_trans init_to_x0 (step_trans x0_to_x1 x1_to_x2)) as H02.
  destruct x2_to_x3 as [m3 [hm3 H23]].
  pose proof (step_trans H02 H23) as H_init_x3.
  assert (Hm3_split : m3 = 10 + ((m3 - 392) + 2 * 191)) by lia.
  set (T0 := ([W1; W0] ^^ (m3 - 392)) ++ ([W1; W0] ^^ (2 * 191))).
  assert (H_T0 : ChainTail (0 + 191) T0)
    by (exact (ChainTail_pow_pair (m3 - 392) (CT_nil 191))).
  assert (H_x3_eq : (([W1; W0] ^^ m3) ++ u0) =
                    (([W1; W0] ^^ 10) ++ (T0 ++ u0))).
  { rewrite Hm3_split at 1. rewrite lpow_add, lpow_add.
    unfold T0. repeat rewrite <- app_assoc. reflexivity. }
  rewrite H_x3_eq in H_init_x3.
  destruct (runU_steps 191 0 ltac:(lia) H_T0 runU_191_eq)
    as [T191 [H_T191 H_rounds]].
  pose proof (step_trans H_init_x3 H_rounds) as H_to_191.
  destruct (ChainTail_zero_lincsp H_T191) as [nT [T191' H_lpT]].
  pose proof (lincspFinite_sound u191 _ u191_lincsp_eq) as H_lpU.
  destruct (LIncsP_append H_lpT H_lpU) as [nTU H_lpTU].
  destruct (LIncsP_pow_10 10 H_lpTU) as [nAll H_lpAll].
  pose proof (LIncs_RC (LIncsP_to_LIncs H_lpAll) 1) as H_incs_final.
  pose proof (step_trans H_to_191 H_incs_final) as H_to_inc.
  assert (H_10T_only : Only011 (([W1; W1] ^^ 10) ++ T191')).
  { destruct (LIncsP_pow_10 10 H_lpT) as [n10T H10T].
    exact (LIncsP_only011 H10T). }
  set (P_all := (([W1; W1] ^^ 10) ++ T191') ++ u191_pre').
  assert (H_P_only : Only011 P_all)
    by (exact (Only011_append H_10T_only (checkOnly011_sound u191_pre' u191_pre'_only011))).
  assert (H_assoc : (([W1; W1] ^^ 10) ++ (T191' ++ (u191_pre' ++ msb_17))) =
                    P_all ++ msb_17).
  { unfold P_all. repeat rewrite <- app_assoc. reflexivity. }
  assert (H_rc_eq : RC (1 + nAll) =
    [S1; S0] *> ([S1; S1] *> (([S0; S1; S1] ^^ nAll) *> ([S0; S1] *> 0inf))))
    by reflexivity.
  rewrite H_assoc, H_rc_eq in H_to_inc.
  destruct (Only011_skip H_P_only msb_17
              ([S1; S1] *> (([S0; S1; S1] ^^ nAll) *> ([S0; S1] *> 0inf))))
    as [r' H_skip].
  pose proof (step_trans H_to_inc H_skip) as H_to_msb.
  eapply halts_evstep; [apply msb_17_halt | exact H_to_msb].
Qed.

End TM2.
Print Assumptions TM2.halt.
