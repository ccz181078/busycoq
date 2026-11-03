(* 1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF never halts. *)

From Coq Require Import Lia ZifyNat ZifyBool PeanoNat Bool String Lists.Streams List Arith.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := Eval compute in
  (TM_from_str "1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ep_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Ltac split_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      let E := fresh "Eif" in destruct b eqn:E
  | H : context [if ?b then _ else _] |- _ =>
      let E := fresh "Eif" in destruct b eqn:E
  end.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac fast_start_progress :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

(* ========================================================================== *)
(* Preliminaries: Option Iteration & List Repeat Helpers                      *)
(* ========================================================================== *)

Fixpoint iterOpt {X : Type} (f : X -> option X) (n : nat) (x : X) : option X :=
  match n with
  | 0 => Some x
  | S n' =>
    match f x with
    | Some y => iterOpt f n' y
    | None => None
    end
  end.

Lemma iterOpt_add {X : Type} (f : X -> option X) (m n : nat) (x : X) :
  iterOpt f (m + n) x =
  match iterOpt f m x with
  | Some y => iterOpt f n y
  | None => None
  end.
Proof.
  revert x.
  induction m as [| m ih]; intros x; [reflexivity |].
  cbn [Nat.add iterOpt].
  destruct (f x) as [y |]; [exact (ih y) | reflexivity].
Qed.

Lemma iterOpt_trans {X : Type} {f : X -> option X} {m n : nat} {x y z : X}
    (h1 : iterOpt f m x = Some y) (h2 : iterOpt f n y = Some z) :
  iterOpt f (m + n) x = Some z.
Proof.
  rewrite iterOpt_add, h1. exact h2.
Qed.

Lemma repeat_succ {X : Type} (k : nat) (x : X) :
  repeat x (k + 1) = x :: repeat x k.
Proof.
  rewrite Nat.add_1_r. reflexivity.
Qed.

Lemma repeat_add {X : Type} (m n : nat) (x : X) :
  repeat x (m + n) = repeat x m ++ repeat x n.
Proof.
  apply repeat_app.
Qed.

Lemma repeat_append_cons_same {X : Type} (k : nat) (x : X) (L : list X) :
  repeat x k ++ (x :: L) = repeat x (k + 1) ++ L.
Proof.
  induction k as [| k ih]; [reflexivity |].
  cbn [repeat app]. rewrite ih. reflexivity.
Qed.

Lemma repeat_succ_append {X : Type} (k : nat) (x : X) (R : list X) :
  repeat x (k + 1) ++ R = repeat x k ++ (x :: R).
Proof.
  symmetry. apply repeat_append_cons_same.
Qed.

Lemma repeat_two_mul_append_two {X : Type} (k : nat) (x : X) (R : list X) :
  repeat x (2 * (k + 1)) ++ R = repeat x (2 * k) ++ (x :: x :: R).
Proof.
  replace (2 * (k + 1)) with (2 * k + 2) by lia.
  rewrite repeat_add, <- app_assoc. reflexivity.
Qed.

Lemma cons_repeat_append {X : Type} (k : nat) (x : X) (R : list X) :
  x :: (repeat x k ++ R) = repeat x (k + 1) ++ R.
Proof.
  rewrite repeat_succ. reflexivity.
Qed.

Lemma cons_repeat_odd_append {X : Type} (j : nat) (x : X) (R : list X) :
  x :: (repeat x (2 * j + 1) ++ R) = repeat x (2 * (j + 1)) ++ R.
Proof.
  replace (2 * (j + 1)) with ((2 * j + 1) + 1) by lia.
  apply cons_repeat_append.
Qed.

(* ========================================================================== *)
(* Section 1: Stage 1 (decode_blk and 22-Clause Transducer step_blk)          *)
(* ========================================================================== *)

Inductive LToken : Type :=
  | L1
  | L10
  | L00.

Fixpoint toLC (l : list LToken) : side :=
  match l with
  | [] => 0inf%sym
  | L1 :: l' => 1%sym >> toLC l'
  | L10 :: l' => 0%sym >> 1%sym >> toLC l'
  | L00 :: l' => 0%sym >> 0%sym >> toLC l'
  end.

Fixpoint encode_run (a : nat) (r : side) : side :=
  match a with
  | 0 => 1%sym >> r
  | S a' => 0%sym >> encode_run a' r
  end.

Fixpoint toRBlank (B : list nat) : side :=
  match B with
  | [] => 0inf%sym
  | a :: B' => encode_run a (toRBlank B')
  end.

Inductive Mode6 : Type :=
  | M6_h11D
  | M6_h10B
  | M6_h100F
  | M6_h10F
  | M6_h1E
  | M6_hL.

Definition BlkCfg : Type := Mode6 * list LToken * list nat.

Definition decode_blk (c : BlkCfg) : Q * tape :=
  let '(m, l, bs) := c in
  match m with
  | M6_h11D  => (toRBlank bs) <{{A}} ([1; 1]%sym *> toLC l)
  | M6_h10B  => (toRBlank bs) <{{C}} ([0; 1]%sym *> toLC l)
  | M6_h100F => (toRBlank bs) <{{D}} ([0; 0; 1]%sym *> toLC l)
  | M6_h10F  => (toRBlank bs) <{{D}} ([0; 1]%sym *> toLC l)
  | M6_h1E   => (toRBlank bs) <{{F}} ([1]%sym *> toLC l)
  | M6_hL    => ([0; 0]%sym *> toRBlank bs) {{B}}> (toLC l)
  end.

Lemma init_reaches_blk0 :
  c0 -->* decode_blk (M6_h11D, [L10; L1], []).
Proof.
  unfold c0, tape0, decode_blk.
  cbn [toRBlank toLC Str_app].
  repeat (try solve [fast_finish]; fast_step).
Qed.

Definition step_blk (c : BlkCfg) : option BlkCfg :=
  let '(m, l, bs) := c in
  match m with
  | M6_h11D =>
    match bs with
    | [] => Some (M6_hL, l, [0])
    | 0 :: bs' => Some (M6_h10B, L1 :: l, bs')
    | S a :: bs' => Some (M6_hL, l, 0 :: a :: bs')
    end
  | M6_h10B =>
    match bs with
    | [] => Some (M6_h11D, L10 :: L1 :: L1 :: l, [])
    | 0 :: bs' => Some (M6_h100F, l, bs')
    | 1 :: bs' => Some (M6_h1E, L00 :: L1 :: l, bs')
    | 2 :: bs' => Some (M6_h10F, L10 :: L1 :: l, bs')
    | 3 :: bs' => Some (M6_h1E, L10 :: L10 :: L1 :: l, bs')
    | S (S (S (S a))) :: bs' => Some (M6_h11D, L10 :: L1 :: L1 :: l, a :: bs')
    end
  | M6_h100F =>
    match bs with
    | [] => Some (M6_h11D, L10 :: L10 :: l, [])
    | 0 :: _ => None
    | 1 :: bs' => Some (M6_h10F, L00 :: L1 :: l, bs')
    | 2 :: bs' => Some (M6_h1E, L10 :: L00 :: L1 :: l, bs')
    | S (S (S a)) :: bs' => Some (M6_h11D, L10 :: L10 :: l, a :: bs')
    end
  | M6_h10F =>
    match bs with
    | [] => Some (M6_h11D, L10 :: L1 :: l, [])
    | 0 :: _ => None
    | 1 :: bs' => Some (M6_h10F, L10 :: l, bs')
    | 2 :: bs' => Some (M6_h1E, L10 :: L10 :: l, bs')
    | S (S (S a)) :: bs' => Some (M6_h11D, L10 :: L1 :: l, a :: bs')
    end
  | M6_h1E =>
    match bs with
    | [] => Some (M6_h11D, l, [])
    | 0 :: bs' => Some (M6_h1E, L1 :: l, bs')
    | S a :: bs' => Some (M6_h11D, l, a :: bs')
    end
  | M6_hL =>
    match bs with
    | [] => None
    | a :: bs' =>
      match l with
      | [] => Some (M6_h11D, [L10], a :: bs')
      | L00 :: l' => Some (M6_h11D, L10 :: l', a :: bs')
      | L10 :: l' => Some (M6_hL, l', 0 :: S a :: bs')
      | L1 :: l' => Some (M6_hL, l', S a :: bs')
      end
    end
  end.

Theorem step_blk_correct (c c' : BlkCfg) (h : step_blk c = Some c') :
  decode_blk c -->+ decode_blk c'.
Proof.
  destruct c as [[m l] bs].
  destruct m.
  - (* M6_h11D *)
    destruct bs as [| [| a] bs']; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
  - (* M6_h10B *)
    destruct bs as [| [| [| [| [| a]]]] bs']; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
  - (* M6_h100F *)
    destruct bs as [| [| [| [| a]]] bs']; try discriminate h; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
  - (* M6_h10F *)
    destruct bs as [| [| [| [| a]]] bs']; try discriminate h; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
  - (* M6_h1E *)
    destruct bs as [| [| a] bs']; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
  - (* M6_hL *)
    destruct bs as [| a bs']; [discriminate h |].
    destruct l as [| [| | ] l']; inversion h; subst c'; clear h;
      unfold decode_blk; cbn [toRBlank encode_run toLC Str_app Streams.hd Streams.tl];
      fast_start_progress.
Qed.

(* ========================================================================== *)
(* Section 2: Stage 2 (SBlock, Phi, step_5mode) & Stage 3 (Spine, step_sq)    *)
(* ========================================================================== *)

Inductive SBlock : Type :=
  | SA (k : nat)
  | SB (k : nat).

Fixpoint evalSB (ls : list SBlock) : list LToken :=
  match ls with
  | [] => []
  | SA k :: lsp => repeat L1 k ++ (L10 :: evalSB lsp)
  | SB k :: lsp => repeat L1 k ++ (L00 :: evalSB lsp)
  end.

Definition incTop (ls : list SBlock) (d : nat) : list SBlock :=
  match ls with
  | [] => [SA d]
  | SA k :: lsp => SA (k + d) :: lsp
  | SB k :: lsp => SB (k + d) :: lsp
  end.

Lemma evalSB_incTop {ls : list SBlock} (hls : ls <> []) (d : nat) :
  evalSB (incTop ls d) = repeat L1 d ++ evalSB ls.
Proof.
  destruct ls as [| [k | k] lsp]; [contradiction | |];
    cbn [incTop evalSB];
    replace (k + d) with (d + k) by lia;
    rewrite repeat_add, <- app_assoc; reflexivity.
Qed.

Inductive Mode5 : Type :=
  | hL
  | h10B
  | h1E
  | h100F
  | h10F.

Definition Cfg5 : Type := Mode5 * list SBlock * list nat.

Definition Guard5 (c : Cfg5) : Prop :=
  let '(m, ls, _) := c in m <> hL -> ls <> [].

Definition Phi (c : Cfg5) : BlkCfg :=
  let '(m, ls, rs) := c in
  match m with
  | hL    => (M6_hL, evalSB ls, 0 :: rs)
  | h10B  => (M6_h10B, evalSB ls, rs)
  | h1E   => (M6_h1E, evalSB ls, rs)
  | h100F => (M6_h100F, evalSB ls, rs)
  | h10F  => (M6_h10F, evalSB ls, rs)
  end.

Lemma pop_L1_run (r a : nat) (l' : list LToken) (rs : list nat) :
  iterOpt step_blk r (M6_hL, repeat L1 r ++ l', a :: rs) =
    Some (M6_hL, l', (a + r) :: rs).
Proof.
  revert a.
  induction r as [| r ih]; intros a.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [repeat app iterOpt step_blk].
    rewrite (ih (S a)).
    replace (S a + r) with (a + S r) by lia.
    reflexivity.
Qed.

Lemma pop_L1_run_zero (r : nat) (l' : list LToken) (rs : list nat) :
  iterOpt step_blk r (M6_hL, repeat L1 r ++ l', 0 :: rs) =
    Some (M6_hL, l', r :: rs).
Proof.
  exact (pop_L1_run r 0 l' rs).
Qed.

Definition step_5mode (c : Cfg5) : option Cfg5 :=
  let '(m, ls, rs) := c in
  match m with
  | hL =>
    match ls with
    | [] => Some (h10B, [SA 1], rs)
    | SA k :: lsp => Some (hL, lsp, S k :: rs)
    | SB 0 :: lsp => Some (h10B, SA 1 :: lsp, rs)
    | SB (S k) :: lsp => Some (hL, lsp, 1 :: k :: rs)
    end
  | h10B =>
    match rs with
    | [] => Some (hL, SA 0 :: incTop ls 2, [])
    | 0 :: rsp => Some (h100F, ls, rsp)
    | 1 :: rsp => Some (h1E, SB 0 :: incTop ls 1, rsp)
    | 2 :: rsp => Some (h10F, SA 0 :: incTop ls 1, rsp)
    | 3 :: rsp => Some (h1E, SA 0 :: SA 0 :: incTop ls 1, rsp)
    | 4 :: rsp => Some (h10B, SA 1 :: incTop ls 2, rsp)
    | S (S (S (S (S a)))) :: rsp => Some (hL, SA 0 :: incTop ls 2, a :: rsp)
    end
  | h100F =>
    match rs with
    | [] => Some (hL, SA 0 :: SA 0 :: ls, [])
    | 0 :: _ => None
    | 1 :: rsp => Some (h10F, SB 0 :: incTop ls 1, rsp)
    | 2 :: rsp => Some (h1E, SA 0 :: SB 0 :: incTop ls 1, rsp)
    | 3 :: rsp => Some (h10B, SA 1 :: SA 0 :: ls, rsp)
    | S (S (S (S a))) :: rsp => Some (hL, SA 0 :: SA 0 :: ls, a :: rsp)
    end
  | h10F =>
    match rs with
    | [] => Some (hL, SA 0 :: incTop ls 1, [])
    | 0 :: _ => None
    | 1 :: rsp => Some (h10F, SA 0 :: ls, rsp)
    | 2 :: rsp => Some (h1E, SA 0 :: SA 0 :: ls, rsp)
    | 3 :: rsp => Some (h10B, SA 1 :: incTop ls 1, rsp)
    | S (S (S (S a))) :: rsp => Some (hL, SA 0 :: incTop ls 1, a :: rsp)
    end
  | h1E =>
    match rs with
    | [] => Some (hL, ls, [])
    | 0 :: rsp => Some (h1E, incTop ls 1, rsp)
    | 1 :: rsp => Some (h10B, incTop ls 1, rsp)
    | S (S a) :: rsp => Some (hL, ls, a :: rsp)
    end
  end.

Theorem step_5mode_correct (c c' : Cfg5)
    (hguard : Guard5 c) (h : step_5mode c = Some c') :
  exists j, j > 0 /\ iterOpt step_blk j (Phi c) = Some (Phi c').
Proof.
  destruct c as [[m ls] rs].
  destruct m.
  - (* hL *)
    destruct ls as [| [k | [| k]] lsp]; inversion h; subst c'; clear h.
    + exists 2. split; [lia | reflexivity].
    + exists (k + 1). split; [lia |].
      cbn [Phi evalSB].
      eapply iterOpt_trans; [exact (pop_L1_run_zero k (L10 :: evalSB lsp) rs) | reflexivity].
    + exists 2. split; [lia | reflexivity].
    + exists (S k + 3). split; [lia |].
      cbn [Phi]. change (evalSB (SB (S k) :: lsp)) with (repeat L1 (S k) ++ (L00 :: evalSB lsp)).
      eapply iterOpt_trans; [exact (pop_L1_run_zero (S k) (L00 :: evalSB lsp) rs) | reflexivity].
  - (* h10B *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| [| a]]]]] rsp]; inversion h; subst c'; clear h;
      [ exists 2 | exists 1 | exists 1 | exists 1 | exists 1 | exists 2 | exists 2 ];
      (split; [lia | cbn [Phi evalSB repeat app]; try rewrite (evalSB_incTop hls); reflexivity]).
  - (* h1E *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| a]] rsp]; inversion h; subst c'; clear h;
      [ exists 2 | exists 1 | exists 2 | exists 2 ];
      (split; [lia | cbn [Phi evalSB repeat app]; try rewrite (evalSB_incTop hls); reflexivity]).
  - (* h100F *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h; inversion h; subst c'; clear h;
      [ exists 2 | exists 1 | exists 1 | exists 2 | exists 2 ];
      (split; [lia | cbn [Phi evalSB repeat app]; try rewrite (evalSB_incTop hls); reflexivity]).
  - (* h10F *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h; inversion h; subst c'; clear h;
      [ exists 2 | exists 1 | exists 1 | exists 2 | exists 2 ];
      (split; [lia | cbn [Phi evalSB repeat app]; try rewrite (evalSB_incTop hls); reflexivity]).
Qed.

Definition W_5 : list SBlock := [SA 3; SA 0; SA 2; SA 0; SA 2].

Fixpoint Spine (n : nat) : list SBlock :=
  match n with
  | 0 => W_5
  | S n' => SA 0 :: SA 2 :: Spine n'
  end.

Lemma spine_nonempty (n : nat) : Spine n <> [].
Proof.
  destruct n; discriminate.
Qed.

Fixpoint repA0A2 (n : nat) : list SBlock :=
  match n with
  | 0 => []
  | S n' => SA 0 :: SA 2 :: repA0A2 n'
  end.

Fixpoint rep31 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => rep31 n' ++ [3; 1]
  end.

Lemma spine_eq_repA0A2 (n : nat) :
  Spine n = repA0A2 n ++ W_5.
Proof.
  induction n as [| n ih]; [reflexivity |].
  cbn [Spine repA0A2 app]. rewrite ih. reflexivity.
Qed.

Lemma spine_left_drain (n : nat) (L0 : list SBlock) (R : list nat) :
  iterOpt step_5mode (2 * n) (hL, repA0A2 n ++ L0, R) =
    Some (hL, L0, rep31 n ++ R).
Proof.
  revert R.
  induction n as [| n ih]; intros R; [reflexivity |].
  replace (2 * S n) with (2 + 2 * n) by lia.
  cbn [repA0A2 app].
  assert (h2 : iterOpt step_5mode 2 (hL, SA 0 :: SA 2 :: (repA0A2 n ++ L0), R) =
               Some (hL, repA0A2 n ++ L0, 3 :: 1 :: R)) by reflexivity.
  eapply iterOpt_trans; [exact h2 |].
  rewrite (ih (3 :: 1 :: R)).
  cbn [rep31]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma w5_bottom_bounce (R' : list nat) :
  iterOpt step_5mode 11 (hL, W_5, R') = Some (h10B, SA 1 :: W_5, R').
Proof.
  reflexivity.
Qed.

Lemma spine_right_climb (n : nat) (L0 : list SBlock) (R : list nat) :
  iterOpt step_5mode (2 * n) (h10B, SA 1 :: L0, rep31 n ++ R) =
    Some (h10B, SA 1 :: (repA0A2 n ++ L0), R).
Proof.
  revert L0 R.
  induction n as [| n ih]; intros L0 R; [reflexivity |].
  replace (2 * S n) with (2 * n + 2) by lia.
  cbn [rep31]. rewrite <- app_assoc.
  eapply iterOpt_trans; [exact (ih L0 (3 :: 1 :: R)) |].
  reflexivity.
Qed.

Theorem spine_bounce_stationary (n : nat) (R : list nat) :
  iterOpt step_5mode (4 * n + 11) (hL, Spine n, R) =
    Some (h10B, SA 1 :: Spine n, R).
Proof.
  rewrite spine_eq_repA0A2.
  pose proof (spine_left_drain n W_5 R) as h1.
  pose proof (w5_bottom_bounce (rep31 n ++ R)) as h2.
  pose proof (spine_right_climb n W_5 R) as h3.
  pose proof (iterOpt_trans (iterOpt_trans h1 h2) h3) as h123.
  replace (2 * n + 11 + 2 * n) with (4 * n + 11) in h123 by lia.
  exact h123.
Qed.

Theorem spine_bounce_absorb (n : nat) (R : list nat) :
  iterOpt step_5mode (4 * n + 15) (hL, [SA 0; SA 2] ++ Spine n, R) =
    Some (h10B, SA 1 :: Spine (S n), R).
Proof.
  pose proof (spine_bounce_stationary (S n) R) as h.
  replace (4 * S n + 11) with (4 * n + 15) in h by lia.
  exact h.
Qed.

Definition CfgSq : Type := Mode5 * list SBlock * list nat.

Definition GuardSq (c : CfgSq) : Prop :=
  let '(m, ls, _) := c in m <> hL -> ls <> [].

Definition Psi_sq (n : nat) (c : CfgSq) : Cfg5 :=
  let '(m, ls, rs) := c in (m, ls ++ Spine n, rs).

Definition step_sq (c : CfgSq) : option CfgSq :=
  let '(m, ls, rs) := c in
  match m with
  | hL =>
    match ls with
    | [] => Some (h10B, [SA 1], rs)
    | [SA 0; SA 2] => Some (h10B, [SA 1], rs)
    | SA k :: lsp => Some (hL, lsp, S k :: rs)
    | SB 0 :: lsp => Some (h10B, SA 1 :: lsp, rs)
    | SB (S k) :: lsp => Some (hL, lsp, 1 :: k :: rs)
    end
  | h10B =>
    match rs with
    | [] => Some (hL, SA 0 :: incTop ls 2, [])
    | 0 :: rsp => Some (h100F, ls, rsp)
    | 1 :: rsp => Some (h1E, SB 0 :: incTop ls 1, rsp)
    | 2 :: rsp => Some (h10F, SA 0 :: incTop ls 1, rsp)
    | 3 :: rsp => Some (h1E, SA 0 :: SA 0 :: incTop ls 1, rsp)
    | 4 :: rsp => Some (h10B, SA 1 :: incTop ls 2, rsp)
    | S (S (S (S (S a)))) :: rsp => Some (hL, SA 0 :: incTop ls 2, a :: rsp)
    end
  | h100F =>
    match rs with
    | [] => Some (hL, SA 0 :: SA 0 :: ls, [])
    | 0 :: _ => None
    | 1 :: rsp => Some (h10F, SB 0 :: incTop ls 1, rsp)
    | 2 :: rsp => Some (h1E, SA 0 :: SB 0 :: incTop ls 1, rsp)
    | 3 :: rsp => Some (h10B, SA 1 :: SA 0 :: ls, rsp)
    | S (S (S (S a))) :: rsp => Some (hL, SA 0 :: SA 0 :: ls, a :: rsp)
    end
  | h10F =>
    match rs with
    | [] => Some (hL, SA 0 :: incTop ls 1, [])
    | 0 :: _ => None
    | 1 :: rsp => Some (h10F, SA 0 :: ls, rsp)
    | 2 :: rsp => Some (h1E, SA 0 :: SA 0 :: ls, rsp)
    | 3 :: rsp => Some (h10B, SA 1 :: incTop ls 1, rsp)
    | S (S (S (S a))) :: rsp => Some (hL, SA 0 :: incTop ls 1, a :: rsp)
    end
  | h1E =>
    match rs with
    | [] => Some (hL, ls, [])
    | 0 :: rsp => Some (h1E, incTop ls 1, rsp)
    | 1 :: rsp => Some (h10B, incTop ls 1, rsp)
    | S (S a) :: rsp => Some (hL, ls, a :: rsp)
    end
  end.

Lemma incTop_nonempty (ls : list SBlock) (d : nat) : incTop ls d <> [].
Proof.
  destruct ls as [| [k | k] lsp]; discriminate.
Qed.

Lemma incTop_append {ls : list SBlock} (hls : ls <> []) (S : list SBlock) (d : nat) :
  incTop (ls ++ S) d = incTop ls d ++ S.
Proof.
  destruct ls as [| [k | k] lsp]; [contradiction | reflexivity | reflexivity].
Qed.

Lemma step_sq_preserves_guard (c c' : CfgSq)
    (hguard : GuardSq c) (h : step_sq c = Some c') :
  GuardSq c'.
Proof.
  destruct c as [[m ls] rs].
  destruct m.
  - (* hL *)
    destruct ls as [| [ [| k] | [| k] ] lsp].
    + inversion h; subst c'; intro; congruence.
    + destruct lsp as [| [ [| [| [| k2]]] | k2 ] [| sb3 lsp3]];
        inversion h; subst c'; intro; congruence.
    + inversion h; subst c'; intro; congruence.
    + inversion h; subst c'; intro; congruence.
    + inversion h; subst c'; intro; congruence.
  - (* h10B *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| [| a]]]]] rsp]; inversion h; subst c'; intro hne;
      (exact hls || apply incTop_nonempty || congruence).
  - (* h1E *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| a]] rsp]; inversion h; subst c'; intro hne;
      (exact hls || apply incTop_nonempty || congruence).
  - (* h100F *)
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h;
      inversion h; subst c'; intro; congruence.
  - (* h10F *)
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h;
      inversion h; subst c'; intro; congruence.
Qed.

Definition decode_sq (n : nat) (c : CfgSq) : Q * tape :=
  decode_blk (Phi (Psi_sq n c)).

Lemma psi_sq_guard (n : nat) (c : CfgSq) : Guard5 (Psi_sq n c).
Proof.
  destruct c as [[m ls] rs].
  cbn [Psi_sq Guard5]. intros _ hemp.
  apply app_eq_nil in hemp. destruct hemp as [_ hsp].
  exact (spine_nonempty n hsp).
Qed.

Theorem step_sq_lift (n : nat) (c c' : CfgSq)
    (hguard : GuardSq c) (h : step_sq c = Some c') :
  exists n' k, k > 0 /\ iterOpt step_5mode k (Psi_sq n c) = Some (Psi_sq n' c').
Proof.
  destruct c as [[m ls] rs].
  destruct m.
  - (* hL *)
    destruct ls as [| [ [| k] | [| k] ] lsp].
    + inversion h; subst c'.
      exists n, (4 * n + 11). split; [lia | exact (spine_bounce_stationary n rs)].
    + destruct lsp as [| [ [| [| [| k2]]] | k2 ] [| sb3 lsp3]];
        inversion h; subst c'.
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists (S n), (4 * n + 15). split; [lia | exact (spine_bounce_absorb n rs)].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
      * exists n, 1. split; [lia | reflexivity].
    + inversion h; subst c'. exists n, 1. split; [lia | reflexivity].
    + inversion h; subst c'. exists n, 1. split; [lia | reflexivity].
    + inversion h; subst c'. exists n, 1. split; [lia | reflexivity].
  - (* h10B *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| [| a]]]]] rsp]; inversion h; subst c';
      exists n, 1; (split; [lia | cbn [Psi_sq iterOpt step_5mode app]; try rewrite (incTop_append hls); reflexivity]).
  - (* h1E *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| a]] rsp]; inversion h; subst c';
      exists n, 1; (split; [lia | cbn [Psi_sq iterOpt step_5mode app]; try rewrite (incTop_append hls); reflexivity]).
  - (* h100F *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h; inversion h; subst c';
      exists n, 1; (split; [lia | cbn [Psi_sq iterOpt step_5mode app]; try rewrite (incTop_append hls); reflexivity]).
  - (* h10F *)
    assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h; inversion h; subst c';
      exists n, 1; (split; [lia | cbn [Psi_sq iterOpt step_5mode app]; try rewrite (incTop_append hls); reflexivity]).
Qed.

Lemma iterOpt_step_blk_plus {j : nat} (hj : j > 0) {b1 b2 : BlkCfg}
    (h : iterOpt step_blk j b1 = Some b2) :
  decode_blk b1 -->+ decode_blk b2.
Proof.
  revert b1 h.
  induction j as [| j ih]; intros b1 h; [lia |].
  cbn [iterOpt] in h.
  destruct (step_blk b1) as [bm |] eqn:hs; [| discriminate h].
  destruct j as [| j'].
  - inversion h; subst bm. exact (step_blk_correct b1 b2 hs).
  - exact (ptrans (step_blk_correct b1 bm hs) (ih ( ltac:(lia) ) bm h)).
Qed.

Lemma step_5mode_preserves_guard (c c' : Cfg5)
    (hguard : Guard5 c) (h : step_5mode c = Some c') :
  Guard5 c'.
Proof.
  destruct c as [[m ls] rs].
  destruct m.
  - destruct ls as [| [k | [| k]] lsp]; inversion h; subst c'; intro; congruence.
  - assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| [| [| [| a]]]]] rsp]; inversion h; subst c'; intro hne;
      (exact hls || apply incTop_nonempty || congruence).
  - assert (hls : ls <> []) by (apply hguard; discriminate).
    destruct rs as [| [| [| a]] rsp]; inversion h; subst c'; intro hne;
      (exact hls || apply incTop_nonempty || congruence).
  - destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h;
      inversion h; subst c'; intro; congruence.
  - destruct rs as [| [| [| [| [| a]]]] rsp]; try discriminate h;
      inversion h; subst c'; intro; congruence.
Qed.

Lemma iterOpt_step_5mode_lift {k : nat} (hk : k > 0) {c1 c2 : Cfg5}
    (hguard : Guard5 c1) (h : iterOpt step_5mode k c1 = Some c2) :
  decode_blk (Phi c1) -->+ decode_blk (Phi c2).
Proof.
  revert c1 hguard h.
  induction k as [| k ih]; intros c1 hguard h; [lia |].
  cbn [iterOpt] in h.
  destruct (step_5mode c1) as [cm |] eqn:hs; [| discriminate h].
  destruct (step_5mode_correct c1 cm hguard hs) as [j [hj hblk]].
  pose proof (iterOpt_step_blk_plus hj hblk) as hp1.
  destruct k as [| k'].
  - inversion h; subst cm. exact hp1.
  - pose proof (step_5mode_preserves_guard c1 cm hguard hs) as hg'.
    exact (ptrans hp1 (ih ltac:(lia) cm hg' h)).
Qed.

Lemma iterOpt_step_sq_lift {k : nat} (hk : k > 0) (n : nat) {c1 c2 : CfgSq}
    (hguard : GuardSq c1) (h : iterOpt step_sq k c1 = Some c2) :
  exists n', decode_sq n c1 -->+ decode_sq n' c2.
Proof.
  revert n c1 hguard h.
  induction k as [| k ih]; intros n c1 hguard h; [lia |].
  cbn [iterOpt] in h.
  destruct (step_sq c1) as [cm |] eqn:hs; [| discriminate h].
  destruct (step_sq_lift n c1 cm hguard hs) as [n_mid [j [hj h5]]].
  pose proof (iterOpt_step_5mode_lift hj (psi_sq_guard n c1) h5) as hp1.
  destruct k as [| k'].
  - inversion h; subst cm. exists n_mid. exact hp1.
  - pose proof (step_sq_preserves_guard c1 cm hguard hs) as hg'.
    destruct (ih ltac:(lia) n_mid cm hg' h) as [n' hp2].
    exists n'. exact (ptrans hp1 hp2).
Qed.

Definition c0_sq : CfgSq := (hL, [SA 0], []).
Definition c319_sq : CfgSq := (h10B, [SA 1], [3; 1; 0; 1; 3; 1; 1; 1; 1; 1; 0; 1]).

Lemma init_reaches_c319 :
  exists n0, c0 -->* decode_sq n0 c319_sq.
Proof.
  assert (h2_iter : iterOpt step_blk 35 (M6_h11D, [L10; L1], []) = Some (Phi (Psi_sq 0 c0_sq)))
    by (vm_compute; reflexivity).
  pose proof (@iterOpt_step_blk_plus 35 ltac:(lia) _ _ h2_iter) as h2.
  assert (h3_iter : iterOpt step_sq 319 c0_sq = Some c319_sq)
    by (vm_compute; reflexivity).
  assert (hg0 : GuardSq c0_sq) by (intro hc; exfalso; exact (hc eq_refl)).
  destruct (@iterOpt_step_sq_lift 319 ltac:(lia) 0 _ _ hg0 h3_iter) as [n0 h3].
  exists n0.
  exact (etrans init_reaches_blk0 (etrans (pev h2) (pev h3))).
Qed.

(* ========================================================================== *)
(* Section 3: Scanning, Popping, Templates & Turnarounds                      *)
(* ========================================================================== *)

Definition SqReachesPlus (R1 R2 : list nat) : Prop :=
  exists k, k > 0 /\ iterOpt step_sq k (h10B, [SA 1], R1) = Some (h10B, [SA 1], R2).

Definition SqReachesStar (R1 R2 : list nat) : Prop :=
  exists k, iterOpt step_sq k (h10B, [SA 1], R1) = Some (h10B, [SA 1], R2).

Lemma sqReachesStar_refl (R : list nat) : SqReachesStar R R.
Proof. exists 0. reflexivity. Qed.

Lemma sqReachesStar_of_plus {R1 R2 : list nat} (h : SqReachesPlus R1 R2) :
  SqReachesStar R1 R2.
Proof. destruct h as [k [_ hk]]. exists k. exact hk. Qed.

Lemma sqReachesPlus_trans {R1 R2 R3 : list nat}
    (h1 : SqReachesPlus R1 R2) (h2 : SqReachesPlus R2 R3) :
  SqReachesPlus R1 R3.
Proof.
  destruct h1 as [k1 [hk1 hs1]], h2 as [k2 [hk2 hs2]].
  exists (k1 + k2). split; [lia | exact (iterOpt_trans hs1 hs2)].
Qed.

Lemma sqReachesPlus_star_trans {R1 R2 R3 : list nat}
    (h1 : SqReachesPlus R1 R2) (h2 : SqReachesStar R2 R3) :
  SqReachesPlus R1 R3.
Proof.
  destruct h1 as [k1 [hk1 hs1]], h2 as [k2 hs2].
  exists (k1 + k2). split; [lia | exact (iterOpt_trans hs1 hs2)].
Qed.

Lemma sqReachesStar_trans {R1 R2 R3 : list nat}
    (h1 : SqReachesStar R1 R2) (h2 : SqReachesStar R2 R3) :
  SqReachesStar R1 R3.
Proof.
  destruct h1 as [k1 hs1], h2 as [k2 hs2].
  exists (k1 + k2). exact (iterOpt_trans hs1 hs2).
Qed.

Lemma sqReachesPlus_to_tm {R1 R2 : list nat} (h : SqReachesPlus R1 R2) (n : nat) :
  exists n', decode_sq n (h10B, [SA 1], R1) -->+ decode_sq n' (h10B, [SA 1], R2).
Proof.
  destruct h as [k [hk hiter]].
  assert (hg : GuardSq (h10B, [SA 1], R1)) by (intro; discriminate).
  exact (@iterOpt_step_sq_lift k hk n _ _ hg hiter).
Qed.

Definition CfgSqReachesPlus (c1 c2 : CfgSq) : Prop :=
  exists k, k > 0 /\ iterOpt step_sq k c1 = Some c2.

Definition CfgSqReachesStar (c1 c2 : CfgSq) : Prop :=
  exists k, iterOpt step_sq k c1 = Some c2.

Lemma cfgSqReachesStar_of_iterOpt {k : nat} {c1 c2 : CfgSq}
    (h : iterOpt step_sq k c1 = Some c2) : CfgSqReachesStar c1 c2.
Proof. exists k. exact h. Qed.

Lemma cfgSqReachesPlus_of_iterOpt {k : nat} {c1 c2 : CfgSq}
    (h : iterOpt step_sq k c1 = Some c2) (hk : k > 0) : CfgSqReachesPlus c1 c2.
Proof. exists k. exact (conj hk h). Qed.

Lemma cfgSqReachesPlus_trans {c1 c2 c3 : CfgSq}
    (h1 : CfgSqReachesPlus c1 c2) (h2 : CfgSqReachesPlus c2 c3) :
  CfgSqReachesPlus c1 c3.
Proof.
  destruct h1 as [k1 [hk1 hs1]], h2 as [k2 [hk2 hs2]].
  exists (k1 + k2). split; [lia | exact (iterOpt_trans hs1 hs2)].
Qed.

Lemma cfgSqReachesStar_plus_trans {c1 c2 c3 : CfgSq}
    (h1 : CfgSqReachesStar c1 c2) (h2 : CfgSqReachesPlus c2 c3) :
  CfgSqReachesPlus c1 c3.
Proof.
  destruct h1 as [k1 hs1], h2 as [k2 [hk2 hs2]].
  exists (k1 + k2). split; [lia | exact (iterOpt_trans hs1 hs2)].
Qed.

Lemma incTop_incTop (ls : list SBlock) (d1 d2 : nat) :
  incTop (incTop ls d1) d2 = incTop ls (d1 + d2).
Proof.
  destruct ls as [| [k | k] lsp]; cbn [incTop]; f_equal; f_equal; lia.
Qed.

Lemma scan_ones_h10B (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq (2 * (k + 1)) (h10B, ls, repeat 1 (2 * (k + 1)) ++ R) =
    Some (h10B, SB 1 :: (repeat (SB 2) k ++ incTop ls 1), R).
Proof.
  revert R.
  induction k as [| k ih]; intros R; [reflexivity |].
  replace (S k) with (k + 1) by lia.
  rewrite (repeat_two_mul_append_two (k + 1) 1 R).
  replace (2 * (k + 1 + 1)) with (2 * (k + 1) + 2) by lia.
  eapply iterOpt_trans; [exact (ih (1 :: 1 :: R)) |].
  rewrite (repeat_succ k (SB 2)). reflexivity.
Qed.

Lemma scan_ones_h1E (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq (2 * (k + 1)) (h1E, ls, repeat 1 (2 * (k + 1)) ++ R) =
    Some (h1E, SB 0 :: (repeat (SB 2) k ++ incTop ls 2), R).
Proof.
  revert R.
  induction k as [| k ih]; intros R.
  - cbn [Nat.add Nat.mul repeat app iterOpt step_sq].
    rewrite incTop_incTop. reflexivity.
  - replace (S k) with (k + 1) by lia.
    rewrite (repeat_two_mul_append_two (k + 1) 1 R).
    replace (2 * (k + 1 + 1)) with (2 * (k + 1) + 2) by lia.
    eapply iterOpt_trans; [exact (ih (1 :: 1 :: R)) |].
    rewrite (repeat_succ k (SB 2)). reflexivity.
Qed.

Lemma scan_ones_h10F (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq k (h10F, ls, repeat 1 k ++ R) =
    Some (h10F, repeat (SA 0) k ++ ls, R).
Proof.
  revert ls.
  induction k as [| k ih]; intros ls; [reflexivity |].
  cbn [repeat app iterOpt step_sq].
  rewrite (ih (SA 0 :: ls)).
  rewrite repeat_append_cons_same, Nat.add_1_r. reflexivity.
Qed.

Lemma step_sq_hL_A0 (lsp : list SBlock) (h : lsp <> [SA 2]) (rs : list nat) :
  step_sq (hL, SA 0 :: lsp, rs) = Some (hL, lsp, 1 :: rs).
Proof.
  destruct lsp as [| [ [| [| [| k]]] | k ] [| sb3 lsp3]];
    try reflexivity; exfalso; exact (h eq_refl).
Qed.

Lemma repeat_A0_append_ne_A2 (k : nat) {ls : list SBlock} (h : ls <> [SA 2]) :
  repeat (SA 0) k ++ ls <> [SA 2].
Proof.
  destruct k as [| k]; [exact h | discriminate].
Qed.

Lemma pop_B2_run_hL (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq k (hL, repeat (SB 2) k ++ ls, R) =
    Some (hL, ls, repeat 1 (2 * k) ++ R).
Proof.
  revert R.
  induction k as [| k ih]; intros R; [reflexivity |].
  cbn [repeat app iterOpt step_sq].
  rewrite (ih (1 :: 1 :: R)).
  replace (S k) with (k + 1) by lia.
  rewrite <- repeat_two_mul_append_two. reflexivity.
Qed.

Definition stackAfterOnes (k : nat) (ls : list SBlock) : list SBlock :=
  match k with
  | 0 => SA 1 :: ls
  | S k' => SB 1 :: (repeat (SB 2) k' ++ (SA 2 :: ls))
  end.

Lemma scan_ones_h10B_any (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq (2 * k) (h10B, SA 1 :: ls, repeat 1 (2 * k) ++ R) =
    Some (h10B, stackAfterOnes k ls, R).
Proof.
  destruct k as [| k']; [reflexivity |].
  replace (S k') with (k' + 1) at 1 2 by lia.
  exact (scan_ones_h10B k' (SA 1 :: ls) R).
Qed.

Lemma incTop_stackAfterOnes (k : nat) (ls : list SBlock) :
  incTop (stackAfterOnes k ls) 1 = repeat (SB 2) k ++ (SA 2 :: ls).
Proof.
  destruct k; reflexivity.
Qed.

Lemma pop_B2_A2_hL (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq (k + 1) (hL, repeat (SB 2) k ++ (SA 2 :: ls), R) =
    Some (hL, ls, 3 :: (repeat 1 (2 * k) ++ R)).
Proof.
  eapply iterOpt_trans; [exact (pop_B2_run_hL k (SA 2 :: ls) R) | reflexivity].
Qed.

Lemma rep_B2_A2_ne_A2 (k : nat) (ls : list SBlock) (h : k >= 1 \/ ls <> []) :
  repeat (SB 2) k ++ (SA 2 :: ls) <> [SA 2].
Proof.
  destruct k as [| k].
  - cbn [repeat app]. destruct h as [hk | hls]; [lia | congruence].
  - discriminate.
Qed.

Lemma pop_B1_B2_A2_hL (k : nat) (ls : list SBlock) (R : list nat) :
  iterOpt step_sq (k + 2) (hL, SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), R) =
    Some (hL, ls, 3 :: (repeat 1 (2 * k + 1) ++ (0 :: R))).
Proof.
  replace (k + 2) with (1 + (k + 1)) by lia.
  assert (h1 : iterOpt step_sq 1 (hL, SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), R) =
               Some (hL, repeat (SB 2) k ++ (SA 2 :: ls), 1 :: 0 :: R)) by reflexivity.
  eapply iterOpt_trans; [exact h1 |].
  rewrite (pop_B2_A2_hL k ls (1 :: 0 :: R)), repeat_append_cons_same.
  reflexivity.
Qed.

Lemma bounce_hL_suffix (ss : list SBlock) (hS : ss = [] \/ ss = [SA 0; SA 2]) (R : list nat) :
  iterOpt step_sq 1 (hL, ss, R) = Some (h10B, [SA 1], R).
Proof.
  destruct hS as [-> | ->]; reflexivity.
Qed.

Lemma double3_reduction (R : list nat) :
  SqReachesPlus (3 :: 3 :: R) (1 :: 1 :: R).
Proof.
  exists 4. split; [lia | reflexivity].
Qed.

Definition TailWord (w z d : nat) : list nat :=
  repeat 1 w ++ (3 :: (repeat 1 z ++ [d; 1])).

Definition R_tail (w z d : nat) : list nat :=
  3 :: TailWord w z d.

Definition M_sq (v w z d : nat) : list nat :=
  3 :: (repeat 1 v ++ (2 :: 1 :: R_tail w z d)).

Definition M2_sq (v w z d : nat) : list nat :=
  3 :: (repeat 1 v ++ (2 :: R_tail w z d)).

Definition H_sq (v w0 z d : nat) : list nat :=
  3 :: (repeat 1 v ++ (0 :: R_tail w0 z d)).

Definition F_sq (u v j w0 z d : nat) : list nat :=
  3 :: (repeat 1 u ++ (3 :: (repeat 1 v ++ (3 :: (repeat 1 j ++ (0 :: R_tail w0 z d)))))).

Definition G_sq (v j w z d : nat) : list nat :=
  3 :: (repeat 1 v ++ (3 :: (repeat 1 j ++ (0 :: R_tail w z d)))).

Definition psiTilde (w z : nat) : nat * nat :=
  if w mod 2 =? 0 then (w + 1, z) else (w - 1, z + 2).

Definition psiShift (w z : nat) : nat * nat :=
  if w mod 2 =? 0 then (w + 1, z + 2) else (w - 1, z + 4).

Lemma psiTilde_psiTilde (w z : nat) :
  psiTilde (fst (psiTilde w z)) (snd (psiTilde w z)) = (w, z + 2).
Proof.
  unfold psiTilde.
  destruct (w mod 2 =? 0) eqn:Ew; cbn [fst snd]; split_ifs; f_equal; lia.
Qed.

Lemma psiTilde_snd_odd (w z : nat) (hz : z mod 2 = 1) :
  (snd (psiTilde w z)) mod 2 = 1.
Proof.
  unfold psiTilde. destruct (w mod 2 =? 0) eqn:Ew; cbn [snd]; lia.
Qed.

Lemma psiTilde_add_two (w z : nat) :
  psiTilde w (z + 2) = psiShift w z.
Proof.
  unfold psiTilde, psiShift. destruct (w mod 2 =? 0); f_equal; lia.
Qed.

Lemma psiShift_eq_psiTilde_step (w z : nat) :
  psiShift w z = (fst (psiTilde w z), snd (psiTilde w z) + 2).
Proof.
  unfold psiTilde, psiShift. destruct (w mod 2 =? 0); cbn [fst snd]; f_equal; lia.
Qed.

Lemma psiShift_psiTilde_add (w z k : nat) :
  psiShift (fst (psiTilde w z)) (snd (psiTilde w z) + 2 * k) = (w, z + 2 * k + 4).
Proof.
  unfold psiTilde, psiShift.
  destruct (w mod 2 =? 0) eqn:Ew; cbn [fst snd]; split_ifs; f_equal; lia.
Qed.

Definition stackP1 (u : nat) (ls : list SBlock) : list SBlock :=
  repeat (SB 2) u ++ (SA 2 :: SA 0 :: SA 2 :: ls).

Lemma prefix_P1_scan (u : nat) (ls : list SBlock) (R : list nat) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, 3 :: (repeat 1 (2 * (u + 1)) ++ (3 :: R)))
    (h10B, SA 1 :: stackP1 u ls, 1 :: R).
Proof.
  assert (h1 : CfgSqReachesPlus
      (h10B, SA 1 :: ls, 3 :: (repeat 1 (2 * (u + 1)) ++ (3 :: R)))
      (h1E, SA 0 :: SA 0 :: SA 2 :: ls, repeat 1 (2 * (u + 1)) ++ (3 :: R)))
    by (exists 1; split; [lia | reflexivity]).
  pose proof (cfgSqReachesPlus_of_iterOpt
    (scan_ones_h1E u (SA 0 :: SA 0 :: SA 2 :: ls) (3 :: R)) ltac:(lia)) as h2.
  assert (h3 : CfgSqReachesPlus
      (h1E, SB 0 :: (repeat (SB 2) u ++ (SA 2 :: SA 0 :: SA 2 :: ls)), 3 :: R)
      (h10B, SA 1 :: stackP1 u ls, 1 :: R))
    by (exists 2; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Lemma prefix_P1_pop (u : nat) (ls : list SBlock) (R' : list nat) :
  CfgSqReachesPlus
    (hL, stackP1 u ls, R')
    (hL, SA 0 :: SA 2 :: ls, 3 :: (repeat 1 (2 * u) ++ R')).
Proof.
  exact (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL u (SA 0 :: SA 2 :: ls) R') ltac:(lia)).
Qed.

Definition stackP2 (m : nat) (ls : list SBlock) : list SBlock :=
  repeat (SB 2) m ++ (SA 2 :: ls).

Lemma prefix_P2_scan (m : nat) (ls : list SBlock) (R : list nat) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, 1 :: (repeat 1 (2 * m) ++ (3 :: R)))
    (h10B, SA 1 :: stackP2 m ls, 1 :: R).
Proof.
  change (1 :: (repeat 1 (2 * m) ++ (3 :: R))) with (repeat 1 (S (2 * m)) ++ (3 :: R)).
  replace (S (2 * m)) with (2 * m + 1) by lia.
  rewrite repeat_succ_append.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any m ls (1 :: 3 :: R))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes m ls, 1 :: 3 :: R)
      (h10B, SA 1 :: stackP2 m ls, 1 :: R)).
  { exists 3. split; [lia | destruct m; reflexivity]. }
  exact (cfgSqReachesStar_plus_trans h1 h2).
Qed.

Lemma prefix_P2_pop (m : nat) (ls : list SBlock) (R' : list nat) :
  CfgSqReachesPlus
    (hL, stackP2 m ls, R')
    (hL, ls, 3 :: (repeat 1 (2 * m) ++ R')).
Proof.
  exact (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL m ls R') ltac:(lia)).
Qed.

Definition stackP3 (m : nat) (ss : list SBlock) : list SBlock :=
  SA 0 :: (repeat (SB 2) m ++ (SA 2 :: ss)).

Lemma prefix_P3_scan_from_S (m : nat) (ss : list SBlock) (R : list nat) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ss, repeat 1 (2 * m) ++ (3 :: 1 :: R))
    (h10B, SA 1 :: stackP3 m ss, R).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any m ss (3 :: 1 :: R))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes m ss, 3 :: 1 :: R)
      (h10B, SA 1 :: stackP3 m ss, R)).
  { exists 2. split; [lia | destruct m; reflexivity]. }
  exact (cfgSqReachesStar_plus_trans h1 h2).
Qed.

Lemma prefix_P3_scan (m : nat) (R : list nat) :
  CfgSqReachesPlus
    (h10B, [SA 1], 3 :: (repeat 1 (2 * m + 1) ++ (3 :: 1 :: R)))
    (h10B, SA 1 :: stackP3 m [SA 0; SA 2], R).
Proof.
  rewrite repeat_succ. cbn [app].
  assert (h0 : CfgSqReachesPlus
      (h10B, [SA 1], 3 :: 1 :: (repeat 1 (2 * m) ++ (3 :: 1 :: R)))
      (h10B, SA 1 :: [SA 0; SA 2], repeat 1 (2 * m) ++ (3 :: 1 :: R)))
    by (exists 2; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans h0 (prefix_P3_scan_from_S m [SA 0; SA 2] R)).
Qed.

Lemma prefix_M2_scan (u : nat) (ls : list SBlock) (R : list nat) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, 3 :: (repeat 1 (2 * (u + 1)) ++ (2 :: R)))
    (h10B, SA 1 :: stackP1 u ls, 0 :: R).
Proof.
  assert (h1 : CfgSqReachesPlus
      (h10B, SA 1 :: ls, 3 :: (repeat 1 (2 * (u + 1)) ++ (2 :: R)))
      (h1E, SA 0 :: SA 0 :: SA 2 :: ls, repeat 1 (2 * (u + 1)) ++ (2 :: R)))
    by (exists 1; split; [lia | reflexivity]).
  pose proof (cfgSqReachesPlus_of_iterOpt
    (scan_ones_h1E u (SA 0 :: SA 0 :: SA 2 :: ls) (2 :: R)) ltac:(lia)) as h2.
  assert (h3 : CfgSqReachesPlus
      (h1E, SB 0 :: (repeat (SB 2) u ++ (SA 2 :: SA 0 :: SA 2 :: ls)), 2 :: R)
      (h10B, SA 1 :: stackP1 u ls, 0 :: R))
    by (exists 2; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Definition enc_odd (a b c d : nat) : list nat :=
  3 :: (repeat 1 a ++ (0 :: TailWord b c d)).

Definition enc_even (a b c d : nat) : list nat :=
  repeat 1 (a - 1) ++ (0 :: 1 :: R_tail b c d).

Definition R_mid (c d : nat) : list nat :=
  if d =? 0 then 3 :: (repeat 1 c ++ [3; 1])
  else R_tail (c - 1) 1 0.

Lemma pass1_turnaround_d0 (r : nat) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r + 1) ++ [0; 1])
    (hL, ls, 3 :: (repeat 1 (2 * r + 1) ++ [3; 1])).
Proof.
  rewrite (repeat_succ_append (2 * r) 1 [0; 1]).
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r ls [1; 0; 1])) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r ls, [1; 0; 1])
      (hL, repeat (SB 2) r ++ (SA 2 :: ls), [1; 3; 1])).
  { exists 6. split; [lia | destruct r; reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL r ls [1; 3; 1]) ltac:(lia)) as h3.
  rewrite (repeat_append_cons_same (2 * r)) in h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3).
Qed.

Lemma pass1_turnaround_d2 (r : nat) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r + 1) ++ [2; 1])
    (hL, ls, R_tail (2 * r) 1 0).
Proof.
  rewrite (repeat_succ_append (2 * r) 1 [2; 1]).
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r ls [1; 2; 1])) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r ls, [1; 2; 1])
      (hL, repeat (SB 2) r ++ (SA 2 :: ls), [3; 1; 0; 1])).
  { exists 9. split; [lia | destruct r; reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL r ls [3; 1; 0; 1]) ltac:(lia)) as h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3).
Qed.

Lemma pass1_turnaround (r d : nat) (hd : d = 0 \/ d = 2) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r + 1) ++ [d; 1])
    (hL, ls, R_mid (2 * r + 1) d).
Proof.
  destruct hd as [-> | ->].
  - exact (pass1_turnaround_d0 r ls).
  - unfold R_mid. cbn [Nat.eqb].
    replace (2 * r + 1 - 1) with (2 * r) by lia.
    exact (pass1_turnaround_d2 r ls).
Qed.

Lemma pass2_turnaround (r : nat) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r + 1) ++ [3; 1])
    (hL, ls, R_tail (2 * r) 1 2).
Proof.
  rewrite (repeat_succ_append (2 * r) 1 [3; 1]).
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r ls [1; 3; 1])) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r ls, [1; 3; 1])
      (hL, repeat (SB 2) r ++ (SA 2 :: ls), [3; 1; 2; 1])).
  { exists 9. split; [lia | destruct r; reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL r ls [3; 1; 2; 1]) ltac:(lia)) as h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3).
Qed.

Lemma prefix_P2_scan_2 (m : nat) (ls : list SBlock) (R : list nat) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, 1 :: (repeat 1 (2 * m) ++ (2 :: R)))
    (h10B, SA 1 :: stackP2 m ls, 0 :: R).
Proof.
  change (1 :: (repeat 1 (2 * m) ++ (2 :: R))) with (repeat 1 (S (2 * m)) ++ (2 :: R)).
  replace (S (2 * m)) with (2 * m + 1) by lia.
  rewrite repeat_succ_append.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any m ls (1 :: 2 :: R))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes m ls, 1 :: 2 :: R)
      (h10B, SA 1 :: stackP2 m ls, 0 :: R)).
  { exists 3. split; [lia | destruct m; reflexivity]. }
  exact (cfgSqReachesStar_plus_trans h1 h2).
Qed.

Lemma exit_3_2 (R : list nat) :
  SqReachesPlus (3 :: 2 :: R) (1 :: 0 :: R).
Proof.
  exists 4. split; [lia | reflexivity].
Qed.

Lemma exit_odd_0_3 (r : nat) (R : list nat) :
  SqReachesPlus
    (repeat 1 (2 * r + 1) ++ (0 :: 3 :: R))
    (3 :: (repeat 1 (2 * r + 1) ++ (0 :: 1 :: R))).
Proof.
  rewrite (repeat_succ_append (2 * r)).
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r [] (1 :: 0 :: 3 :: R))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r [], 1 :: 0 :: 3 :: R)
      (hL, SB 1 :: (repeat (SB 2) r ++ [SA 2]), 1 :: R)).
  { exists 3. split; [lia | destruct r; reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B1_B2_A2_hL r [] (1 :: R)) ltac:(lia)) as h3.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (bounce_hL_suffix [] (or_introl eq_refl) (3 :: (repeat 1 (2 * r + 1) ++ (0 :: 1 :: R)))) ltac:(lia)) as h4.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4).
Qed.

Lemma turnaround_even_ones_d0 (r : nat) (ls' : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls', repeat 1 (2 * r) ++ [0; 1])
    (hL, ls', 3 :: (repeat 1 (2 * r + 1) ++ [0; 1])).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r ls' [0; 1])) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r ls', [0; 1])
      (hL, SB 1 :: (repeat (SB 2) r ++ (SA 2 :: ls')), [1])).
  { exists 4. split; [lia | destruct r; reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B1_B2_A2_hL r ls' [1]) ltac:(lia)) as h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3).
Qed.

Lemma turnaround_even_ones_d2 (r : nat) (ls' : list SBlock) (hls' : ls' <> []) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls', repeat 1 (2 * r) ++ [2; 1])
    (hL, ls', 3 :: (repeat 1 (2 * r + 1) ++ [2; 1])).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r ls' [2; 1])) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes r ls', [2; 1])
      (hL, SA 0 :: (repeat (SB 2) r ++ (SA 2 :: ls')), [2; 1])).
  { exists 5. split; [lia | destruct r; reflexivity]. }
  pose proof (rep_B2_A2_ne_A2 r ls' (or_intror hls')) as hne.
  assert (h3 : CfgSqReachesPlus
      (hL, SA 0 :: (repeat (SB 2) r ++ (SA 2 :: ls')), [2; 1])
      (hL, repeat (SB 2) r ++ (SA 2 :: ls'), [1; 2; 1])).
  { exists 1. split; [lia | cbn [iterOpt]; rewrite (step_sq_hL_A0 _ hne); reflexivity]. }
  pose proof (cfgSqReachesPlus_of_iterOpt (pop_B2_A2_hL r ls' [1; 2; 1]) ltac:(lia)) as h4.
  rewrite (repeat_append_cons_same (2 * r)) in h4.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4).
Qed.

Lemma turnaround_even_ones (r d : nat) (hd : d = 0 \/ d = 2) (ls' : list SBlock) (hls' : ls' <> []) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls', repeat 1 (2 * r) ++ [d; 1])
    (hL, ls', 3 :: (repeat 1 (2 * r + 1) ++ [d; 1])).
Proof.
  destruct hd as [-> | ->].
  - exact (turnaround_even_ones_d0 r ls').
  - exact (turnaround_even_ones_d2 r ls' hls').
Qed.

Lemma tail_reflect (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2)
    (ls : list SBlock) (hls : ls <> []) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, TailWord w z d)
    (hL, ls, R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  set (s := z / 2).
  assert (hz_eq : z = 2 * s + 1) by (unfold s; lia).
  destruct (w mod 2 =? 0) eqn:Ew.
  - set (k := w / 2).
    assert (hw_eq : w = 2 * k) by (unfold k; split_ifs; lia).
    assert (hpsi : psiTilde w z = (2 * k + 1, 2 * s + 1))
      by (unfold psiTilde; rewrite Ew; f_equal; lia).
    rewrite hpsi. cbn [fst snd].
    assert (htw : TailWord w z d = repeat 1 (2 * k) ++ (3 :: 1 :: (repeat 1 (2 * s) ++ [d; 1]))).
    { unfold TailWord. rewrite hw_eq, hz_eq, repeat_succ. reflexivity. }
    rewrite htw.
    pose proof (prefix_P3_scan_from_S k ls (repeat 1 (2 * s) ++ [d; 1])) as h1.
    pose proof (turnaround_even_ones s d hd (stackP3 k ls) ltac:(discriminate)) as h2.
    pose proof (rep_B2_A2_ne_A2 k ls (or_intror hls)) as hne.
    assert (h3 : CfgSqReachesPlus
        (hL, stackP3 k ls, 3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))
        (hL, repeat (SB 2) k ++ (SA 2 :: ls), 1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))).
    { exists 1. split; [lia | unfold stackP3; cbn [iterOpt]; rewrite (step_sq_hL_A0 _ hne); reflexivity]. }
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL k ls (1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * k)) in h4.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4).
  - set (k := w / 2).
    assert (hw_eq : w = 2 * k + 1) by (unfold k; split_ifs; lia).
    assert (hpsi : psiTilde w z = (2 * k, 2 * (s + 1) + 1))
      by (unfold psiTilde; rewrite Ew; f_equal; lia).
    rewrite hpsi. cbn [fst snd].
    assert (htw : TailWord w z d = 1 :: (repeat 1 (2 * k) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))).
    { unfold TailWord. rewrite hw_eq, hz_eq, (repeat_succ (2 * k) 1). reflexivity. }
    rewrite htw.
    pose proof (prefix_P2_scan k ls (repeat 1 (2 * s + 1) ++ [d; 1])) as h1.
    rewrite (cons_repeat_odd_append s 1 [d; 1]) in h1.
    assert (hsp2_ne : stackP2 k ls <> []) by (destruct k; discriminate).
    pose proof (turnaround_even_ones (s + 1) d hd (stackP2 k ls) hsp2_ne) as h2.
    pose proof (prefix_P2_pop k ls (3 :: (repeat 1 (2 * (s + 1) + 1) ++ [d; 1]))) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Lemma sep_0 (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, 0 :: R_tail w z d)
    (hL, ls, 2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  assert (h1 : CfgSqReachesPlus
      (h10B, SA 1 :: ls, 0 :: 3 :: TailWord w z d)
      (h10B, SA 1 :: SA 0 :: SA 1 :: ls, TailWord w z d))
    by (exists 2; split; [lia | reflexivity]).
  pose proof (tail_reflect w z d hz hd (SA 0 :: SA 1 :: ls) ltac:(discriminate)) as h2.
  assert (h3 : CfgSqReachesPlus
      (hL, SA 0 :: SA 1 :: ls, R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)
      (hL, ls, 2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))
    by (exists 2; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Lemma sep_even_0 (k : nat) (ls : list SBlock) (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * (k + 1)) ++ (0 :: R_tail w z d))
    (hL, ls, 3 :: (repeat 1 (2 * k + 1) ++ (0 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any (k + 1) ls (0 :: 3 :: TailWord w z d))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes (k + 1) ls, 0 :: 3 :: TailWord w z d)
      (h10B, SA 1 :: SA 0 :: SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), TailWord w z d)).
  { exists 2. split; [lia | replace (k + 1) with (S k) by lia; reflexivity]. }
  pose proof (tail_reflect w z d hz hd
    (SA 0 :: SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls))) ltac:(discriminate)) as h3.
  assert (h4 : CfgSqReachesPlus
      (hL, SA 0 :: SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)
      (hL, SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))
    by (exists 1; split; [lia | reflexivity]).
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B1_B2_A2_hL k ls (1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) ltac:(lia)) as h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5).
Qed.

Lemma sep_even_01 (k : nat) (ls : list SBlock) (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * k) ++ (0 :: 1 :: R_tail w z d))
    (hL, ls, 3 :: (repeat 1 (2 * k + 1) ++ (0 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k ls (0 :: 1 :: 3 :: TailWord w z d))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes k ls, 0 :: 1 :: 3 :: TailWord w z d)
      (h10B, SA 1 :: SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), TailWord w z d)).
  { exists 3. split; [lia | destruct k; reflexivity]. }
  pose proof (tail_reflect w z d hz hd
    (SB 1 :: (repeat (SB 2) k ++ (SA 2 :: ls))) ltac:(discriminate)) as h3.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B1_B2_A2_hL k ls (R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) ltac:(lia)) as h4.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4).
Qed.

Lemma sep_even_2 (k : nat) (ls : list SBlock) (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * k) ++ (2 :: R_tail w z d))
    (hL, ls, 3 :: (repeat 1 (2 * k) ++ (2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k ls (2 :: 3 :: TailWord w z d))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes k ls, 2 :: 3 :: TailWord w z d)
      (h10B, SA 1 :: SA 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), TailWord w z d)).
  { exists 2. split; [lia | destruct k; reflexivity]. }
  pose proof (tail_reflect w z d hz hd
    (SA 1 :: (repeat (SB 2) k ++ (SA 2 :: ls))) ltac:(discriminate)) as h3.
  assert (h4 : CfgSqReachesPlus
      (hL, SA 1 :: (repeat (SB 2) k ++ (SA 2 :: ls)), R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)
      (hL, repeat (SB 2) k ++ (SA 2 :: ls), 2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))
    by (exists 1; split; [lia | reflexivity]).
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL k ls (2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) ltac:(lia)) as h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5).
Qed.

Lemma sep_even_21 (k : nat) (ls : list SBlock) (hkL : k >= 1 \/ ls <> [])
    (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * k) ++ (2 :: 1 :: R_tail w z d))
    (hL, ls, 3 :: (repeat 1 (2 * k + 1) ++ (2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))).
Proof.
  pose proof (cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k ls (2 :: 1 :: 3 :: TailWord w z d))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes k ls, 2 :: 1 :: 3 :: TailWord w z d)
      (h10B, SA 1 :: SA 1 :: SA 0 :: (repeat (SB 2) k ++ (SA 2 :: ls)), TailWord w z d)).
  { exists 3. split; [lia | destruct k; reflexivity]. }
  pose proof (tail_reflect w z d hz hd
    (SA 1 :: SA 0 :: (repeat (SB 2) k ++ (SA 2 :: ls))) ltac:(discriminate)) as h3.
  pose proof (rep_B2_A2_ne_A2 k ls hkL) as hne.
  assert (h4 : CfgSqReachesPlus
      (hL, SA 1 :: SA 0 :: (repeat (SB 2) k ++ (SA 2 :: ls)), R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)
      (hL, repeat (SB 2) k ++ (SA 2 :: ls), 1 :: 2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)).
  { exists 2. split; [lia |].
    cbn [iterOpt].
    change (step_sq (hL, SA 1 :: SA 0 :: (repeat (SB 2) k ++ (SA 2 :: ls)),
             R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))
      with (Some (hL, SA 0 :: (repeat (SB 2) k ++ (SA 2 :: ls)),
             2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)).
    cbn [iterOpt].
    rewrite (step_sq_hL_A0 _ hne). reflexivity. }
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL k ls (1 :: 2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) ltac:(lia)) as h5.
  rewrite (repeat_append_cons_same (2 * k)) in h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5).
Qed.

Lemma sep_21_nil (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (2 :: 1 :: R_tail w z d) (2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  assert (h1 : CfgSqReachesPlus
      (h10B, [SA 1], 2 :: 1 :: 3 :: TailWord w z d)
      (h10B, [SA 1; SA 1; SA 0; SA 2], TailWord w z d))
    by (exists 3; split; [lia | reflexivity]).
  pose proof (tail_reflect w z d hz hd [SA 1; SA 0; SA 2] ltac:(discriminate)) as h2.
  assert (h3 : CfgSqReachesPlus
      (hL, [SA 1; SA 0; SA 2], R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)
      (h10B, [SA 1], 2 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))
    by (exists 2; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.


(* ========================================================================== *)
(* Section 4: 2-Adic Valuation, Contraction Loops, Phases 1-2 & Even Cascade  *)
(* ========================================================================== *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma div_mod_2 (n : nat) : n = 2 * (n / 2) + n mod 2 /\ (n mod 2 = 0 \/ n mod 2 = 1).
Proof.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma div_mod_4 (n : nat) :
  n = 4 * (n / 4) + n mod 4 /\
  (n mod 4 = 0 \/ n mod 4 = 1 \/ n mod 4 = 2 \/ n mod 4 = 3).
Proof.
  pose proof (Nat.div_mod n 4 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound n 4 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma add_even_mod2 (a k : nat) : (a + 2 * k) mod 2 = a mod 2.
Proof.
  pose proof (div_mod_2 a) as Ha.
  pose proof (div_mod_2 (a + 2 * k)) as Hak.
  lia.
Qed.

Lemma add_two_mod2 (a : nat) : (a + 2) mod 2 = a mod 2.
Proof.
  replace (a + 2) with (a + 2 * 1) by lia.
  apply add_even_mod2.
Qed.

Fixpoint splitTwoAux (fuel m : nat) : nat * nat :=
  match fuel with
  | 0 => (0, m)
  | S fuel' =>
    if m mod 2 =? 0 then
      let p := splitTwoAux fuel' (m / 2) in
      (fst p + 1, snd p)
    else (0, m)
  end.

Definition splitTwo (m : nat) : nat * nat := splitTwoAux m m.

Lemma splitTwoAux_eq (f1 f2 m : nat) (hm : m >= 1) (hf1 : m <= f1) (hf2 : m <= f2) :
  splitTwoAux f1 m = splitTwoAux f2 m.
Proof.
  revert f2 m hm hf1 hf2.
  induction f1 as [| f1 ih]; intros f2 m hm hf1 hf2; [lia |].
  destruct f2 as [| f2]; [lia |].
  cbn [splitTwoAux].
  destruct (m mod 2 =? 0) eqn:Em; [| reflexivity].
  pose proof (div_mod_2 m) as Hm.
  rewrite (ih f2 (m / 2) ltac:(lia) ltac:(lia) ltac:(lia)).
  reflexivity.
Qed.

Lemma splitTwo_odd (m : nat) (hm : m mod 2 = 1) : splitTwo m = (0, m).
Proof.
  destruct m as [| m'].
  - pose proof (div_mod_2 0); lia.
  - unfold splitTwo; cbn [splitTwoAux].
    destruct (S m' mod 2 =? 0) eqn:Em; [lia | reflexivity].
Qed.

Lemma splitTwo_two_mul (m : nat) (hm : m >= 1) :
  splitTwo (2 * m) = (fst (splitTwo m) + 1, snd (splitTwo m)).
Proof.
  unfold splitTwo.
  pose proof (div_mod_2 (2 * m)) as Hm.
  assert (h2m : 2 * m = S (2 * m - 1)) by lia.
  rewrite h2m at 1.
  cbn [splitTwoAux].
  destruct ((2 * m) mod 2 =? 0) eqn:Em; [| lia].
  replace ((2 * m) / 2) with m by lia.
  rewrite (splitTwoAux_eq (2 * m - 1) m m hm ltac:(lia) (Nat.le_refl m)).
  reflexivity.
Qed.

Lemma one_le_pow2 (t : nat) : 2 ^ t >= 1.
Proof.
  induction t as [| t ih]; cbn [Nat.pow]; lia.
Qed.

Lemma mul_pos_of_pos_of_odd {x a : nat} (hx : x >= 1) (ha : a mod 2 = 1) : x * a >= 1.
Proof.
  pose proof (div_mod_2 a) as Ha.
  assert (ha1 : a >= 1) by lia.
  nia.
Qed.

Lemma splitTwo_pow_mul_odd (nu a : nat) (ha : a mod 2 = 1) :
  splitTwo (2 ^ nu * a) = (nu, a).
Proof.
  induction nu as [| nu ih].
  - replace (2 ^ 0 * a) with a by (cbn [Nat.pow]; lia).
    exact (splitTwo_odd a ha).
  - pose proof (mul_pos_of_pos_of_odd (one_le_pow2 nu) ha) as hpos.
    replace (2 ^ S nu * a) with (2 * (2 ^ nu * a)) by (cbn [Nat.pow]; lia).
    rewrite (splitTwo_two_mul (2 ^ nu * a) hpos), ih.
    cbn [fst snd]. f_equal; lia.
Qed.

Lemma psiTilde_even (k z : nat) : psiTilde (2 * k) z = (2 * k + 1, z).
Proof. pose proof (div_mod_2 (2 * k)); unfold psiTilde; split_ifs; [reflexivity | lia]. Qed.

Lemma psiTilde_odd (k z : nat) : psiTilde (2 * k + 1) z = (2 * k, z + 2).
Proof. pose proof (div_mod_2 (2 * k + 1)); unfold psiTilde; split_ifs; [lia | f_equal; lia]. Qed.

Lemma bounce_from_A0A2 {R1 R2 : list nat}
    (h : CfgSqReachesPlus (h10B, [SA 1], R1) (hL, [SA 0; SA 2], R2)) :
  SqReachesPlus R1 R2.
Proof.
  exact (cfgSqReachesPlus_trans h
    (cfgSqReachesPlus_of_iterOpt (bounce_hL_suffix [SA 0; SA 2] (or_intror eq_refl) R2) ltac:(lia))).
Qed.

Lemma bounce_from_nil {R1 R2 : list nat}
    (h : CfgSqReachesPlus (h10B, [SA 1], R1) (hL, [], R2)) :
  SqReachesPlus R1 R2.
Proof.
  exact (cfgSqReachesPlus_trans h
    (cfgSqReachesPlus_of_iterOpt (bounce_hL_suffix [] (or_introl eq_refl) R2) ltac:(lia))).
Qed.

Lemma prefix_odd_3 (m : nat) (R : list nat) :
  CfgSqReachesPlus
    (h10B, [SA 1], 3 :: (repeat 1 (2 * m + 1) ++ R))
    (h10B, SA 1 :: [SA 0; SA 2], repeat 1 (2 * m) ++ R).
Proof.
  rewrite repeat_succ. cbn [app].
  exists 2. split; [lia | reflexivity].
Qed.

Lemma step_stackP3_hL (k : nat) (ls : list SBlock) (hkL : k >= 1 \/ ls <> []) (R : list nat) :
  CfgSqReachesPlus
    (hL, stackP3 k ls, R)
    (hL, repeat (SB 2) k ++ (SA 2 :: ls), 1 :: R).
Proof.
  exists 1. split; [lia |].
  unfold stackP3; cbn [iterOpt].
  rewrite (step_sq_hL_A0 _ (rep_B2_A2_ne_A2 k ls hkL)).
  reflexivity.
Qed.

Lemma two_cons_repeat_even (v : nat) (R : list nat) :
  1 :: 1 :: (repeat 1 (2 * v) ++ R) = repeat 1 (2 * (v + 1)) ++ R.
Proof.
  replace (2 * (v + 1)) with (2 + 2 * v) by lia.
  rewrite repeat_add. reflexivity.
Qed.

Lemma M2_sq_odd_step (m w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (M2_sq (2 * m + 1) w z0 d) (M2_sq (2 * m) (fst (psiTilde w z0)) (snd (psiTilde w z0)) d).
Proof.
  apply bounce_from_A0A2.
  exact (cfgSqReachesPlus_trans
    (prefix_odd_3 m (2 :: R_tail w z0 d))
    (sep_even_2 m [SA 0; SA 2] w z0 d hz0 hd)).
Qed.

Lemma M_sq_odd_to_M2 (m w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (M_sq (2 * m + 1) w z d) (M2_sq (2 * m) w (z + 2) d).
Proof.
  assert (hb1 : SqReachesPlus (M_sq (2 * m + 1) w z d)
      (M2_sq (2 * m + 1) (fst (psiTilde w z)) (snd (psiTilde w z)) d)).
  { apply bounce_from_A0A2.
    exact (cfgSqReachesPlus_trans
      (prefix_odd_3 m (2 :: 1 :: R_tail w z d))
      (sep_even_21 m [SA 0; SA 2] ltac:(right; intro; discriminate) w z d hz hd)). }
  pose proof (M2_sq_odd_step m (fst (psiTilde w z)) (snd (psiTilde w z)) d
    (psiTilde_snd_odd w z hz) hd) as hb2.
  rewrite psiTilde_psiTilde in hb2. cbn [fst snd] in hb2.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma loop_L1F (u v j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (F_sq (2 * u + 4) (2 * v) (2 * j + 1) w z d)
    (F_sq (2 * u) (2 * v) (2 * j + 3) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus
      (F_sq (2 * u + 4) (2 * v) (2 * j + 1) w z d)
      (3 :: (repeat 1 (2 * u + 2) ++ (3 :: (repeat 1 (2 * v) ++
        (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))))).
  { apply bounce_from_A0A2.
    unfold F_sq.
    replace (2 * u + 4) with (2 * (u + 1 + 1)) by lia.
    pose proof (prefix_P1_scan (u + 1) [] (repeat 1 (2 * v) ++
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))))) as h1.
    pose proof (prefix_P2_scan v (stackP1 (u + 1) [])
      (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))) as h2.
    rewrite (cons_repeat_odd_append j 1 (0 :: R_tail w z d)) in h2.
    pose proof (sep_even_0 j (stackP2 v (stackP1 (u + 1) [])) w z d hz hd) as h3.
    fold wt zt in h3.
    pose proof (prefix_P2_pop v (stackP1 (u + 1) [])
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h4.
    pose proof (prefix_P1_pop (u + 1) []
      (3 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))) as h5.
    replace (2 * (u + 1)) with (2 * u + 2) in h5 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5). }
  assert (hb2 : SqReachesPlus
      (3 :: (repeat 1 (2 * u + 2) ++ (3 :: (repeat 1 (2 * v) ++
        (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))))
      (F_sq (2 * u) (2 * v) (2 * j + 3) w (z + 2) d)).
  { apply bounce_from_A0A2.
    replace (2 * u + 2) with (2 * (u + 1)) by lia.
    pose proof (prefix_P1_scan u [] (repeat 1 (2 * v) ++
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d))))) as h1.
    pose proof (prefix_P2_scan v (stackP1 u [])
      (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d))) as h2.
    rewrite (cons_repeat_odd_append j 1 (0 :: 1 :: R_tail wt zt d)) in h2.
    pose proof (sep_even_01 (j + 1) (stackP2 v (stackP1 u [])) wt zt d
      (psiTilde_snd_odd w z hz) hd) as h3.
    unfold wt, zt in h3; rewrite psiTilde_psiTilde in h3; cbn [fst snd] in h3.
    replace (2 * (j + 1) + 1) with (2 * j + 3) in h3 by lia.
    pose proof (prefix_P2_pop v (stackP1 u [])
      (3 :: (repeat 1 (2 * j + 3) ++ (0 :: R_tail w (z + 2) d)))) as h4.
    pose proof (prefix_P1_pop u []
      (3 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 3) ++ (0 :: R_tail w (z + 2) d)))))) as h5.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma bridge_F2 (v j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (F_sq 2 (2 * v) (2 * j + 1) w z d)
    (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus
      (F_sq 2 (2 * v) (2 * j + 1) w z d)
      (3 :: 3 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))).
  { apply bounce_from_A0A2.
    pose proof (prefix_P1_scan 0 [] (repeat 1 (2 * v) ++
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))))) as h1.
    pose proof (prefix_P2_scan v (stackP1 0 [])
      (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))) as h2.
    rewrite (cons_repeat_odd_append j 1 (0 :: R_tail w z d)) in h2.
    pose proof (sep_even_0 j (stackP2 v (stackP1 0 [])) w z d hz hd) as h3.
    fold wt zt in h3.
    pose proof (prefix_P2_pop v (stackP1 0 [])
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h4.
    pose proof (prefix_P1_pop 0 []
      (3 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))) as h5.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5). }
  pose proof (double3_reduction (repeat 1 (2 * v) ++
    (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d))))) as hb2.
  assert (hb3 : SqReachesPlus
      (1 :: 1 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d)).
  { apply bounce_from_nil.
    rewrite two_cons_repeat_even, (repeat_succ (2 * j) 1). cbn [app].
    pose proof (prefix_P3_scan_from_S (v + 1) []
      (repeat 1 (2 * j) ++ (0 :: 1 :: R_tail wt zt d))) as h1.
    pose proof (sep_even_01 j (stackP3 (v + 1) []) wt zt d
      (psiTilde_snd_odd w z hz) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    pose proof (step_stackP3_hL (v + 1) [] ltac:(left; lia)
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL (v + 1) [] (1 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * (v + 1))) in h4.
    replace (2 * (v + 1) + 1) with (2 * v + 3) in h4 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  exact (sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3).
Qed.

Lemma bridge_F0_ge3 (v j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (F_sq 0 (2 * v) (2 * j + 3) w z d)
    (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  pose proof (double3_reduction (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 3) ++ (0 :: R_tail w z d))))) as hb1.
  assert (hb2 : SqReachesPlus
      (1 :: 1 :: (repeat 1 (2 * v) ++ (3 :: (repeat 1 (2 * j + 3) ++ (0 :: R_tail w z d)))))
      (3 :: (repeat 1 (2 * v + 3) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))).
  { apply bounce_from_nil.
    rewrite two_cons_repeat_even.
    replace (2 * j + 3) with (2 * (j + 1) + 1) by lia.
    rewrite (repeat_succ (2 * (j + 1)) 1). cbn [app].
    pose proof (prefix_P3_scan_from_S (v + 1) []
      (repeat 1 (2 * (j + 1)) ++ (0 :: R_tail w z d))) as h1.
    pose proof (sep_even_0 j (stackP3 (v + 1) []) w z d hz hd) as h2.
    fold wt zt in h2.
    pose proof (step_stackP3_hL (v + 1) [] ltac:(left; lia)
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL (v + 1) [] (1 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * (v + 1))) in h4.
    replace (2 * (v + 1) + 1) with (2 * v + 3) in h4 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  assert (hb3 : SqReachesPlus
      (3 :: (repeat 1 (2 * v + 3) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d)).
  { apply bounce_from_A0A2.
    replace (2 * v + 3) with (2 * (v + 1) + 1) at 1 by lia.
    rewrite (repeat_succ (2 * j) 1). cbn [app].
    pose proof (prefix_P3_scan (v + 1) (repeat 1 (2 * j) ++ (0 :: 1 :: R_tail wt zt d))) as h1.
    pose proof (sep_even_01 j (stackP3 (v + 1) [SA 0; SA 2]) wt zt d
      (psiTilde_snd_odd w z hz) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    pose proof (step_stackP3_hL (v + 1) [SA 0; SA 2] ltac:(left; lia)
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL (v + 1) [SA 0; SA 2] (1 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * (v + 1))) in h4.
    replace (2 * (v + 1) + 1) with (2 * v + 3) in h4 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  exact (sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3).
Qed.

Lemma bridge_F0_1 (v w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (F_sq 0 (2 * v) 1 w z d)
    (M_sq (2 * v + 3) (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  pose proof (double3_reduction (repeat 1 (2 * v) ++ (3 :: 1 :: 0 :: R_tail w z d))) as hb1.
  assert (hb2 : SqReachesPlus
      (1 :: 1 :: (repeat 1 (2 * v) ++ (3 :: 1 :: 0 :: R_tail w z d)))
      (M_sq (2 * v + 3) wt zt d)).
  { apply bounce_from_nil.
    rewrite two_cons_repeat_even.
    pose proof (prefix_P3_scan_from_S (v + 1) [] (0 :: R_tail w z d)) as h1.
    pose proof (sep_0 w z d hz hd (stackP3 (v + 1) [])) as h2.
    fold wt zt in h2.
    pose proof (step_stackP3_hL (v + 1) [] ltac:(left; lia)
      (2 :: 1 :: R_tail wt zt d)) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL (v + 1) [] (1 :: 2 :: 1 :: R_tail wt zt d)) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * (v + 1))) in h4.
    replace (2 * (v + 1) + 1) with (2 * v + 3) in h4 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma loop_L2G (m j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq (2 * m + 1) (2 * j + 3) w z d)
    (G_sq (2 * m + 1) (2 * j + 1) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus
      (G_sq (2 * m + 1) (2 * j + 3) w z d)
      (3 :: (repeat 1 (2 * m + 1) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))).
  { apply bounce_from_A0A2.
    unfold G_sq.
    replace (2 * j + 3) with (2 * (j + 1) + 1) by lia.
    rewrite (repeat_succ (2 * (j + 1)) 1). cbn [app].
    pose proof (prefix_P3_scan m (repeat 1 (2 * (j + 1)) ++ (0 :: R_tail w z d))) as h1.
    pose proof (sep_even_0 j (stackP3 m [SA 0; SA 2]) w z d hz hd) as h2.
    fold wt zt in h2.
    pose proof (step_stackP3_hL m [SA 0; SA 2] ltac:(right; intro; discriminate)
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL m [SA 0; SA 2] (1 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * m)) in h4.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  assert (hb2 : SqReachesPlus
      (3 :: (repeat 1 (2 * m + 1) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * m + 1) (2 * j + 1) w (z + 2) d)).
  { apply bounce_from_A0A2.
    rewrite (repeat_succ (2 * j) 1). cbn [app].
    pose proof (prefix_P3_scan m (repeat 1 (2 * j) ++ (0 :: 1 :: R_tail wt zt d))) as h1.
    pose proof (sep_even_01 j (stackP3 m [SA 0; SA 2]) wt zt d
      (psiTilde_snd_odd w z hz) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    pose proof (step_stackP3_hL m [SA 0; SA 2] ltac:(right; intro; discriminate)
      (3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) as h3.
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL m [SA 0; SA 2] (1 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: R_tail w (z + 2) d)))) ltac:(lia)) as h4.
    rewrite (repeat_append_cons_same (2 * m)) in h4.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma G_odd_1_to_M (m w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq (2 * m + 1) 1 w z d)
    (M_sq (2 * m + 1) (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  apply bounce_from_A0A2.
  pose proof (prefix_P3_scan m (0 :: R_tail w z d)) as h1.
  pose proof (sep_0 w z d hz hd (stackP3 m [SA 0; SA 2])) as h2.
  pose proof (step_stackP3_hL m [SA 0; SA 2] ltac:(right; intro; discriminate)
    (2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) as h3.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL m [SA 0; SA 2] (1 :: 2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) ltac:(lia)) as h4.
  rewrite (repeat_append_cons_same (2 * m)) in h4.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4).
Qed.

Lemma G_odd_drain (m j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq (2 * m + 1) (2 * j + 1) w z d)
    (M2_sq (2 * m) (fst (psiTilde w z)) (snd (psiTilde w z) + 2 * j + 2) d).
Proof.
  revert z hz.
  induction j as [| j ih]; intros z hz.
  - pose proof (G_odd_1_to_M m w z d hz hd) as h1.
    pose proof (M_sq_odd_to_M2 m (fst (psiTilde w z)) (snd (psiTilde w z)) d
      (psiTilde_snd_odd w z hz) hd) as h2.
    replace (snd (psiTilde w z) + 2 * 0 + 2) with (snd (psiTilde w z) + 2) by lia.
    exact (sqReachesPlus_trans h1 h2).
  - replace (2 * S j + 1) with (2 * j + 3) by lia.
    pose proof (loop_L2G m j w z d hz hd) as h1.
    pose proof (ih (z + 2) ltac:(rewrite add_two_mod2; exact hz)) as h2.
    rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
    cbn [fst snd] in h2.
    replace (snd (psiTilde w z) + 2 + 2 * j + 2) with (snd (psiTilde w z) + 2 * S j + 2) in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

Lemma F_universal_drain (u v j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (F_sq (2 * u) (2 * v) (2 * j + 1) w z d)
    (M2_sq (2 * v + 2) (fst (psiTilde w z)) (snd (psiTilde w z) + 2 * (u + j + 1)) d).
Proof.
  assert (h_even_odd : forall k u0, (u0 = 0 \/ u0 = 1) -> forall j0 z0, z0 mod 2 = 1 ->
      SqReachesPlus
        (F_sq (2 * (2 * k + u0)) (2 * v) (2 * j0 + 1) w z0 d)
        (M2_sq (2 * v + 2) (fst (psiTilde w z0)) (snd (psiTilde w z0) + 2 * (2 * k + u0 + j0 + 1)) d)).
  { induction k as [| k ih]; intros u0 hu0 j0 z0 hz0.
    - destruct hu0 as [-> | ->].
      + destruct j0 as [| j'].
        * pose proof (bridge_F0_1 v w z0 d hz0 hd) as h1.
          pose proof (M_sq_odd_to_M2 (v + 1) (fst (psiTilde w z0)) (snd (psiTilde w z0)) d
            (psiTilde_snd_odd w z0 hz0) hd) as h2.
          replace (2 * (v + 1) + 1) with (2 * v + 3) in h2 by lia.
          replace (2 * (v + 1)) with (2 * v + 2) in h2 by lia.
          replace (snd (psiTilde w z0) + 2 * (2 * 0 + 0 + 0 + 1)) with (snd (psiTilde w z0) + 2) by lia.
          exact (sqReachesPlus_trans h1 h2).
        * replace (2 * S j' + 1) with (2 * j' + 3) by lia.
          pose proof (bridge_F0_ge3 v j' w z0 d hz0 hd) as h1.
          pose proof (G_odd_drain (v + 1) j' w (z0 + 2) d ltac:(rewrite add_two_mod2; exact hz0) hd) as h2.
          rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
          cbn [fst snd] in h2.
          replace (2 * (v + 1) + 1) with (2 * v + 3) in h2 by lia.
          replace (2 * (v + 1)) with (2 * v + 2) in h2 by lia.
          replace (snd (psiTilde w z0) + 2 + 2 * j' + 2) with
            (snd (psiTilde w z0) + 2 * (2 * 0 + 0 + S j' + 1)) in h2 by lia.
          exact (sqReachesPlus_trans h1 h2).
      + replace (2 * (2 * 0 + 1)) with 2 by lia.
        pose proof (bridge_F2 v j0 w z0 d hz0 hd) as h1.
        pose proof (G_odd_drain (v + 1) j0 w (z0 + 2) d ltac:(rewrite add_two_mod2; exact hz0) hd) as h2.
        rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
        cbn [fst snd] in h2.
        replace (2 * (v + 1) + 1) with (2 * v + 3) in h2 by lia.
        replace (2 * (v + 1)) with (2 * v + 2) in h2 by lia.
        replace (snd (psiTilde w z0) + 2 + 2 * j0 + 2) with
          (snd (psiTilde w z0) + 2 * (2 * 0 + 1 + j0 + 1)) in h2 by lia.
        exact (sqReachesPlus_trans h1 h2).
    - replace (2 * (2 * S k + u0)) with (2 * (2 * k + u0) + 4) by lia.
      pose proof (loop_L1F (2 * k + u0) v j0 w z0 d hz0 hd) as h1.
      pose proof (ih u0 hu0 (j0 + 1) (z0 + 2) ltac:(rewrite add_two_mod2; exact hz0)) as h2.
      rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
      cbn [fst snd] in h2.
      replace (2 * (j0 + 1) + 1) with (2 * j0 + 3) in h2 by lia.
      replace (snd (psiTilde w z0) + 2 + 2 * (2 * k + u0 + (j0 + 1) + 1)) with
        (snd (psiTilde w z0) + 2 * (2 * S k + u0 + j0 + 1)) in h2 by lia.
      exact (sqReachesPlus_trans h1 h2). }
  destruct (div_mod_2 u) as [hu_eq hmod].
  pose proof (h_even_odd (u / 2) (u mod 2) hmod j z hz) as hmain.
  rewrite <- hu_eq in hmain.
  exact hmain.
Qed.

Lemma loop_LH (m w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (H_sq (2 * m + 3) w z d)
    (H_sq (2 * m + 1) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus
      (H_sq (2 * m + 3) w z d)
      (3 :: (repeat 1 (2 * m + 1) ++ (0 :: 1 :: R_tail wt zt d)))).
  { apply bounce_from_A0A2.
    pose proof (prefix_odd_3 (m + 1) (0 :: R_tail w z d)) as h1.
    replace (2 * (m + 1) + 1) with (2 * m + 3) in h1 by lia.
    pose proof (sep_even_0 m [SA 0; SA 2] w z d hz hd) as h2.
    fold wt zt in h2.
    exact (cfgSqReachesPlus_trans h1 h2). }
  assert (hb2 : SqReachesPlus
      (3 :: (repeat 1 (2 * m + 1) ++ (0 :: 1 :: R_tail wt zt d)))
      (H_sq (2 * m + 1) w (z + 2) d)).
  { apply bounce_from_A0A2.
    pose proof (prefix_odd_3 m (0 :: 1 :: R_tail wt zt d)) as h1.
    pose proof (sep_even_01 m [SA 0; SA 2] wt zt d (psiTilde_snd_odd w z hz) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    exact (cfgSqReachesPlus_trans h1 h2). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma H_base_to_M2 (w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (H_sq 1 w z d)
    (M2_sq 0 (fst (psiTilde w z)) (snd (psiTilde w z) + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus (H_sq 1 w z d) (2 :: 1 :: R_tail wt zt d)).
  { apply bounce_from_A0A2.
    exact (cfgSqReachesPlus_trans (prefix_odd_3 0 (0 :: R_tail w z d)) (sep_0 w z d hz hd [SA 0; SA 2])). }
  pose proof (sep_21_nil wt zt d (psiTilde_snd_odd w z hz) hd) as hb2.
  unfold wt, zt in hb2; rewrite psiTilde_psiTilde in hb2; cbn [fst snd] in hb2.
  assert (hb3 : SqReachesPlus (2 :: R_tail w (z + 2) d) (M2_sq 0 wt (zt + 2) d)).
  { apply bounce_from_nil.
    pose proof (sep_even_2 0 [] w (z + 2) d ltac:(rewrite add_two_mod2; exact hz) hd) as h.
    rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h.
    cbn [fst snd] in h. fold wt zt in h.
    exact h. }
  exact (sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3).
Qed.

Lemma H_drain (m w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (H_sq (2 * m + 1) w z d)
    (M2_sq 0 (fst (psiTilde w z)) (snd (psiTilde w z) + 2 * m + 2) d).
Proof.
  revert z hz.
  induction m as [| m ih]; intros z hz.
  - replace (snd (psiTilde w z) + 2 * 0 + 2) with (snd (psiTilde w z) + 2) by lia.
    exact (H_base_to_M2 w z d hz hd).
  - replace (2 * S m + 1) with (2 * m + 3) by lia.
    pose proof (loop_LH m w z d hz hd) as h1.
    pose proof (ih (z + 2) ltac:(rewrite add_two_mod2; exact hz)) as h2.
    rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
    cbn [fst snd] in h2.
    replace (snd (psiTilde w z) + 2 + 2 * m + 2) with (snd (psiTilde w z) + 2 * S m + 2) in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

(* Phase 1: Unified J_even / J_odd and enc_odd -> M2_sq *)

Definition J_even (m r w z d : nat) : list nat :=
  3 :: (repeat 1 (2 * m) ++ (3 :: (repeat 1 (2 * r) ++ (2 :: R_tail w z d)))).

Definition J_odd (m r w z d : nat) : list nat :=
  3 :: (repeat 1 (2 * m) ++ (3 :: (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail w z d)))).

Lemma pop_A0_run_hL (k : nat) (ls : list SBlock) (hls : ls <> [SA 2]) (R : list nat) :
  iterOpt step_sq k (hL, repeat (SA 0) k ++ ls, R) =
    Some (hL, ls, repeat 1 k ++ R).
Proof.
  revert R.
  induction k as [| k ih]; intros R; [reflexivity |].
  cbn [repeat app iterOpt].
  rewrite (step_sq_hL_A0 _ (repeat_A0_append_ne_A2 k hls) R).
  rewrite (ih (1 :: R)), repeat_append_cons_same, repeat_succ.
  reflexivity.
Qed.

Lemma enc_odd_b1_step1 (m s d : nat) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_odd (2 * m + 1) 1 (2 * s + 1) d)
    (3 :: (repeat 1 (2 * m + 1) ++ (0 :: R_mid (2 * s + 1) d))).
Proof.
  apply bounce_from_A0A2.
  change (enc_odd (2 * m + 1) 1 (2 * s + 1) d)
    with (3 :: (repeat 1 (2 * m + 1) ++ (0 :: 1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))).
  pose proof (prefix_odd_3 m (0 :: 1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))) as h1.
  pose proof (cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m [SA 0; SA 2] (0 :: 1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))) as h2.
  assert (h3 : CfgSqReachesPlus
      (h10B, stackAfterOnes m [SA 0; SA 2], 0 :: 1 :: 3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))
      (h10B, SA 1 :: SB 1 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]), repeat 1 (2 * s + 1) ++ [d; 1])).
  { exists 3. split; [lia | destruct m; reflexivity]. }
  pose proof (pass1_turnaround s d hd (SB 1 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))) as h4.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B1_B2_A2_hL m [SA 0; SA 2] (R_mid (2 * s + 1) d)) ltac:(lia)) as h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 (cfgSqReachesStar_plus_trans h2 h3)) h4) h5).
Qed.

Lemma enc_odd_ge2_mid (m k s d : nat) (hd : d = 0 \/ d = 2) :
  CfgSqReachesPlus
    (h10B, [SA 1], enc_odd (2 * m + 1) (k + 2) (2 * s + 1) d)
    (h10B, SA 1 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]),
      repeat 1 k ++ (2 :: R_mid (2 * s + 1) d)).
Proof.
  assert (h0 : enc_odd (2 * m + 1) (k + 2) (2 * s + 1) d =
      3 :: (repeat 1 (2 * m + 1) ++ (0 :: 1 :: (repeat 1 (k + 1) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))))).
  { unfold enc_odd, TailWord. replace (k + 2) with ((k + 1) + 1) by lia.
    rewrite (repeat_succ (k + 1) 1). reflexivity. }
  rewrite h0.
  pose proof (prefix_odd_3 m
    (0 :: 1 :: (repeat 1 (k + 1) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))))) as h1.
  pose proof (cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m [SA 0; SA 2]
      (0 :: 1 :: (repeat 1 (k + 1) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))))) as h2.
  assert (h3 : CfgSqReachesPlus
      (h10B, stackAfterOnes m [SA 0; SA 2],
        0 :: 1 :: (repeat 1 (k + 1) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))))
      (h10F, SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]),
        repeat 1 (k + 1) ++ (3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))).
  { exists 2. split; [lia | destruct m; reflexivity]. }
  pose proof (cfgSqReachesStar_of_iterOpt
    (scan_ones_h10F (k + 1) (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))
      (3 :: (repeat 1 (2 * s + 1) ++ [d; 1])))) as h4.
  assert (h5 : CfgSqReachesPlus
      (h10F, repeat (SA 0) (k + 1) ++ (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2])),
        3 :: (repeat 1 (2 * s + 1) ++ [d; 1]))
      (h10B, SA 1 :: SA 1 :: (repeat (SA 0) k ++ (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))),
        repeat 1 (2 * s + 1) ++ [d; 1])).
  { exists 1. split; [lia | rewrite repeat_succ; reflexivity]. }
  pose proof (pass1_turnaround s d hd
    (SA 1 :: (repeat (SA 0) k ++ (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))))) as h6.
  assert (h7 : CfgSqReachesPlus
      (hL, SA 1 :: (repeat (SA 0) k ++ (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))), R_mid (2 * s + 1) d)
      (hL, repeat (SA 0) k ++ (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2])), 2 :: R_mid (2 * s + 1) d))
    by (exists 1; split; [lia | reflexivity]).
  pose proof (cfgSqReachesStar_of_iterOpt
    (pop_A0_run_hL k (SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]))
      ltac:(discriminate) (2 :: R_mid (2 * s + 1) d))) as h8.
  assert (h9 : CfgSqReachesPlus
      (hL, SB 0 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]), repeat 1 k ++ (2 :: R_mid (2 * s + 1) d))
      (h10B, SA 1 :: (repeat (SB 2) m ++ [SA 2; SA 0; SA 2]), repeat 1 k ++ (2 :: R_mid (2 * s + 1) d)))
    by (exists 1; split; [lia | reflexivity]).
  exact (cfgSqReachesPlus_trans
    (cfgSqReachesPlus_trans
      (cfgSqReachesPlus_trans
        (cfgSqReachesPlus_trans
          (cfgSqReachesPlus_trans h1 (cfgSqReachesStar_plus_trans h2 h3))
          (cfgSqReachesStar_plus_trans h4 h5))
        h6)
      h7)
    (cfgSqReachesStar_plus_trans h8 h9)).
Qed.

Lemma rmid_even_2 (r s d : nat) (hd : d = 0 \/ d = 2) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r) ++ (2 :: R_mid (2 * s + 1) d))
    (hL, ls, 3 :: (repeat 1 (2 * r) ++ (2 :: R_tail (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d)))).
Proof.
  destruct hd as [-> | ->].
  - unfold R_mid; cbn [Nat.eqb Nat.sub].
    pose proof (cfgSqReachesStar_of_iterOpt
      (scan_ones_h10B_any r ls (2 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1])))) as h1.
    assert (h2 : CfgSqReachesPlus
        (h10B, stackAfterOnes r ls, 2 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))
        (h10B, SA 1 :: SA 1 :: (repeat (SB 2) r ++ (SA 2 :: ls)), repeat 1 (2 * s + 1) ++ [3; 1])).
    { exists 2. split; [lia | destruct r; reflexivity]. }
    pose proof (pass2_turnaround s (SA 1 :: (repeat (SB 2) r ++ (SA 2 :: ls)))) as h3.
    assert (h4 : CfgSqReachesPlus
        (hL, SA 1 :: (repeat (SB 2) r ++ (SA 2 :: ls)), R_tail (2 * s) 1 2)
        (hL, repeat (SB 2) r ++ (SA 2 :: ls), 2 :: R_tail (2 * s) 1 2))
      by (exists 1; split; [lia | reflexivity]).
    pose proof (cfgSqReachesPlus_of_iterOpt
      (pop_B2_A2_hL r ls (2 :: R_tail (2 * s) 1 2)) ltac:(lia)) as h5.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5).
  - unfold R_mid; cbn [Nat.eqb Nat.sub].
    replace (2 * s + 1 - 1) with (2 * s) by lia.
    pose proof (sep_even_2 r ls (2 * s) 1 0 eq_refl (or_introl eq_refl)) as h.
    rewrite psiTilde_even in h. cbn [fst snd] in h.
    exact h.
Qed.

Lemma rmid_odd_2 (r s d : nat) (hd : d = 0 \/ d = 2) (ls : list SBlock) :
  CfgSqReachesPlus
    (h10B, SA 1 :: ls, repeat 1 (2 * r + 1) ++ (2 :: R_mid (2 * s + 1) d))
    (hL, ls, 3 :: (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d)))).
Proof.
  rewrite (repeat_succ (2 * r) 1). cbn [app].
  pose proof (prefix_P2_scan_2 r ls (R_mid (2 * s + 1) d)) as hp.
  destruct hd as [-> | ->].
  - unfold R_mid in hp |- *; cbn [Nat.eqb Nat.sub] in hp |- *.
    assert (h2 : CfgSqReachesPlus
        (h10B, SA 1 :: stackP2 r ls, 0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))
        (h10B, SA 1 :: SA 0 :: SA 1 :: stackP2 r ls, repeat 1 (2 * s + 1) ++ [3; 1]))
      by (exists 2; split; [lia | reflexivity]).
    pose proof (pass2_turnaround s (SA 0 :: SA 1 :: stackP2 r ls)) as h3.
    assert (h4 : CfgSqReachesPlus
        (hL, SA 0 :: SA 1 :: stackP2 r ls, R_tail (2 * s) 1 2)
        (hL, stackP2 r ls, 2 :: 1 :: R_tail (2 * s) 1 2))
      by (exists 2; split; [lia | reflexivity]).
    pose proof (prefix_P2_pop r ls (2 :: 1 :: R_tail (2 * s) 1 2)) as h5.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans hp h2) h3) h4) h5).
  - unfold R_mid in hp |- *; cbn [Nat.eqb Nat.sub] in hp |- *.
    replace (2 * s + 1 - 1) with (2 * s) in hp |- * by lia.
    pose proof (sep_0 (2 * s) 1 0 eq_refl (or_introl eq_refl) (stackP2 r ls)) as h2.
    rewrite psiTilde_even in h2; cbn [fst snd] in h2.
    pose proof (prefix_P2_pop r ls (2 :: 1 :: R_tail (2 * s + 1) 1 0)) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans hp h2) h3).
Qed.

Lemma enc_odd_even_b_step1 (m r s d : nat) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_odd (2 * m + 1) (2 * r + 2) (2 * s + 1) d)
    (J_even m r (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d)).
Proof.
  apply bounce_from_A0A2.
  pose proof (enc_odd_ge2_mid m (2 * r) s d hd) as h1.
  pose proof (rmid_even_2 r s d hd (repeat (SB 2) m ++ [SA 2; SA 0; SA 2])) as h2.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL m [SA 0; SA 2]
      (3 :: (repeat 1 (2 * r) ++ (2 :: R_tail (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d))))) ltac:(lia)) as h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Lemma enc_odd_odd_b_step1 (m r s d : nat) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_odd (2 * m + 1) (2 * r + 3) (2 * s + 1) d)
    (J_odd m r (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d)).
Proof.
  apply bounce_from_A0A2.
  replace (2 * r + 3) with ((2 * r + 1) + 2) by lia.
  pose proof (enc_odd_ge2_mid m (2 * r + 1) s d hd) as h1.
  pose proof (rmid_odd_2 r s d hd (repeat (SB 2) m ++ [SA 2; SA 0; SA 2])) as h2.
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL m [SA 0; SA 2]
      (3 :: (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail (if d =? 0 then 2 * s else 2 * s + 1) 1 (2 - d))))) ltac:(lia)) as h3.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3).
Qed.

Lemma J_even_zero_to_M2 (r w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (J_even 0 r w z d) (M2_sq (2 * r + 2) (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  pose proof (double3_reduction (repeat 1 (2 * r) ++ (2 :: R_tail w z d))) as hb1.
  rewrite two_cons_repeat_even in hb1.
  pose proof (bounce_from_nil (sep_even_2 (r + 1) [] w z d hz hd)) as hb2.
  replace (2 * (r + 1)) with (2 * r + 2) in hb2 at 2 by lia.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma J_even_succ_to_J_odd (m r w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (J_even (m + 1) r w z d) (J_odd m r (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  apply bounce_from_A0A2.
  pose proof (prefix_P1_scan m [] (repeat 1 (2 * r) ++ (2 :: R_tail w z d))) as h1.
  pose proof (prefix_P2_scan_2 r (stackP1 m []) (R_tail w z d)) as h2.
  pose proof (sep_0 w z d hz hd (stackP2 r (stackP1 m []))) as h3.
  pose proof (prefix_P2_pop r (stackP1 m [])
    (2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)) as h4.
  pose proof (prefix_P1_pop m []
    (3 :: (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d)))) as h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5).
Qed.

Lemma J_odd_zero_to_M2 (r w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (J_odd 0 r w z d) (M2_sq (2 * r + 2) w (z + 2) d).
Proof.
  pose proof (double3_reduction (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail w z d))) as hb1.
  rewrite two_cons_repeat_even in hb1.
  pose proof (bounce_from_nil (sep_even_21 (r + 1) [] ltac:(left; lia) w z d hz hd)) as hb2.
  pose proof (M2_sq_odd_step (r + 1) (fst (psiTilde w z)) (snd (psiTilde w z)) d
    (psiTilde_snd_odd w z hz) hd) as hb3.
  rewrite psiTilde_psiTilde in hb3; cbn [fst snd] in hb3.
  replace (2 * (r + 1)) with (2 * r + 2) in hb3 at 2 by lia.
  exact (sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3).
Qed.

Lemma J_odd_succ_to_F (m r w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (J_odd (m + 1) r w z d) (F_sq (2 * m) (2 * r) 1 (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  apply bounce_from_A0A2.
  pose proof (prefix_P1_scan m [] (repeat 1 (2 * r) ++ (2 :: 1 :: R_tail w z d))) as h1.
  pose proof (prefix_P2_scan_2 r (stackP1 m []) (1 :: R_tail w z d)) as h2.
  pose proof (sep_even_01 0 (stackP2 r (stackP1 m [])) w z d hz hd) as h3.
  pose proof (prefix_P2_pop r (stackP1 m [])
    (3 :: [1] ++ (0 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))) as h4.
  pose proof (prefix_P1_pop m []
    (3 :: (repeat 1 (2 * r) ++ (3 :: [1] ++ (0 :: R_tail (fst (psiTilde w z)) (snd (psiTilde w z)) d))))) as h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5).
Qed.

Lemma phase1_b1_d0 (m s : nat) :
  SqReachesPlus (enc_odd (2 * m + 1) 1 (2 * s + 1) 0) (M2_sq 0 (2 * s) (2 * m + 3) 2).
Proof.
  pose proof (enc_odd_b1_step1 m s 0 (or_introl eq_refl)) as h1.
  unfold R_mid in h1; cbn [Nat.eqb] in h1.
  destruct m as [| m'].
  - assert (h2 : SqReachesPlus
        (3 :: (repeat 1 (2 * 0 + 1) ++ (0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))))
        (2 :: 1 :: R_tail (2 * s) 1 2)).
    { apply bounce_from_A0A2.
      assert (ha : CfgSqReachesPlus
          (h10B, [SA 1], 3 :: 1 :: 0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))
          (h10B, SA 1 :: [SA 0; SA 1; SA 0; SA 2], repeat 1 (2 * s + 1) ++ [3; 1]))
        by (exists 4; split; [lia | reflexivity]).
      pose proof (pass2_turnaround s [SA 0; SA 1; SA 0; SA 2]) as hb.
      assert (hc : CfgSqReachesPlus
          (hL, [SA 0; SA 1; SA 0; SA 2], R_tail (2 * s) 1 2)
          (hL, [SA 0; SA 2], 2 :: 1 :: R_tail (2 * s) 1 2))
        by (exists 2; split; [lia | reflexivity]).
      exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans ha hb) hc). }
    pose proof (sep_21_nil (2 * s) 1 2 eq_refl (or_intror eq_refl)) as h3.
    rewrite psiTilde_even in h3; cbn [fst snd] in h3.
    pose proof (bounce_from_nil (sep_even_2 0 [] (2 * s + 1) 1 2 eq_refl (or_intror eq_refl))) as h4.
    rewrite psiTilde_odd in h4; cbn [fst snd] in h4.
    exact (sqReachesPlus_trans (sqReachesPlus_trans (sqReachesPlus_trans h1 h2) h3) h4).
  - replace (S m') with (m' + 1) in h1 |- * by lia.
    assert (h2 : SqReachesPlus
        (3 :: (repeat 1 (2 * (m' + 1) + 1) ++ (0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))))
        (3 :: (repeat 1 (2 * m' + 1) ++ (0 :: 1 :: R_tail (2 * s) 1 2)))).
    { apply bounce_from_A0A2.
      pose proof (prefix_odd_3 (m' + 1) (0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))) as ha.
      pose proof (cfgSqReachesStar_of_iterOpt
        (scan_ones_h10B_any (m' + 1) [SA 0; SA 2] (0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1])))) as hb.
      assert (hc : CfgSqReachesPlus
          (h10B, stackAfterOnes (m' + 1) [SA 0; SA 2], 0 :: 3 :: (repeat 1 (2 * s + 1) ++ [3; 1]))
          (h10B, SA 1 :: SA 0 :: SB 1 :: (repeat (SB 2) m' ++ [SA 2; SA 0; SA 2]),
            repeat 1 (2 * s + 1) ++ [3; 1])).
      { exists 2. split; [lia | replace (m' + 1) with (S m') by lia; reflexivity]. }
      pose proof (pass2_turnaround s (SA 0 :: SB 1 :: (repeat (SB 2) m' ++ [SA 2; SA 0; SA 2]))) as hd'.
      assert (he : CfgSqReachesPlus
          (hL, SA 0 :: SB 1 :: (repeat (SB 2) m' ++ [SA 2; SA 0; SA 2]), R_tail (2 * s) 1 2)
          (hL, SB 1 :: (repeat (SB 2) m' ++ [SA 2; SA 0; SA 2]), 1 :: R_tail (2 * s) 1 2))
        by (exists 1; split; [lia | reflexivity]).
      pose proof (cfgSqReachesPlus_of_iterOpt
        (pop_B1_B2_A2_hL m' [SA 0; SA 2] (1 :: R_tail (2 * s) 1 2)) ltac:(lia)) as hf.
      exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans ha (cfgSqReachesStar_plus_trans hb hc)) hd') he) hf). }
    assert (h3 : SqReachesPlus
        (3 :: (repeat 1 (2 * m' + 1) ++ (0 :: 1 :: R_tail (2 * s) 1 2)))
        (H_sq (2 * m' + 1) (2 * s + 1) 1 2)).
    { apply bounce_from_A0A2.
      pose proof (prefix_odd_3 m' (0 :: 1 :: R_tail (2 * s) 1 2)) as ha.
      pose proof (sep_even_01 m' [SA 0; SA 2] (2 * s) 1 2 eq_refl (or_intror eq_refl)) as hb.
      rewrite psiTilde_even in hb; cbn [fst snd] in hb.
      exact (cfgSqReachesPlus_trans ha hb). }
    pose proof (H_drain m' (2 * s + 1) 1 2 eq_refl (or_intror eq_refl)) as h4.
    rewrite psiTilde_odd in h4; cbn [fst snd] in h4.
    replace (1 + 2 + 2 * m' + 2) with (2 * (m' + 1) + 3) in h4 by lia.
    exact (sqReachesPlus_trans (sqReachesPlus_trans (sqReachesPlus_trans h1 h2) h3) h4).
Qed.

Record OddState : Type := mkOdd {
  oa : nat;
  ob : nat;
  oc : nat;
  od : nat
}.

Definition InSodd (s : OddState) : Prop :=
  oa s mod 2 = 1 /\ ob s >= 1 /\ oc s >= 3 /\ oc s mod 2 = 1 /\ (od s = 0 \/ od s = 2).

Lemma phase1_to_M2 (s : OddState) (hs : InSodd s) :
  SqReachesPlus
    (enc_odd (oa s) (ob s) (oc s) (od s))
    (M2_sq (2 * (ob s / 2))
      (if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
       then oc s else oc s - 1)
      (if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2)
      (2 - od s)).
Proof.
  destruct hs as [ha_odd [hb_ge1 [hc_ge3 [hc_odd hd]]]].
  pose proof (div_mod_2 (oa s)) as Ha_dm.
  pose proof (div_mod_2 (ob s)) as Hb_dm.
  pose proof (div_mod_2 (oc s)) as Hc_dm.
  set (m := oa s / 2).
  set (sc := oc s / 2).
  assert (ha_eq : oa s = 2 * m + 1) by (unfold m; lia).
  assert (hc_eq : oc s = 2 * sc + 1) by (unfold sc; lia).
  clearbody m sc. clear Ha_dm Hc_dm.
  destruct (proj2 Hb_dm) as [heb | heb].
  - (* ob s even >= 2 *)
    set (r := ob s / 2 - 1).
    assert (hb_eq : ob s = 2 * r + 2) by (unfold r; lia).
    assert (hq : 2 * (ob s / 2) = 2 * r + 2) by (unfold r; lia).
    clearbody r.
    set (w1 := if od s =? 0 then 2 * sc else 2 * sc + 1).
    set (dp := 2 - od s).
    assert (hdp : dp = 0 \/ dp = 2) by (unfold dp; lia).
    assert (hstep1 : SqReachesPlus (enc_odd (oa s) (ob s) (oc s) (od s)) (J_even m r w1 1 dp)).
    { rewrite ha_eq, hb_eq, hc_eq.
      exact (enc_odd_even_b_step1 m r sc (od s) hd). }
    assert (hpsi1 : psiTilde w1 1 =
        (if od s =? 0 then 2 * sc + 1 else 2 * sc, if od s =? 0 then 1 else 3)).
    { unfold w1. destruct (od s =? 0); [exact (psiTilde_even sc 1) | exact (psiTilde_odd sc 1)]. }
    assert (hJ : SqReachesPlus (J_even m r w1 1 dp)
        (M2_sq (2 * r + 2) (fst (psiTilde w1 1)) (snd (psiTilde w1 1) + 2 * m) dp)).
    { destruct m as [| [| m2]].
      - replace (snd (psiTilde w1 1) + 2 * 0) with (snd (psiTilde w1 1)) by lia.
        exact (J_even_zero_to_M2 r w1 1 dp eq_refl hdp).
      - pose proof (J_even_succ_to_J_odd 0 r w1 1 dp eq_refl hdp) as hj1.
        pose proof (J_odd_zero_to_M2 r (fst (psiTilde w1 1)) (snd (psiTilde w1 1)) dp
          (psiTilde_snd_odd w1 1 eq_refl) hdp) as hj2.
        replace (snd (psiTilde w1 1) + 2 * 1) with (snd (psiTilde w1 1) + 2) by lia.
        exact (sqReachesPlus_trans hj1 hj2).
      - replace (S (S m2)) with ((m2 + 1) + 1) by lia.
        pose proof (J_even_succ_to_J_odd (m2 + 1) r w1 1 dp eq_refl hdp) as hj1.
        pose proof (J_odd_succ_to_F m2 r (fst (psiTilde w1 1)) (snd (psiTilde w1 1)) dp
          (psiTilde_snd_odd w1 1 eq_refl) hdp) as hj2.
        rewrite psiTilde_psiTilde in hj2; cbn [fst snd] in hj2.
        pose proof (F_universal_drain m2 r 0 w1 3 dp eq_refl hdp) as hj3.
        assert (hpsi3 : psiTilde w1 3 = (fst (psiTilde w1 1), snd (psiTilde w1 1) + 2)).
        { replace 3 with (1 + 2) by lia. rewrite psiTilde_add_two, psiShift_eq_psiTilde_step. reflexivity. }
        rewrite hpsi3 in hj3; cbn [fst snd] in hj3.
        replace (snd (psiTilde w1 1) + 2 + 2 * (m2 + 0 + 1)) with
          (snd (psiTilde w1 1) + 2 * ((m2 + 1) + 1)) in hj3 by lia.
        exact (sqReachesPlus_trans (sqReachesPlus_trans hj1 hj2) hj3). }
    pose proof (sqReachesPlus_trans hstep1 hJ) as htot.
    rewrite hpsi1, <- hq in htot; cbn [fst snd] in htot.
    clear hstep1 hJ hpsi1 w1.
    assert (hw_eq : (if od s =? 0 then 2 * sc + 1 else 2 * sc) =
        (if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
         then oc s else oc s - 1)) by (split_ifs; lia).
    assert (hz_eq : (if od s =? 0 then 1 else 3) + 2 * m =
        (if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2)) by (split_ifs; lia).
    rewrite <- hw_eq, <- hz_eq.
    exact htot.
  - (* ob s odd >= 1 *)
    assert (hb_cases : ob s = 1 \/ ob s >= 3) by lia.
    destruct hb_cases as [hb1 | hb3].
    + destruct hd as [hd0 | hd2].
      * assert (hq0 : 2 * (ob s / 2) = 0) by lia.
        assert (hw0 : (if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
            then oc s else oc s - 1) = 2 * sc) by (split_ifs; lia).
        assert (hz0 : (if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2) = 2 * m + 3)
          by (split_ifs; lia).
        assert (hd0' : 2 - od s = 2) by lia.
        rewrite hq0, hw0, hz0, hd0', ha_eq, hb1, hc_eq, hd0.
        exact (phase1_b1_d0 m sc).
      * pose proof (enc_odd_b1_step1 m sc 2 (or_intror eq_refl)) as h1.
        unfold R_mid in h1; cbn [Nat.eqb] in h1.
        replace (2 * sc + 1 - 1) with (2 * sc) in h1 by lia.
        pose proof (H_drain m (2 * sc) 1 0 eq_refl (or_introl eq_refl)) as h2.
        rewrite psiTilde_even in h2; cbn [fst snd] in h2.
        pose proof (sqReachesPlus_trans h1 h2) as htot.
        assert (hq0 : 2 * (ob s / 2) = 0) by lia.
        assert (hw0 : (if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
            then oc s else oc s - 1) = 2 * sc + 1) by (split_ifs; lia).
        assert (hz0 : (if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2) = 1 + 2 * m + 2)
          by (split_ifs; lia).
        assert (hd2' : 2 - od s = 0) by lia.
        rewrite hq0, hw0, hz0, hd2', ha_eq, hb1, hc_eq, hd2.
        exact htot.
    + set (r := ob s / 2 - 1).
      assert (hb_eq : ob s = 2 * r + 3) by (unfold r; lia).
      assert (hq : 2 * (ob s / 2) = 2 * r + 2) by (unfold r; lia).
      clearbody r.
      set (w1 := if od s =? 0 then 2 * sc else 2 * sc + 1).
      set (dp := 2 - od s).
      assert (hdp : dp = 0 \/ dp = 2) by (unfold dp; lia).
      assert (hstep1 : SqReachesPlus (enc_odd (oa s) (ob s) (oc s) (od s)) (J_odd m r w1 1 dp)).
      { rewrite ha_eq, hb_eq, hc_eq.
        exact (enc_odd_odd_b_step1 m r sc (od s) hd). }
      assert (hJ : SqReachesPlus (J_odd m r w1 1 dp) (M2_sq (2 * r + 2) w1 (2 * m + 3) dp)).
      { destruct m as [| m1].
        - replace (2 * 0 + 3) with (1 + 2) by lia.
          exact (J_odd_zero_to_M2 r w1 1 dp eq_refl hdp).
        - replace (S m1) with (m1 + 1) by lia.
          pose proof (J_odd_succ_to_F m1 r w1 1 dp eq_refl hdp) as hj1.
          pose proof (F_universal_drain m1 r 0 (fst (psiTilde w1 1)) (snd (psiTilde w1 1)) dp
            (psiTilde_snd_odd w1 1 eq_refl) hdp) as hj2.
          rewrite psiTilde_psiTilde in hj2; cbn [fst snd] in hj2.
          replace (1 + 2 + 2 * (m1 + 0 + 1)) with (2 * (m1 + 1) + 3) in hj2 by lia.
          exact (sqReachesPlus_trans hj1 hj2). }
      pose proof (sqReachesPlus_trans hstep1 hJ) as htot.
      rewrite <- hq in htot.
      clear hstep1 hJ.
      assert (hw_eq : w1 =
          (if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
           then oc s else oc s - 1)) by (unfold w1; split_ifs; lia).
      assert (hz_eq : 2 * m + 3 =
          (if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2)) by (split_ifs; lia).
      rewrite <- hw_eq, <- hz_eq.
      exact htot.
Qed.

(* Phase 2: M2_sq (2 * (k - 1)) w Z d -> enc_odd / enc_even *)

Lemma M2_ge4_to_G (m w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (M2_sq (2 * m + 4) w z0 d) (G_sq (2 * m) 1 w (z0 + 2) d).
Proof.
  set (wt := fst (psiTilde w z0)).
  set (zt := snd (psiTilde w z0)).
  assert (hb1 : SqReachesPlus (M2_sq (2 * m + 4) w z0 d)
      (3 :: (repeat 1 (2 * m + 2) ++ (2 :: 1 :: R_tail wt zt d)))).
  { apply bounce_from_A0A2.
    unfold M2_sq. replace (2 * m + 4) with (2 * (m + 1 + 1)) by lia.
    pose proof (prefix_M2_scan (m + 1) [] (R_tail w z0 d)) as h1.
    pose proof (sep_0 w z0 d hz0 hd (stackP1 (m + 1) [])) as h2.
    fold wt zt in h2.
    pose proof (prefix_P1_pop (m + 1) [] (2 :: 1 :: R_tail wt zt d)) as h3.
    replace (2 * (m + 1)) with (2 * m + 2) in h3 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  assert (hb2 : SqReachesPlus
      (3 :: (repeat 1 (2 * m + 2) ++ (2 :: 1 :: R_tail wt zt d)))
      (G_sq (2 * m) 1 w (z0 + 2) d)).
  { apply bounce_from_A0A2.
    replace (2 * m + 2) with (2 * (m + 1)) by lia.
    pose proof (prefix_M2_scan m [] (1 :: R_tail wt zt d)) as h1.
    pose proof (sep_even_01 0 (stackP1 m []) wt zt d (psiTilde_snd_odd w z0 hz0) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    pose proof (prefix_P1_pop m [] (3 :: [1] ++ (0 :: R_tail w (z0 + 2) d))) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma loop_L1G (v j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq (2 * v + 4) (2 * j + 1) w z d)
    (G_sq (2 * v) (2 * j + 3) w (z + 2) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus
      (G_sq (2 * v + 4) (2 * j + 1) w z d)
      (3 :: (repeat 1 (2 * v + 2) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))).
  { apply bounce_from_A0A2.
    unfold G_sq. replace (2 * v + 4) with (2 * (v + 1 + 1)) by lia.
    pose proof (prefix_P1_scan (v + 1) [] (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))) as h1.
    rewrite (cons_repeat_odd_append j 1 (0 :: R_tail w z d)) in h1.
    pose proof (sep_even_0 j (stackP1 (v + 1) []) w z d hz hd) as h2.
    fold wt zt in h2.
    pose proof (prefix_P1_pop (v + 1) [] (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h3.
    replace (2 * (v + 1)) with (2 * v + 2) in h3 by lia.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  assert (hb2 : SqReachesPlus
      (3 :: (repeat 1 (2 * v + 2) ++ (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v) (2 * j + 3) w (z + 2) d)).
  { apply bounce_from_A0A2.
    replace (2 * v + 2) with (2 * (v + 1)) by lia.
    pose proof (prefix_P1_scan v [] (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d))) as h1.
    rewrite (cons_repeat_odd_append j 1 (0 :: 1 :: R_tail wt zt d)) in h1.
    pose proof (sep_even_01 (j + 1) (stackP1 v []) wt zt d (psiTilde_snd_odd w z hz) hd) as h2.
    unfold wt, zt in h2; rewrite psiTilde_psiTilde in h2; cbn [fst snd] in h2.
    replace (2 * (j + 1) + 1) with (2 * j + 3) in h2 by lia.
    pose proof (prefix_P1_pop v [] (3 :: (repeat 1 (2 * j + 3) ++ (0 :: R_tail w (z + 2) d)))) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma G_even_0_exit (j w z d : nat) :
  SqReachesPlus (G_sq 0 (2 * j + 1) w z d) (enc_odd (2 * j + 3) (w + 1) z d).
Proof.
  pose proof (double3_reduction (repeat 1 (2 * j + 1) ++ (0 :: 3 :: TailWord w z d))) as hb1.
  assert (heq1 : 1 :: 1 :: (repeat 1 (2 * j + 1) ++ (0 :: 3 :: TailWord w z d)) =
      repeat 1 (2 * (j + 1) + 1) ++ (0 :: 3 :: TailWord w z d)).
  { replace (2 * (j + 1) + 1) with (S (S (2 * j + 1))) by lia. reflexivity. }
  rewrite heq1 in hb1.
  pose proof (exit_odd_0_3 (j + 1) (TailWord w z d)) as hb2.
  replace (2 * (j + 1) + 1) with (2 * j + 3) in hb1, hb2 by lia.
  assert (heq2 : 3 :: (repeat 1 (2 * j + 3) ++ (0 :: 1 :: TailWord w z d)) =
      enc_odd (2 * j + 3) (w + 1) z d).
  { unfold enc_odd, TailWord. rewrite (repeat_succ w 1). reflexivity. }
  rewrite heq2 in hb2.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma G_even_2_exit (j w z d : nat) (hz : z mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq 2 (2 * j + 1) w z d)
    (enc_even (2 * j + 4) (fst (psiTilde w z)) (snd (psiTilde w z)) d).
Proof.
  set (wt := fst (psiTilde w z)).
  set (zt := snd (psiTilde w z)).
  assert (hb1 : SqReachesPlus (G_sq 2 (2 * j + 1) w z d)
      (3 :: 3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))).
  { apply bounce_from_A0A2.
    pose proof (prefix_P1_scan 0 [] (repeat 1 (2 * j + 1) ++ (0 :: R_tail w z d))) as h1.
    rewrite (cons_repeat_odd_append j 1 (0 :: R_tail w z d)) in h1.
    pose proof (sep_even_0 j (stackP1 0 []) w z d hz hd) as h2.
    fold wt zt in h2.
    pose proof (prefix_P1_pop 0 [] (3 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)))) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  pose proof (double3_reduction (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d))) as hb2.
  assert (heq : 1 :: 1 :: (repeat 1 (2 * j + 1) ++ (0 :: 1 :: R_tail wt zt d)) =
      enc_even (2 * j + 4) wt zt d).
  { unfold enc_even. replace (2 * j + 4 - 1) with (S (S (2 * j + 1))) by lia. reflexivity. }
  rewrite heq in hb2.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma M2_0_exit (w z0 d : nat) :
  SqReachesPlus (M2_sq 0 w z0 d) (enc_odd 1 (w + 1) z0 d).
Proof.
  pose proof (exit_3_2 (3 :: TailWord w z0 d)) as hb1.
  pose proof (exit_odd_0_3 0 (TailWord w z0 d)) as hb2.
  assert (heq : 3 :: (repeat 1 (2 * 0 + 1) ++ (0 :: 1 :: TailWord w z0 d)) =
      enc_odd 1 (w + 1) z0 d).
  { unfold enc_odd, TailWord. rewrite (repeat_succ w 1). reflexivity. }
  rewrite heq in hb2.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma M2_2_exit (w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (M2_sq 2 w z0 d) (enc_even 2 (fst (psiTilde w z0)) (snd (psiTilde w z0)) d).
Proof.
  set (wt := fst (psiTilde w z0)).
  set (zt := snd (psiTilde w z0)).
  assert (hb1 : SqReachesPlus (M2_sq 2 w z0 d) (3 :: 2 :: 1 :: R_tail wt zt d)).
  { apply bounce_from_A0A2.
    pose proof (prefix_M2_scan 0 [] (R_tail w z0 d)) as h1.
    pose proof (sep_0 w z0 d hz0 hd (stackP1 0 [])) as h2.
    fold wt zt in h2.
    pose proof (prefix_P1_pop 0 [] (2 :: 1 :: R_tail wt zt d)) as h3.
    exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3). }
  pose proof (exit_3_2 (1 :: R_tail wt zt d)) as hb2.
  exact (sqReachesPlus_trans hb1 hb2).
Qed.

Lemma G_even_drain_0 (r j w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (G_sq (4 * r) (2 * j + 1) w z0 d) (enc_odd (2 * (j + r) + 3) (w + 1) (z0 + 2 * r) d).
Proof.
  revert j z0 hz0.
  induction r as [| r ih]; intros j z0 hz0.
  - replace (j + 0) with j by lia.
    replace (z0 + 2 * 0) with z0 by lia.
    exact (G_even_0_exit j w z0 d).
  - pose proof (loop_L1G (2 * r) j w z0 d hz0 hd) as h1.
    replace (2 * (2 * r) + 4) with (4 * S r) in h1 by lia.
    replace (2 * (2 * r)) with (4 * r) in h1 by lia.
    pose proof (ih (j + 1) (z0 + 2) ltac:(rewrite add_two_mod2; exact hz0)) as h2.
    replace (2 * (j + 1) + 1) with (2 * j + 3) in h2 by lia.
    replace (2 * (j + 1 + r) + 3) with (2 * (j + S r) + 3) in h2 by lia.
    replace (z0 + 2 + 2 * r) with (z0 + 2 * S r) in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

Lemma G_even_drain_2 (r j w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (G_sq (4 * r + 2) (2 * j + 1) w z0 d)
    (enc_even (2 * (j + r) + 4) (fst (psiTilde w z0)) (snd (psiTilde w z0) + 2 * r) d).
Proof.
  revert j z0 hz0.
  induction r as [| r ih]; intros j z0 hz0.
  - replace (j + 0) with j by lia.
    replace (snd (psiTilde w z0) + 2 * 0) with (snd (psiTilde w z0)) by lia.
    exact (G_even_2_exit j w z0 d hz0 hd).
  - pose proof (loop_L1G (2 * r + 1) j w z0 d hz0 hd) as h1.
    replace (2 * (2 * r + 1) + 4) with (4 * S r + 2) in h1 by lia.
    replace (2 * (2 * r + 1)) with (4 * r + 2) in h1 by lia.
    pose proof (ih (j + 1) (z0 + 2) ltac:(rewrite add_two_mod2; exact hz0)) as h2.
    rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
    cbn [fst snd] in h2.
    replace (2 * (j + 1) + 1) with (2 * j + 3) in h2 by lia.
    replace (2 * (j + 1 + r) + 4) with (2 * (j + S r) + 4) in h2 by lia.
    replace (snd (psiTilde w z0) + 2 + 2 * r) with (snd (psiTilde w z0) + 2 * S r) in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

Lemma phase2_odd (r w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus (M2_sq (4 * r) w z0 d) (enc_odd (2 * r + 1) (w + 1) (z0 + 2 * r) d).
Proof.
  destruct r as [| r'].
  - replace (z0 + 2 * 0) with z0 by lia.
    exact (M2_0_exit w z0 d).
  - pose proof (M2_ge4_to_G (2 * r') w z0 d hz0 hd) as h1.
    replace (2 * (2 * r') + 4) with (4 * S r') in h1 by lia.
    replace (2 * (2 * r')) with (4 * r') in h1 by lia.
    pose proof (G_even_drain_0 r' 0 w (z0 + 2) d ltac:(rewrite add_two_mod2; exact hz0) hd) as h2.
    replace (2 * (0 + r') + 3) with (2 * S r' + 1) in h2 by lia.
    replace (z0 + 2 + 2 * r') with (z0 + 2 * S r') in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

Lemma phase2_even (r w z0 d : nat) (hz0 : z0 mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (M2_sq (4 * r + 2) w z0 d)
    (enc_even (2 * r + 2) (fst (psiTilde w z0)) (snd (psiTilde w z0) + 2 * r) d).
Proof.
  destruct r as [| r'].
  - replace (snd (psiTilde w z0) + 2 * 0) with (snd (psiTilde w z0)) by lia.
    exact (M2_2_exit w z0 d hz0 hd).
  - pose proof (M2_ge4_to_G (2 * r' + 1) w z0 d hz0 hd) as h1.
    replace (2 * (2 * r' + 1) + 4) with (4 * S r' + 2) in h1 by lia.
    replace (2 * (2 * r' + 1)) with (4 * r' + 2) in h1 by lia.
    pose proof (G_even_drain_2 r' 0 w (z0 + 2) d ltac:(rewrite add_two_mod2; exact hz0) hd) as h2.
    rewrite psiTilde_add_two, psiShift_eq_psiTilde_step in h2.
    cbn [fst snd] in h2.
    replace (2 * (0 + r') + 4) with (2 * S r' + 2) in h2 by lia.
    replace (snd (psiTilde w z0) + 2 + 2 * r') with (snd (psiTilde w z0) + 2 * S r') in h2 by lia.
    exact (sqReachesPlus_trans h1 h2).
Qed.

(* Even Halving Cascade *)

Lemma enc_even_step1 (k' b0 c0_v d : nat) (hb0 : b0 >= 1) (hc0 : c0_v mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_even (2 * (k' + 1)) b0 c0_v d)
    (M_sq (2 * k' + 1) (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v)) d).
Proof.
  apply bounce_from_nil.
  assert (hrt : R_tail b0 c0_v d = 3 :: 1 :: TailWord (b0 - 1) c0_v d).
  { unfold R_tail, TailWord.
    replace b0 with ((b0 - 1) + 1) at 1 by lia.
    rewrite (repeat_succ (b0 - 1) 1). reflexivity. }
  assert (heq : enc_even (2 * (k' + 1)) b0 c0_v d =
      repeat 1 (2 * k') ++ (1 :: 0 :: 1 :: 3 :: 1 :: TailWord (b0 - 1) c0_v d)).
  { unfold enc_even. rewrite hrt.
    replace (2 * (k' + 1) - 1) with (2 * k' + 1) by lia.
    apply repeat_succ_append. }
  rewrite heq.
  pose proof (cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any k' [] (1 :: 0 :: 1 :: 3 :: 1 :: TailWord (b0 - 1) c0_v d))) as h1.
  assert (h2 : CfgSqReachesPlus
      (h10B, stackAfterOnes k' [], 1 :: 0 :: 1 :: 3 :: 1 :: TailWord (b0 - 1) c0_v d)
      (h10B, SA 1 :: SA 0 :: SB 3 :: (repeat (SB 2) k' ++ [SA 2]), TailWord (b0 - 1) c0_v d)).
  { exists 5. split; [lia | destruct k'; reflexivity]. }
  pose proof (tail_reflect (b0 - 1) c0_v d hc0 hd
    (SA 0 :: SB 3 :: (repeat (SB 2) k' ++ [SA 2])) ltac:(discriminate)) as h3.
  assert (h4 : CfgSqReachesPlus
      (hL, SA 0 :: SB 3 :: (repeat (SB 2) k' ++ [SA 2]),
        R_tail (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v)) d)
      (hL, repeat (SB 2) k' ++ [SA 2],
        1 :: 2 :: 1 :: R_tail (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v)) d))
    by (exists 2; split; [lia | reflexivity]).
  pose proof (cfgSqReachesPlus_of_iterOpt
    (pop_B2_A2_hL k' [] (1 :: 2 :: 1 :: R_tail (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v)) d))
    ltac:(lia)) as h5.
  rewrite (repeat_append_cons_same (2 * k')) in h5.
  exact (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5).
Qed.

Lemma enc_even_to_M2 (k' b0 c0_v d : nat) (hb0 : b0 >= 1) (hc0 : c0_v mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_even (2 * (k' + 1)) b0 c0_v d)
    (M2_sq (2 * k') (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v) + 2) d).
Proof.
  exact (sqReachesPlus_trans
    (enc_even_step1 k' b0 c0_v d hb0 hc0 hd)
    (M_sq_odd_to_M2 k' (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v)) d
      (psiTilde_snd_odd (b0 - 1) c0_v hc0) hd)).
Qed.

Lemma step_even_halve (r b0 c0_v d : nat) (hb0 : b0 >= 1) (hc0 : c0_v mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_even (2 * (2 * r + 2)) b0 c0_v d)
    (enc_even (2 * r + 2) (b0 - 1) (c0_v + (2 * r + 2) + 2) d).
Proof.
  pose proof (enc_even_to_M2 (2 * r + 1) b0 c0_v d hb0 hc0 hd) as h1.
  replace (2 * (2 * r + 1 + 1)) with (2 * (2 * r + 2)) in h1 by lia.
  replace (2 * (2 * r + 1)) with (4 * r + 2) in h1 by lia.
  pose proof (psiTilde_snd_odd (b0 - 1) c0_v hc0) as hsnd.
  pose proof (phase2_even r (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v) + 2) d
    ltac:(rewrite add_two_mod2; exact hsnd) hd) as h2.
  assert (hpsi : psiTilde (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v) + 2) =
      (b0 - 1, c0_v + 4)).
  { rewrite psiTilde_add_two.
    pose proof (psiShift_psiTilde_add (b0 - 1) c0_v 0) as hp.
    replace (snd (psiTilde (b0 - 1) c0_v) + 2 * 0) with (snd (psiTilde (b0 - 1) c0_v)) in hp by lia.
    replace (c0_v + 2 * 0 + 4) with (c0_v + 4) in hp by lia.
    exact hp. }
  rewrite hpsi in h2; cbn [fst snd] in h2.
  replace (c0_v + 4 + 2 * r) with (c0_v + (2 * r + 2) + 2) in h2 by lia.
  exact (sqReachesPlus_trans h1 h2).
Qed.

Lemma step_even_exit (r b0 c0_v d : nat) (hb0 : b0 >= 1) (hc0 : c0_v mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesPlus
    (enc_even (2 * (2 * r + 1)) b0 c0_v d)
    (enc_odd (2 * r + 1) (fst (psiTilde (b0 - 1) c0_v) + 1) (snd (psiTilde (b0 - 1) c0_v) + 2 + 2 * r) d).
Proof.
  pose proof (enc_even_to_M2 (2 * r) b0 c0_v d hb0 hc0 hd) as h1.
  replace (2 * (2 * r)) with (4 * r) in h1 by lia.
  pose proof (psiTilde_snd_odd (b0 - 1) c0_v hc0) as hsnd.
  exact (sqReachesPlus_trans h1
    (phase2_odd r (fst (psiTilde (b0 - 1) c0_v)) (snd (psiTilde (b0 - 1) c0_v) + 2) d
      ltac:(rewrite add_two_mod2; exact hsnd) hd)).
Qed.

Lemma even_cascade (t a' b0 c0_v d : nat) (ha' : a' mod 2 = 1) (hb0 : b0 >= t)
    (hc0 : c0_v mod 2 = 1) (hd : d = 0 \/ d = 2) :
  SqReachesStar
    (enc_even (2 ^ (t + 1) * a') b0 c0_v d)
    (enc_even (2 * a') (b0 - t) (c0_v + (2 ^ (t + 1) - 2) * a' + 2 * t) d).
Proof.
  revert b0 c0_v hb0 hc0.
  induction t as [| t ih]; intros b0 c0_v hb0 hc0.
  - cbn [Nat.add Nat.pow].
    replace (b0 - 0) with b0 by lia.
    replace (2 * 1 * a') with (2 * a') by lia.
    replace (c0_v + (2 * 1 - 2) * a' + 2 * 0) with c0_v by lia.
    exact (sqReachesStar_refl (enc_even (2 * a') b0 c0_v d)).
  - pose proof (mul_pos_of_pos_of_odd (one_le_pow2 t) ha') as hta1.
    assert (hpow2 : 2 ^ (t + 1) = 2 * 2 ^ t) by (replace (t + 1) with (S t) by lia; reflexivity).
    set (r := 2 ^ t * a' - 1).
    assert (hr_eq : 2 ^ (t + 1) * a' = 2 * r + 2) by (unfold r; rewrite hpow2; lia).
    clearbody r.
    assert (hhead : 2 * (2 ^ (t + 1) * a') = 2 ^ (S t + 1) * a').
    { replace (S t + 1) with (S (t + 1)) by lia. cbn [Nat.pow]. lia. }
    pose proof (sqReachesStar_of_plus (step_even_halve r b0 c0_v d ltac:(lia) hc0 hd)) as h1.
    rewrite <- hr_eq, hhead in h1.
    assert (hc_next_odd : (c0_v + 2 ^ (t + 1) * a' + 2) mod 2 = 1).
    { replace (c0_v + 2 ^ (t + 1) * a' + 2) with (c0_v + 2 * (r + 2)) by lia.
      rewrite add_even_mod2. exact hc0. }
    pose proof (ih (b0 - 1) (c0_v + 2 ^ (t + 1) * a' + 2) ltac:(lia) hc_next_odd) as h2.
    replace (b0 - 1 - t) with (b0 - S t) in h2 by lia.
    assert (hsum : c0_v + 2 ^ (t + 1) * a' + 2 + (2 ^ (t + 1) - 2) * a' + 2 * t =
        c0_v + (2 ^ (S t + 1) - 2) * a' + 2 * S t).
    { assert (hp11 : 2 ^ (S t + 1) = 2 * 2 ^ (t + 1))
        by (replace (S t + 1) with (S (t + 1)) by lia; reflexivity).
      clear h1 h2 hr_eq hhead hc_next_odd ha' hc0 hd.
      pose proof (one_le_pow2 t) as hp1.
      assert (hp2_ge2 : 2 ^ (t + 1) >= 2) by lia.
      clear hpow2 hp1 hta1.
      nia. }
    rewrite hsum in h2.
    exact (sqReachesStar_trans h1 h2).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ========================================================================== *)
(* Section 5A: Exact Odd-Return Map R_odd & Structural Step Bounds            *)
(* ========================================================================== *)

Lemma some_inj {X : Type} {x y : X} (h : Some x = Some y) : x = y.
Proof. inversion h; reflexivity. Qed.

Lemma oa_mk (a b c d : nat) : oa (mkOdd a b c d) = a. Proof. reflexivity. Qed.
Lemma ob_mk (a b c d : nat) : ob (mkOdd a b c d) = b. Proof. reflexivity. Qed.
Lemma oc_mk (a b c d : nat) : oc (mkOdd a b c d) = c. Proof. reflexivity. Qed.
Lemma od_mk (a b c d : nat) : od (mkOdd a b c d) = d. Proof. reflexivity. Qed.

Lemma div_mod_2_le (n : nat) :
  n = 2 * (n / 2) + n mod 2 /\ n mod 2 <= 1.
Proof.
  destruct (div_mod_2 n); lia.
Qed.

Lemma div_mod_2_4_le (b : nat) :
  b = 2 * (b / 2) + b mod 2 /\ b mod 2 <= 1 /\
  b = 4 * (b / 4) + b mod 4 /\ b mod 4 <= 3.
Proof.
  destruct (div_mod_2 b) as [hb2 hm2].
  destruct (div_mod_4 b) as [hb4 hm4].
  lia.
Qed.

Lemma pow2_add1 (n : nat) : 2 ^ (n + 1) = 2 * 2 ^ n.
Proof.
  replace (n + 1) with (S n) by lia. reflexivity.
Qed.

Lemma pow2_mono (a b : nat) (hab : a <= b) : 2 ^ a <= 2 ^ b.
Proof.
  induction hab as [| b hab ih]; [lia | cbn [Nat.pow]; lia].
Qed.

Lemma psiTilde_odd_val (c z : nat) (hc : c mod 2 = 1) :
  psiTilde c z = (c - 1, z + 2).
Proof.
  unfold psiTilde. rewrite hc. reflexivity.
Qed.

Lemma psiTilde_pred_odd (c z : nat) (hc3 : c >= 3) (hc : c mod 2 = 1) :
  psiTilde (c - 1) z = (c, z).
Proof.
  pose proof (div_mod_2_le c) as Hc.
  replace (c - 1) with (2 * (c / 2)) by lia.
  rewrite psiTilde_even. f_equal; lia.
Qed.

Lemma splitTwoAux_spec (fuel m : nat) (hm : m >= 1) (hfuel : m <= fuel) :
  2 ^ fst (splitTwoAux fuel m) * snd (splitTwoAux fuel m) = m /\
  snd (splitTwoAux fuel m) mod 2 = 1.
Proof.
  revert m hm hfuel.
  induction fuel as [| fuel ih]; intros m hm hfuel; [lia |].
  cbn [splitTwoAux].
  pose proof (div_mod_2_le m) as Hm.
  destruct (m mod 2 =? 0) eqn:Em.
  - destruct (ih (m / 2) ltac:(lia) ltac:(lia)) as [heq hodd].
    cbn [fst snd]. split; [| exact hodd].
    rewrite pow2_add1, <- Nat.mul_assoc, heq. lia.
  - cbn [fst snd Nat.pow]. lia.
Qed.

Lemma splitTwo_spec (m : nat) (hm : m >= 1) :
  2 ^ fst (splitTwo m) * snd (splitTwo m) = m /\ snd (splitTwo m) mod 2 = 1.
Proof.
  exact (splitTwoAux_spec m m hm (Nat.le_refl m)).
Qed.

Definition InSdom (s : OddState) : Prop :=
  InSodd s /\ oc s >= oa s.

Definition bInSdom (s : OddState) : bool :=
  ((oa s mod 2 =? 1) && (1 <=? ob s) && (3 <=? oc s) && (oc s mod 2 =? 1) &&
   ((od s =? 0) || (od s =? 2)) && (oa s <=? oc s))%bool.

Lemma bInSdom_iff (s : OddState) : bInSdom s = true <-> InSdom s.
Proof.
  unfold bInSdom, InSdom, InSodd. lia.
Qed.

Definition sigma_true (b d : nat) : nat :=
  if b mod 4 =? 1 then 0
  else if b mod 4 =? 0 then (if d =? 0 then 1 else 0)
  else if b mod 4 =? 2 then (if d =? 0 then 1 else 0)
  else (if d =? 2 then 1 else 0).

Lemma sigma_true_le_one (b d : nat) : sigma_true b d <= 1.
Proof.
  unfold sigma_true.
  destruct (b mod 4 =? 1), (d =? 0), (b mod 4 =? 0), (d =? 2), (b mod 4 =? 2), (b mod 4 =? 3);
    cbn; lia.
Qed.

Definition nu_of (s : OddState) : nat := fst (splitTwo (ob s / 2 + 1)).

Definition a_next_of (s : OddState) : nat := snd (splitTwo (ob s / 2 + 1)).

Definition R_odd (s : OddState) : option OddState :=
  let m := ob s / 2 + 1 in
  let nu := nu_of s in
  let a' := a_next_of s in
  let sig := sigma_true (ob s) (od s) in
  if oc s <? sig + nu then None
  else
    let M := oc s - sig - nu in
    let d' := 2 - od s in
    if nu =? 0 then
      let b' := if ob s mod 4 =? 1 then oc s + od s / 2 else oc s + 1 - od s / 2 in
      let c' := if ob s mod 4 =? 1 then oa s + a' + 1 else oa s + a' - 1 + od s in
      Some (mkOdd a' b' c' d')
    else
      let b' := if M mod 2 =? 0 then M + 2 else M in
      let c' := 2 * m - a' + oa s + 2 * nu +
        (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0) +
        (if M mod 2 =? 0 then 0 else 2) - 1 in
      Some (mkOdd a' b' c' d').

Lemma R_odd_halt_iff (s : OddState) :
  R_odd s = None <-> oc s < sigma_true (ob s) (od s) + nu_of s.
Proof.
  unfold R_odd.
  destruct (oc s <? sigma_true (ob s) (od s) + nu_of s) eqn:E.
  - split; [intros _; lia | intros _; reflexivity].
  - destruct (nu_of s =? 0); (split; [discriminate | lia]).
Qed.

Theorem R_odd_sound (s s' : OddState) (hs : InSodd s) (hr : R_odd s = Some s') :
  SqReachesPlus (enc_odd (oa s) (ob s) (oc s) (od s)) (enc_odd (oa s') (ob s') (oc s') (od s')).
Proof.
  pose proof (phase1_to_M2 s hs) as hp1.
  destruct hs as [ha_odd [hb_ge1 [hc_ge3 [hc_odd hd]]]].
  pose proof (div_mod_2_4_le (ob s)) as Hb_dm.
  pose proof (div_mod_2_le (oa s)) as Ha_dm.
  pose proof (div_mod_2_le (oc s)) as Hc_dm.
  pose proof (div_mod_2_le (od s)) as Hd_dm.
  destruct (splitTwo_spec (ob s / 2 + 1) ltac:(lia)) as [hm_eq ha'_odd].
  fold (nu_of s) (a_next_of s) in hm_eq, ha'_odd.
  set (m := ob s / 2 + 1) in hm_eq |- *.
  assert (hm_def : m = ob s / 2 + 1) by reflexivity.
  clearbody m.
  pose proof (div_mod_2_le (a_next_of s)) as Ha'_dm.
  set (w1 := if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
             then oc s else oc s - 1) in hp1.
  assert (hw1_def : forall _ : unit, w1 = if (((ob s mod 2 =? 0) && (od s =? 0)) || ((ob s mod 2 =? 1) && (od s =? 2)))%bool
                         then oc s else oc s - 1) by (intro; reflexivity).
  clearbody w1.
  set (Z1 := if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2) in hp1.
  assert (hZ1_def : forall _ : unit, Z1 = if ((ob s mod 2 =? 0) && (od s =? 0))%bool then oa s else oa s + 2) by (intro; reflexivity).
  clearbody Z1.
  set (d' := 2 - od s) in hp1.
  assert (hd' : d' = 0 \/ d' = 2) by (unfold d'; lia).
  assert (hZ1_odd : Z1 mod 2 = 1).
  { rewrite (hZ1_def tt). destruct ((ob s mod 2 =? 0) && (od s =? 0))%bool;
      [exact ha_odd | rewrite add_two_mod2; exact ha_odd]. }
  unfold R_odd in hr; cbn zeta in hr; rewrite <- hm_def in hr.
  destruct (oc s <? sigma_true (ob s) (od s) + nu_of s) eqn:Elt; [discriminate hr |].
  destruct (nu_of s) as [| t] eqn:Enu.
  - (* nu_of s = 0 *)
    cbn [Nat.eqb] in hr.
    inversion hr; subst s'; clear hr; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
    cbn [Nat.pow] in hm_eq.
    set (r := a_next_of s / 2).
    assert (ha'_eq : a_next_of s = 2 * r + 1) by (unfold r; lia).
    clearbody r.
    assert (hqb : 2 * (ob s / 2) = 4 * r) by lia.
    rewrite hqb in hp1.
    pose proof (phase2_odd r w1 Z1 d' hZ1_odd hd') as hp2.
    pose proof (sqReachesPlus_trans hp1 hp2) as htot.
    assert (hb_mod4_0 : ob s mod 4 = 0 \/ ob s mod 4 = 1) by lia.
    assert (hb2_from_4 : (ob s mod 4 = 0 -> ob s mod 2 = 0) /\ (ob s mod 4 = 1 -> ob s mod 2 = 1)) by lia.
    assert (hbw : w1 + 1 = (if ob s mod 4 =? 1 then oc s + od s / 2 else oc s + 1 - od s / 2)).
    { rewrite (hw1_def tt); clear hw1_def hZ1_def hp1 hp2 htot.
      destruct hb_mod4_0 as [hb4 | hb4], hd as [hd0 | hd2];
        [pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0
        |pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2];
        cbn; lia. }
    assert (hcz : Z1 + 2 * r = (if ob s mod 4 =? 1 then oa s + a_next_of s + 1 else oa s + a_next_of s - 1 + od s)).
    { rewrite (hZ1_def tt); clear hw1_def hZ1_def hp1 hp2 htot hbw.
      destruct hb_mod4_0 as [hb4 | hb4], hd as [hd0 | hd2];
        [pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0
        |pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2];
        cbn; lia. }
    rewrite <- ha'_eq, hbw, hcz in htot.
    exact htot.
  - (* nu_of s = S t *)
    cbn [Nat.eqb] in hr.
    replace (S t) with (t + 1) in hr, hm_eq, Elt by (clear; lia).
    inversion hr; subst s'; clear hr; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
    pose proof (mul_pos_of_pos_of_odd (one_le_pow2 t) ha'_odd) as hta_pos.
    assert (hm_half : m = 2 * (2 ^ t * a_next_of s)).
    { rewrite <- hm_eq, pow2_add1, <- Nat.mul_assoc. reflexivity. }
    set (r0 := 2 ^ t * a_next_of s - 1).
    assert (hr0_m : 2 * r0 + 2 = m) by (unfold r0; lia).
    clearbody r0.
    assert (hqb : 2 * (ob s / 2) = 4 * r0 + 2) by lia.
    rewrite hqb in hp1.
    pose proof (phase2_even r0 w1 Z1 d' hZ1_odd hd') as hp2.
    rewrite hr0_m in hp2.
    assert (hb_mod4 : ob s mod 4 = 2 \/ ob s mod 4 = 3) by lia.
    assert (hb2_from_4 : (ob s mod 4 = 2 -> ob s mod 2 = 0) /\ (ob s mod 4 = 3 -> ob s mod 2 = 1)) by lia.
    assert (hsig_eq : forall _ : unit, sigma_true (ob s) (od s) =
        if (((ob s mod 4 =? 2) && (od s =? 0)) || ((ob s mod 4 =? 3) && (od s =? 2)))%bool then 1 else 0).
    { intro; unfold sigma_true.
      destruct hb_mod4 as [hb4 | hb4], hd as [hd0 | hd2];
        rewrite hb4, ?hd0, ?hd2; reflexivity. }
    assert (hpsi_eval :
        fst (psiTilde w1 Z1) = oc s - sigma_true (ob s) (od s) /\
        snd (psiTilde w1 Z1) + 2 * r0 =
          m + oa s + (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0)).
    { rewrite (hsig_eq tt), (hw1_def tt), (hZ1_def tt); clear hw1_def hZ1_def hp1 hp2 hsig_eq.
      destruct hb_mod4 as [hb4 | hb4], hd as [hd0 | hd2];
        [pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0; cbn [Nat.eqb andb orb];
         rewrite (psiTilde_odd_val (oc s) _ hc_odd); cbn [fst snd]; lia
        |pose proof (proj1 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2; cbn [Nat.eqb andb orb];
         rewrite (psiTilde_pred_odd (oc s) _ hc_ge3 hc_odd); cbn [fst snd]; lia
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd0; cbn [Nat.eqb andb orb];
         rewrite (psiTilde_pred_odd (oc s) _ hc_ge3 hc_odd); cbn [fst snd]; lia
        |pose proof (proj2 hb2_from_4 hb4) as hb2; rewrite hb4, hb2, hd2; cbn [Nat.eqb andb orb];
         rewrite (psiTilde_odd_val (oc s) _ hc_odd); cbn [fst snd]; lia]. }
    clear hw1_def hZ1_def hsig_eq hb_mod4 hb2_from_4.
    destruct hpsi_eval as [hB0 hC0].
    rewrite hB0, hC0 in hp2; clear hB0 hC0.
    assert (hElt_ge : oc s >= sigma_true (ob s) (od s) + (t + 1)) by (clear - Elt; lia); clear Elt.
    set (B0 := oc s - sigma_true (ob s) (od s)) in hp2 |- *.
    set (C0 := m + oa s + (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0)) in hp2 |- *.
    assert (hC0_def : forall _ : unit, C0 = m + oa s + (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0)) by (intro; reflexivity).
    clearbody C0.
    assert (hC0_odd : C0 mod 2 = 1).
    { rewrite (hC0_def tt).
      replace (m + oa s + (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0))
        with (oa s + 2 * (2 ^ t * a_next_of s + (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 1 else 0)))
        by (clear - hm_half; destruct ((ob s mod 2 =? 1) && (od s =? 2))%bool; lia).
      rewrite add_even_mod2. exact ha_odd. }
    assert (hB0_ge : B0 >= t + 1) by (unfold B0; clear - hElt_ge; lia).
    rewrite <- hm_eq in hp2.
    pose proof (even_cascade t (a_next_of s) B0 C0 d' ha'_odd ltac:(clear - hB0_ge; lia) hC0_odd hd') as hcas.
    set (r' := a_next_of s / 2).
    assert (ha'_eq : a_next_of s = 2 * r' + 1) by (unfold r'; clear - Ha'_dm ha'_odd; lia).
    clearbody r'.
    set (Ct := C0 + (2 ^ (t + 1) - 2) * a_next_of s + 2 * t) in hcas |- *.
    assert (hCt_odd : Ct mod 2 = 1).
    { unfold Ct.
      assert (hp2_ev : (2 ^ (t + 1) - 2) * a_next_of s + 2 * t =
          2 * ((2 ^ t - 1) * a_next_of s + t)).
      { clear. rewrite pow2_add1. pose proof (one_le_pow2 t). nia. }
      replace (C0 + (2 ^ (t + 1) - 2) * a_next_of s + 2 * t)
        with (C0 + 2 * ((2 ^ t - 1) * a_next_of s + t)) by (clear - hp2_ev; lia).
      rewrite add_even_mod2. exact hC0_odd. }
    pose proof (step_even_exit r' (B0 - t) Ct d' ltac:(clear - hB0_ge; lia) hCt_odd hd') as hexit.
    rewrite <- ha'_eq in hexit.
    pose proof (sqReachesPlus_trans (sqReachesPlus_trans hp1 (sqReachesPlus_star_trans hp2 hcas)) hexit) as htot.
    set (M := oc s - sigma_true (ob s) (od s) - (t + 1)).
    assert (hBt : B0 - t - 1 = M) by (unfold B0, M; clear; lia).
    rewrite hBt in htot.
    pose proof (div_mod_2_le M) as HM_dm.
    assert (hb_final : fst (psiTilde M Ct) + 1 = (if M mod 2 =? 0 then M + 2 else M)).
    { unfold psiTilde. clear - HM_dm. destruct (M mod 2 =? 0) eqn:EM; cbn [fst]; lia. }
    assert (hc_final : snd (psiTilde M Ct) + 2 + 2 * r' =
        2 * m - a_next_of s + oa s + 2 * (t + 1) +
        (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0) +
        (if M mod 2 =? 0 then 0 else 2) - 1).
    { assert (hm_sub : (2 ^ (t + 1) - 2) * a_next_of s = m - 2 * a_next_of s).
      { rewrite Nat.mul_sub_distr_r, hm_eq. reflexivity. }
      assert (hm_ge_2a : m >= 2 * a_next_of s).
      { clear - hm_half. rewrite hm_half. pose proof (one_le_pow2 t). nia. }
      unfold psiTilde, Ct. rewrite (hC0_def tt), hm_sub; clear - ha'_eq hm_ge_2a.
      destruct (M mod 2 =? 0) eqn:EM, ((ob s mod 2 =? 1) && (od s =? 2))%bool; cbn [snd]; lia. }
    rewrite hb_final, hc_final in htot.
    exact htot.
Qed.

Lemma R_odd_props (s s' : OddState) (hs : InSdom s) (hr : R_odd s = Some s') :
  InSdom s' /\
  oa s' = a_next_of s /\
  2 ^ (nu_of s + 1) * oa s' = 2 * (ob s / 2 + 1) /\
  2 * (ob s / 2 + 1) <= ob s + 2 /\ ob s + 1 <= 2 * (ob s / 2 + 1) /\
  ob s + oa s + 2 * nu_of s <= 2 * oc s' /\
  2 ^ (nu_of s + 1) <= ob s + 2 /\
  (nu_of s = 0 ->
    oc s <= ob s' /\ ob s' <= oc s + 1 /\
    oa s + oa s' <= oc s' + 1 /\ oc s' <= oa s + oa s' + 1 /\
    oa s + (ob s + 1) / 2 <= oc s') /\
  (nu_of s >= 1 ->
    ob s' + nu_of s <= oc s + 2 /\ oc s <= ob s' + nu_of s + 1 /\
    2 * (ob s / 2 + 1) + oa s + 2 * nu_of s <= oc s' + oa s' + 1 /\
    oc s' + oa s' <= 2 * (ob s / 2 + 1) + oa s + 2 * nu_of s + 3).
Proof.
  destruct hs as [[ha_odd [hb_ge1 [hc_ge3 [hc_odd hd]]]] hca].
  pose proof (div_mod_2_4_le (ob s)) as Hb_dm.
  pose proof (div_mod_2_le (oa s)) as Ha_dm.
  pose proof (div_mod_2_le (oc s)) as Hc_dm.
  pose proof (div_mod_2_le (od s)) as Hd_dm.
  destruct (splitTwo_spec (ob s / 2 + 1) ltac:(lia)) as [hm_eq ha'_odd].
  fold (nu_of s) (a_next_of s) in hm_eq, ha'_odd.
  set (m := ob s / 2 + 1) in hm_eq |- *.
  assert (hm_def : m = ob s / 2 + 1) by reflexivity.
  clearbody m.
  pose proof (div_mod_2_le (a_next_of s)) as Ha'_dm.
  assert (h2m : 2 ^ (nu_of s + 1) * a_next_of s = 2 * m).
  { rewrite pow2_add1, <- Nat.mul_assoc, hm_eq. reflexivity. }
  pose proof (sigma_true_le_one (ob s) (od s)) as hsig.
  unfold R_odd in hr; cbn zeta in hr; rewrite <- hm_def in hr.
  destruct (oc s <? sigma_true (ob s) (od s) + nu_of s) eqn:Elt; [discriminate hr |].
  assert (hElt_ge : oc s >= sigma_true (ob s) (od s) + nu_of s) by (clear - Elt; lia); clear Elt.
  set (d' := 2 - od s) in hr.
  assert (hd' : forall _ : unit, d' = 0 \/ d' = 2) by (intro; unfold d'; clear - hd; lia); clearbody d'.
  assert (hb_sand : 2 * m <= ob s + 2 /\ ob s + 1 <= 2 * m) by (clear - hm_def Hb_dm; lia).
  destruct (hb_sand) as [hb_lo hb_hi].
  destruct (nu_of s =? 0) eqn:Enu0.
  - (* nu_of s = 0 *)
    assert (hnu0 : nu_of s = 0) by (clear - Enu0; lia); clear Enu0.
    rewrite hnu0 in hm_eq; cbn [Nat.pow] in hm_eq.
    assert (h2p0 : 2 ^ (nu_of s + 1) = 2) by (rewrite hnu0; reflexivity).
    assert (hod_le2 : od s <= 2) by (clear - hd; lia).
    assert (hod_even : od s = 2 * (od s / 2)) by (clear - hd Hd_dm; lia).
    pose proof (div_mod_2_le (ob s + 1)) as Hbp_dm.
    assert (hbp_hi : (ob s + 1) / 2 <= m) by (clear - hm_def Hb_dm Hbp_dm; lia).
    destruct (ob s mod 4 =? 1) eqn:Eb4;
      [assert (hb4 : ob s mod 4 = 1) by (clear - Eb4; lia)
      |assert (ha'_ge3 : a_next_of s >= 3) by (clear - Eb4 Hb_dm hm_def hm_eq ha'_odd Ha'_dm hb_ge1; lia);
       assert (hbp_eq : (ob s + 1) / 2 + 1 = a_next_of s)
         by (clear - Eb4 Hb_dm Hbp_dm hm_def hm_eq ha'_odd Ha'_dm; lia)];
      clear Eb4;
      cbn beta iota zeta in hr; apply some_inj in hr; subst s';
      unfold InSdom, InSodd; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
    + pose proof (div_mod_2_le (oa s + a_next_of s + 1)) as Hcp.
      clear - ha'_odd ha_odd hb_ge1 hc_ge3 hod_le2 hod_even Ha_dm Ha'_dm
              hm_eq h2m hd' hb_lo hb_hi hnu0 h2p0 hbp_hi Hcp.
      repeat match goal with |- _ /\ _ => split end;
        try exact ha'_odd; try exact (hd' tt); try exact h2m;
        try exact hb_lo; try exact hb_hi;
        [lia .. | intro; repeat split; lia | intro; exfalso; lia].
    + set (c' := oa s + a_next_of s - 1 + od s).
      assert (hc' : c' + 1 = oa s + a_next_of s + od s) by (unfold c'; clear - Ha_dm ha_odd; lia); clearbody c'.
      pose proof (div_mod_2_le c') as Hcp.
      clear - ha'_odd ha_odd hb_ge1 hc_ge3 hod_le2 hod_even Ha_dm Ha'_dm
              hm_eq h2m hd' hb_lo hb_hi hnu0 h2p0 ha'_ge3 hbp_eq hc' Hcp.
      repeat match goal with |- _ /\ _ => split end;
        try exact ha'_odd; try exact (hd' tt); try exact h2m;
        try exact hb_lo; try exact hb_hi;
        [lia .. | intro; repeat split; lia | intro; exfalso; lia].
  - (* nu_of s >= 1 *)
    assert (hnu_ge1 : nu_of s >= 1) by (clear - Enu0; lia); clear Enu0.
    assert (hm_ge_2a : m >= 2 * a_next_of s).
    { clear - hm_eq hnu_ge1. rewrite <- hm_eq.
      replace (nu_of s) with ((nu_of s - 1) + 1) by lia.
      rewrite pow2_add1. pose proof (one_le_pow2 (nu_of s - 1)). nia. }
    assert (hpow_le : 2 ^ (nu_of s + 1) <= ob s + 2) by (clear - h2m ha'_odd Ha'_dm hb_lo; nia).
    cbn zeta in hr.
    set (M := oc s - sigma_true (ob s) (od s) - nu_of s) in hr.
    assert (hM_add : M + sigma_true (ob s) (od s) + nu_of s = oc s) by (unfold M; clear - hElt_ge; lia).
    clearbody M.
    set (K := 2 * m - a_next_of s + oa s + 2 * nu_of s) in hr.
    assert (hK_add : K + a_next_of s = 2 * m + oa s + 2 * nu_of s) by (unfold K; clear - hm_ge_2a; lia).
    clearbody K.
    set (d1 := if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0) in hr.
    assert (hd1 : d1 <= 2 /\ d1 = 2 * (d1 / 2))
      by (unfold d1; clear; destruct ((ob s mod 2 =? 1) && (od s =? 2))%bool; cbn; lia).
    clearbody d1.
    set (d2 := if M mod 2 =? 0 then 0 else 2) in hr.
    assert (hd2_ev : d2 <= 2 /\ d2 = 2 * (d2 / 2))
      by (unfold d2; clear; destruct (M mod 2 =? 0); cbn; lia).
    clearbody d2.
    set (c' := K + d1 + d2 - 1) in hr.
    assert (hc' : c' + 1 = K + d1 + d2) by (unfold c'; clear - hK_add hm_ge_2a Ha_dm ha_odd; lia).
    clearbody c'.
    pose proof (div_mod_2_le c') as Hcp.
    pose proof (div_mod_2_le M) as HM_dm.
    destruct (M mod 2 =? 0) eqn:EM;
      [assert (hM_mod : M mod 2 = 0) by (clear - EM; lia)
      |assert (hM_mod : M mod 2 = 1) by (clear - EM HM_dm; lia)]; clear EM;
      cbn beta iota zeta in hr; apply some_inj in hr; subst s';
      unfold InSdom, InSodd; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk;
      clear - ha'_odd ha_odd hb_ge1 hc_ge3 Ha_dm Ha'_dm
              h2m hsig hd' hb_lo hb_hi hnu_ge1 hm_ge_2a hpow_le hM_add hK_add hd1 hd2_ev hc' HM_dm hM_mod Hcp;
      (repeat match goal with |- _ /\ _ => split end;
        try exact ha'_odd; try exact (hd' tt); try exact h2m;
        try exact hb_lo; try exact hb_hi; try exact hpow_le;
        [lia .. | intro; exfalso; lia | intro; repeat split; lia]).
Qed.

Definition Hide (P : Prop) : Prop := P.
Lemma hide_intro {P : Prop} (h : P) : Hide P. Proof. exact h. Qed.
Lemma hide_elim {P : Prop} (h : Hide P) : P. Proof. exact h. Qed.
Opaque Hide.

(* ========================================================================== *)
(* Section 5B: Two-Step 2-Adic Collapse Bounds (halt_3 & halt_5)              *)
(* ========================================================================== *)

Lemma pow_two_ge_succ (n : nat) : 2 ^ n >= n + 1.
Proof.
  induction n as [| n ih]; cbn [Nat.pow]; lia.
Qed.

Lemma pow_two_ge_8 (e0 : nat) (he : e0 >= 3) : 2 ^ (e0 + 1) + 8 >= 8 * e0.
Proof.
  induction e0 as [| e0 ih]; [lia |].
  assert (hc : e0 = 2 \/ e0 >= 3) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (3 + 1)) with 16; lia.
  - pose proof (ih hge). replace (S e0 + 1) with (S (e0 + 1)) by lia. cbn [Nat.pow]; lia.
Qed.

Lemma pow_two_ge_14 (e0 : nat) (he : e0 >= 3) : 2 ^ (e0 + 1) + 26 >= 14 * e0.
Proof.
  induction e0 as [| e0 ih]; [lia |].
  assert (hc : e0 = 2 \/ e0 >= 3) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (3 + 1)) with 16; lia.
  - pose proof (ih hge). replace (S e0 + 1) with (S (e0 + 1)) by lia. cbn [Nat.pow]; lia.
Qed.

Lemma pow_two_ge_16 (n : nat) (hn : n >= 5) : 2 ^ (n + 1) + 16 >= 16 * n.
Proof.
  induction n as [| n ih]; [lia |].
  assert (hc : n = 4 \/ n >= 5) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (5 + 1)) with 64; lia.
  - pose proof (ih hge). replace (S n + 1) with (S (n + 1)) by lia. cbn [Nat.pow]; lia.
Qed.

Lemma sq_lt_pow2_succ (e0 : nat) (he : e0 >= 3) : e0 * e0 < 2 ^ (e0 + 1).
Proof.
  induction e0 as [| e0 ih]; [lia |].
  assert (hc : e0 = 2 \/ e0 >= 3) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (3 + 1)) with 16; lia.
  - pose proof (ih hge) as h1.
    pose proof (pow_two_ge_8 e0 hge) as h2.
    replace (S e0 + 1) with (S (e0 + 1)) by lia. cbn [Nat.pow].
    nia.
Qed.

Lemma quad_step1_lt (e0 : nat) (he : e0 >= 8) : (5 * e0 + 5) * e0 < 2 ^ (e0 + 1).
Proof.
  induction e0 as [| e0 ih]; [lia |].
  assert (hc : e0 = 7 \/ e0 = 8 \/ e0 >= 9) by lia.
  destruct hc as [-> | [-> | hge]].
  - change (2 ^ (8 + 1)) with 512; lia.
  - change (2 ^ (9 + 1)) with 1024; lia.
  - pose proof (ih ltac:(lia)) as h1.
    pose proof (pow_two_ge_14 e0 ltac:(lia)) as h2.
    replace (S e0 + 1) with (S (e0 + 1)) by lia. cbn [Nat.pow].
    nia.
Qed.

Lemma quad_step2a_lt (nu : nat) (hnu : nu >= 10) : (3 * nu + 6) * (3 * nu + 7) < 2 ^ (nu + 1).
Proof.
  induction nu as [| nu ih]; [lia |].
  assert (hc : nu = 9 \/ nu >= 10) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (10 + 1)) with 2048; lia.
  - pose proof (ih hge) as h1.
    assert (h3 : 2 ^ (nu + 1) > 18 * nu + 48).
    { assert (hc2 : nu = 10 \/ nu >= 11) by lia.
      destruct hc2 as [-> | h11].
      - change (2 ^ (10 + 1)) with 2048; lia.
      - pose proof (pow_two_ge_16 (nu - 1) ltac:(lia)) as hk.
        replace (nu + 1) with (S ((nu - 1) + 1)) by lia. cbn [Nat.pow]. lia. }
    replace (S nu + 1) with (S (nu + 1)) by lia. cbn [Nat.pow].
    nia.
Qed.

Lemma quad_step2b_lt (nu : nat) (hnu : nu >= 11) : (6 * nu + 11) * (3 * nu + 8) < 2 ^ (nu + 1).
Proof.
  assert (hlin : forall n, n >= 11 -> 2 ^ (n + 1) > 36 * n + 99).
  { induction n as [| n ihn]; intros hn; [lia |].
    assert (hc : n = 10 \/ n >= 11) by lia.
    destruct hc as [-> | hge].
    - change (2 ^ (11 + 1)) with 4096; lia.
    - pose proof (ihn hge). replace (S n + 1) with (S (n + 1)) by lia. cbn [Nat.pow]; lia. }
  induction nu as [| nu ih]; [lia |].
  assert (hc : nu = 10 \/ nu >= 11) by lia.
  destruct hc as [-> | hge].
  - change (2 ^ (11 + 1)) with 4096; lia.
  - pose proof (ih hge) as h1.
    pose proof (hlin nu hge) as h2.
    replace (S nu + 1) with (S (nu + 1)) by lia. cbn [Nat.pow].
    nia.
Qed.

Lemma pow2_dvd_diff_ge {u w1 w2 x1 x2 : nat} (hu1 : u <= w1) (hu2 : u <= w2)
    (hlt : 2 ^ w1 * x1 < 2 ^ w2 * x2) :
  2 ^ u + 2 ^ w1 * x1 <= 2 ^ w2 * x2.
Proof.
  assert (hw1 : 2 ^ w1 * x1 = 2 ^ u * (2 ^ (w1 - u) * x1)).
  { replace w1 with (u + (w1 - u)) at 1 by lia. rewrite Nat.pow_add_r, Nat.mul_assoc. reflexivity. }
  assert (hw2 : 2 ^ w2 * x2 = 2 ^ u * (2 ^ (w2 - u) * x2)).
  { replace w2 with (u + (w2 - u)) at 1 by lia. rewrite Nat.pow_add_r, Nat.mul_assoc. reflexivity. }
  rewrite hw1, hw2 in hlt |- *.
  set (p := 2 ^ u) in hlt |- *; clearbody p.
  set (y1 := 2 ^ (w1 - u) * x1) in hlt |- *; clearbody y1.
  set (y2 := 2 ^ (w2 - u) * x2) in hlt |- *; clearbody y2.
  clear hw1 hw2 hu1 hu2.
  assert (hy : y1 + 1 <= y2) by nia.
  nia.
Qed.

Lemma pow2_odd_inj {u1 u2 x1 x2 : nat} (hx1 : x1 mod 2 = 1) (hx2 : x2 mod 2 = 1)
    (heq : 2 ^ u1 * x1 = 2 ^ u2 * x2) : u1 = u2 /\ x1 = x2.
Proof.
  pose proof (f_equal splitTwo heq) as h.
  rewrite (splitTwo_pow_mul_odd u1 x1 hx1), (splitTwo_pow_mul_odd u2 x2 hx2) in h.
  inversion h; auto.
Qed.

Lemma halt3_step1_bounds (s2 s1 s0 : OddState)
    (hs2 : InSdom s2) (hr2 : R_odd s2 = Some s1)
    (hr1 : R_odd s1 = Some s0) (hr0 : R_odd s0 = None) :
  nu_of s2 >= 1 /\ oc s2 <= ob s1 + nu_of s2 + 1 /\
  (nu_of s2 <= 7 -> oa s1 <= 3 /\ oc s2 <= 15 /\ 2 * oa s1 + oc s2 <= 16 /\ 2 * oa s1 + oc s2 <= nu_of s2 + 11) /\
  (nu_of s2 >= 8 -> 4 * oa s1 + 2 * ob s1 <= nu_of s2 + 10).
Proof.
  pose proof (R_odd_props s2 s1 hs2 hr2) as hp2.
  destruct hp2 as [hs1 [ha1_def [hm2_pow [hb2_lo [hb2_hi [hsum2 [hpow2 [hz2_0 hz2_1]]]]]]]].
  apply hide_intro in hz2_0, hz2_1.
  pose proof (R_odd_props s1 s0 hs1 hr1) as hp1.
  destruct hp1 as [hs0 [ha0_def [hm1_pow [hb1_lo [hb1_hi [hsum1 [hpow1 [hz1_0 hz1_1]]]]]]]].
  apply hide_intro in hz1_0, hz1_1.
  destruct hs0 as [[ha0_s0_odd [hb0_ge1 [hc0_ge3 [hc0_odd hd0]]]] hca0].
  apply hide_intro in hd0.
  pose proof (proj1 (R_odd_halt_iff s0) hr0) as hhalt0.
  pose proof (sigma_true_le_one (ob s0) (od s0)) as hsig0.
  assert (hE_ge3 : nu_of s0 >= 3) by (clear - hc0_ge3 hhalt0 hsig0; lia).
  destruct (splitTwo_spec (ob s0 / 2 + 1) ltac:(clear; lia)) as [hm0_eq ha0_odd].
  fold (nu_of s0) (a_next_of s0) in hm0_eq, ha0_odd.
  pose proof (div_mod_2_le (a_next_of s0)) as Ha0n_dm.
  assert (hm0_pow : 2 ^ (nu_of s0 + 1) * a_next_of s0 = 2 * (ob s0 / 2 + 1)).
  { rewrite pow2_add1, <- Nat.mul_assoc, hm0_eq. reflexivity. }
  assert (hm0_ge_pow : 2 * (ob s0 / 2 + 1) >= 2 ^ (nu_of s0 + 1)) by (clear - hm0_pow ha0_odd Ha0n_dm; nia).
  pose proof (pow_two_ge_8 (nu_of s0) hE_ge3) as hp0_8.
  pose proof (div_mod_2_le (ob s0)) as Hb0_dm.
  assert (hb0_lo : 2 * (ob s0 / 2 + 1) <= ob s0 + 2) by (clear - Hb0_dm; lia).
  assert (hb0_hi : ob s0 + 1 <= 2 * (ob s0 / 2 + 1)) by (clear - Hb0_dm; lia).
  pose proof (div_mod_2_4_le (ob s1)) as Hb1_dm.
  pose proof (div_mod_2_le (ob s1 + 1)) as Hb1p_dm.
  pose proof (div_mod_2_le (oa s1)) as Ha1_dm.
  pose proof (div_mod_2_le (oc s1)) as Hc1_dm.
  pose proof (div_mod_2_le (od s1)) as Hd1_dm.
  assert (hs1_unif : nu_of s0 >= oa s1 + (ob s1 + 1) / 2 + 2 * nu_of s1 /\
      2 * (ob s0 / 2 + 1) + nu_of s1 <= oc s1 + 4 /\ oc s1 <= 2 * (ob s0 / 2 + 1) + nu_of s1).
  { destruct (nu_of s1) as [| t1] eqn:Enu1.
    - pose proof (hide_elim hz1_0 eq_refl) as h0.
      clear - h0 hb0_lo hb0_hi hhalt0 hsig0; lia.
    - pose proof (hide_elim hz1_1 ltac:(clear; lia)) as h1.
      pose proof (div_mod_2_le (oa s0)) as Ha0_dm.
      assert (hm1_2 : 2 * (ob s1 / 2 + 1) >= 4 * oa s0).
      { clear - hm1_pow. replace (S t1 + 1) with (2 + t1) in hm1_pow by lia.
        rewrite Nat.pow_add_r in hm1_pow. change (2 ^ 2) with 4 in hm1_pow.
        pose proof (one_le_pow2 t1). nia. }
      clear - h1 hm1_2 hb0_lo hb0_hi hhalt0 hsig0 ha0_s0_odd Ha0_dm Hb1_dm Hb1p_dm Enu1; lia. }
  destruct hs1_unif as [hE_lb [hc1_lo hc1_hi]].
  clear hr1 hr0 ha0_def hm1_pow hsum1 hpow1 hz1_0 hz1_1 ha0_s0_odd hb0_ge1 hc0_ge3 hc0_odd hd0 hca0 hhalt0 hsig0 hm0_eq hb0_lo hb0_hi Hb0_dm Hd1_dm Hc1_dm.
  destruct hs2 as [[ha2_odd [hb2_ge1 [hc2_ge3 [hc2_odd hd2]]]] ha2_le_c2].
  apply hide_intro in hd2.
  destruct hs1 as [[ha1_odd [hb1_ge1 _]] _].
  pose proof (div_mod_2_le (oa s2)) as Ha2_dm.
  assert (hnu2_ge1 : nu_of s2 >= 1).
  { destruct (nu_of s2) as [| t2] eqn:Enu2; [| clear; lia].
    pose proof (hide_elim hz2_0 eq_refl). lia. }
  pose proof (hide_elim hz2_1 hnu2_ge1) as hz2.
  destruct hz2 as [hc2_lo [hc2_ub [hc1_from2_lo hc1_from2_hi]]].
  clear hr2 ha1_def hz2_0 hz2_1 hb2_ge1 hc2_ge3 hc2_odd hd2.
  set (e0 := nu_of s0) in *. clearbody e0.
  set (m0_2 := 2 * (ob s0 / 2 + 1)) in *. clearbody m0_2.
  set (nu2 := nu_of s2) in *. clearbody nu2.
  set (m2_2 := 2 * (ob s2 / 2 + 1)) in *. clearbody m2_2.
  set (nu1 := nu_of s1) in *. clearbody nu1.
  assert (hm2_ge_2a : m2_2 >= 2 * oa s1).
  { clear - hm2_pow. rewrite <- hm2_pow.
    replace (nu2 + 1) with (1 + nu2) by lia.
    rewrite Nat.pow_add_r. change (2 ^ 1) with 2.
    pose proof (one_le_pow2 nu2). nia. }
  assert (hm2_lt_m0 : m2_2 < m0_2).
  { assert (hL_m : m2_2 + 2 * nu2 <= m0_2 + oa s1 + nu1) by lia.
    assert (htri : m2_2 < m0_2 \/ m2_2 = m0_2 \/ m0_2 < m2_2) by (clear; lia).
    destruct htri as [hlt | [heq | hgt]]; [exact hlt | |].
    - rewrite <- hm2_pow, <- hm0_pow in heq.
      destruct (pow2_odd_inj ha1_odd ha0_odd heq) as [hnu_eq _].
      lia.
    - rewrite <- hm2_pow, <- hm0_pow in hgt.
      assert (henu : e0 <= nu2 \/ nu2 < e0) by (clear; lia).
      destruct henu as [henu | henu].
      + pose proof (@pow2_dvd_diff_ge (e0 + 1) (e0 + 1) (nu2 + 1) (a_next_of s0) (oa s1) ltac:(clear; lia) ltac:(clear - henu; lia) hgt) as hdvd.
        rewrite hm2_pow, hm0_pow in hdvd. lia.
      + pose proof (@pow2_dvd_diff_ge (nu2 + 1) (e0 + 1) (nu2 + 1) (a_next_of s0) (oa s1) ltac:(clear - henu; lia) ltac:(clear; lia) hgt) as hdvd.
        rewrite hm2_pow, hm0_pow in hdvd.
        assert (hpow_le_E : 2 ^ (nu2 + 1) <= e0) by lia.
        assert (ha1_le_E : oa s1 <= e0) by lia.
        assert (hprod : m2_2 <= e0 * e0) by (clear - hm2_pow hpow_le_E ha1_le_E; rewrite <- hm2_pow; nia).
        pose proof (sq_lt_pow2_succ e0 hE_ge3). lia. }
  assert (hdiff_ub : m0_2 + oa s1 + nu1 <= m2_2 + ob s1 + 3 * nu2 + 8) by lia.
  clear hc2_lo hc1_from2_lo hc1_from2_hi hc1_lo hc1_hi ha2_le_c2 ha2_odd Ha2_dm.
  refine (conj hnu2_ge1 (conj hc2_ub (conj _ _))).
  - intros hnu2_le7.
    assert (hcaseA : nu2 <= e0 \/ e0 < nu2) by (clear; lia).
    destruct hcaseA as [hcaseA | hcaseA].
    + assert (hdvd : 2 ^ (nu2 + 1) + m2_2 <= m0_2).
      { rewrite <- hm0_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear; lia | clear - hcaseA; lia | rewrite hm2_pow, hm0_pow; exact hm2_lt_m0]. }
      assert (hpow_ub : 2 ^ (nu2 + 1) <= 2 * e0 + 3 * nu2 + 5) by lia.
      assert (hE_le7 : e0 <= 7).
      { assert (he7 : e0 <= 7 \/ e0 >= 8) by (clear; lia).
        destruct he7 as [he7 | he8]; [exact he7 |].
        pose proof (quad_step1_lt e0 he8) as hq.
        assert (ha1_le : oa s1 + 1 <= e0) by lia.
        assert (hp_le : 2 ^ (nu2 + 1) <= 5 * e0 + 5) by lia.
        assert (hprod : m2_2 + (5 * e0 + 5) <= (5 * e0 + 5) * e0)
          by (clear - hm2_pow hp_le ha1_le; rewrite <- hm2_pow; nia).
        lia. }
      assert (hnu2_le3 : nu2 <= 3).
      { assert (hc : nu2 <= 3 \/ nu2 = 4 \/ nu2 = 5 \/ nu2 = 6 \/ nu2 = 7) by (clear - hnu2_le7; lia).
        destruct hc as [h | [-> | [-> | [-> | ->]]]]; [exact h | | | |];
          [change (2 ^ (4 + 1)) with 32 in hpow_ub
          | change (2 ^ (5 + 1)) with 64 in hpow_ub
          | change (2 ^ (6 + 1)) with 128 in hpow_ub
          | change (2 ^ (7 + 1)) with 256 in hpow_ub]; lia. }
      assert (hpow_le16 : 2 ^ (nu2 + 1) <= 16).
      { pose proof (pow2_mono (nu2 + 1) 4 ltac:(clear - hnu2_le3; lia)) as hp4.
        change (2 ^ 4) with 16 in hp4. exact hp4. }
      assert (hm2_le_16a : m2_2 <= 16 * oa s1) by (clear - hm2_pow hpow_le16; rewrite <- hm2_pow; nia).
      assert (hE_le5 : e0 <= 5).
      { assert (hc : e0 <= 5 \/ e0 = 6 \/ e0 = 7) by (clear - hE_le7; lia).
        destruct hc as [h | [-> | ->]]; [exact h | |];
          [change (2 ^ (6 + 1)) with 128 in hm0_ge_pow
          | change (2 ^ (7 + 1)) with 256 in hm0_ge_pow]; lia. }
      lia.
    + assert (hdvd : 2 ^ (e0 + 1) + m2_2 <= m0_2).
      { rewrite <- hm0_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear - hcaseA; lia | clear; lia | rewrite hm2_pow, hm0_pow; exact hm2_lt_m0]. }
      pose proof (pow_two_ge_14 e0 hE_ge3). lia.
  - intros hnu2_ge8.
    assert (hcaseA : nu2 <= e0 \/ e0 < nu2) by (clear; lia).
    destruct hcaseA as [hcaseA | hcaseA].
    + assert (hdvd : 2 ^ (nu2 + 1) + m2_2 <= m0_2).
      { rewrite <- hm0_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear; lia | clear - hcaseA; lia | rewrite hm2_pow, hm0_pow; exact hm2_lt_m0]. }
      pose proof (quad_step1_lt e0 ltac:(clear - hnu2_ge8 hcaseA; lia)) as hq.
      assert (ha1_le : oa s1 + 1 <= e0) by lia.
      assert (hp_le : 2 ^ (nu2 + 1) <= 5 * e0 + 5) by lia.
      assert (hprod : m2_2 + (5 * e0 + 5) <= (5 * e0 + 5) * e0)
        by (clear - hm2_pow hp_le ha1_le; rewrite <- hm2_pow; nia).
      lia.
    + assert (hdvd : 2 ^ (e0 + 1) + m2_2 <= m0_2).
      { rewrite <- hm0_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear - hcaseA; lia | clear; lia | rewrite hm2_pow, hm0_pow; exact hm2_lt_m0]. }
      pose proof (pow_two_ge_14 e0 hE_ge3). lia.
Qed.

Lemma halt5_nu2_le_7 (s4 s3 s2 s1 s0 : OddState)
    (hs4 : InSdom s4) (hr4 : R_odd s4 = Some s3) (hr3 : R_odd s3 = Some s2)
    (hr2 : R_odd s2 = Some s1) (hr1 : R_odd s1 = Some s0) (hr0 : R_odd s0 = None) :
  nu_of s2 <= 7.
Proof.
  pose proof (R_odd_props s4 s3 hs4 hr4) as hp4.
  destruct hp4 as [hs3 [_ [hm4_pow [hb4_lo [hb4_hi [hsum4 [hpow4 [hz4_zero hz4_pos]]]]]]]].
  apply hide_intro in hz4_zero, hz4_pos.
  pose proof (R_odd_props s3 s2 hs3 hr3) as hp3.
  destruct hp3 as [hs2 [_ [_ [_ [_ [hb3_sum_raw [hpow_nu3 [hz3_0 hz3_1]]]]]]]].
  apply hide_intro in hz3_0, hz3_1.
  pose proof (halt3_step1_bounds s2 s1 s0 hs2 hr2 hr1 hr0) as [_ [hc2_ub [hstep1_le7 hstep1_ge8]]].
  clear hstep1_le7.
  apply hide_intro in hstep1_ge8.
  assert (hnu2_split : nu_of s2 <= 7 \/ nu_of s2 >= 8) by (clear; lia).
  destruct hnu2_split as [hnu2_le7 | hnu2_ge8]; [exact hnu2_le7 |].
  exfalso.
  pose proof (hide_elim hstep1_ge8 hnu2_ge8) as hlin1.
  clear hstep1_ge8 hr1 hr0.
  pose proof (R_odd_props s2 s1 hs2 hr2) as hp2.
  destruct hp2 as [[[ha1_odd [hb1_ge1 _]] _] [_ [hm2_pow [hb2_lo [hb2_hi _]]]]].
  clear hr2 hs2.
  destruct hs3 as [[ha3_odd [hb3_ge1 _]] _].
  pose proof (div_mod_2_le (oa s1)) as Ha1_dm.
  pose proof (div_mod_2_le (oa s3)) as Ha3_dm.
  assert (hc3_sand : 2 * (ob s2 / 2 + 1) + nu_of s3 <= oc s3 + 4 /\ oc s3 <= 2 * (ob s2 / 2 + 1) + nu_of s3).
  { destruct (nu_of s3) as [| t3];
      [pose proof (hide_elim hz3_0 eq_refl) as h0; clear - h0 hb2_lo hb2_hi; lia
      |pose proof (hide_elim hz3_1 ltac:(clear; lia)) as h1; clear - h1 hb2_lo hb2_hi; lia]. }
  clear hr3 hz3_0 hz3_1 hb2_lo hb2_hi.
  assert (hb3_sum : ob s3 + oa s3 + 2 * nu_of s3 <= 3 * nu_of s2 + 8) by lia.
  clear hb3_sum_raw hc2_ub.
  destruct hs4 as [[ha4_odd _] ha4_le_c4].
  pose proof (div_mod_2_le (oa s4)) as Ha4_dm.
  clear hr4.
  set (m2_2 := 2 * (ob s2 / 2 + 1)) in *. clearbody m2_2.
  set (m4_2 := 2 * (ob s4 / 2 + 1)) in *. clearbody m4_2.
  set (nu2 := nu_of s2) in *. clearbody nu2.
  set (nu3 := nu_of s3) in *. clearbody nu3.
  set (nu4 := nu_of s4) in *. clearbody nu4.
  assert (hm2_ge_pow : m2_2 >= 2 ^ (nu2 + 1)) by (clear - hm2_pow ha1_odd Ha1_dm; nia).
  pose proof (pow_two_ge_14 nu2 ltac:(clear - hnu2_ge8; lia)) as hp2_14.
  assert (hnu4_ge1 : nu4 >= 1).
  { destruct nu4 as [| t4]; [pose proof (hide_elim hz4_zero eq_refl); lia | clear; lia]. }
  pose proof (hide_elim hz4_pos hnu4_ge1) as hz4.
  clear hz4_zero hz4_pos.
  assert (hm4_ge_2a : m4_2 >= 2 * oa s3).
  { clear - hm4_pow. rewrite <- hm4_pow.
    replace (nu4 + 1) with (1 + nu4) by lia.
    rewrite Nat.pow_add_r. change (2 ^ 1) with 2.
    pose proof (one_le_pow2 nu4). nia. }
  assert (hL_m : m4_2 + 2 * nu4 <= m2_2 + oa s3 + nu3) by lia.
  assert (hU_m : m2_2 + nu3 + oa s3 <= m4_2 + ob s3 + 3 * nu4 + 8) by lia.
  clear hz4 hc3_sand ha4_odd ha4_le_c4 Ha4_dm hb4_lo hb4_hi hsum4 hpow4.
  assert (htri : m4_2 = m2_2 \/ m2_2 < m4_2 \/ m4_2 < m2_2) by (clear; lia).
  destruct htri as [heq | [hgt | hlt]].
  - (* Branch 1: m4_2 = m2_2 *)
    rewrite <- hm4_pow, <- hm2_pow in heq.
    destruct (pow2_odd_inj ha3_odd ha1_odd heq) as [hnu_eq ha_eq].
    pose proof (pow_two_ge_8 nu3 ltac:(lia)). lia.
  - (* Branch 2: m2_2 < m4_2 *)
    assert (hnu4_cmp : nu2 <= nu4 \/ nu4 < nu2) by (clear; lia).
    destruct hnu4_cmp as [hnu4_ge | hnu4_lt].
    + assert (hdvd : 2 ^ (nu2 + 1) + m2_2 <= m4_2).
      { rewrite <- hm4_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear; lia | clear - hnu4_ge; lia | rewrite hm2_pow, hm4_pow; exact hgt]. }
      lia.
    + assert (hdvd : 2 ^ (nu4 + 1) + m2_2 <= m4_2).
      { rewrite <- hm4_pow, <- hm2_pow.
        apply pow2_dvd_diff_ge; [clear - hnu4_lt; lia | clear; lia | rewrite hm2_pow, hm4_pow; exact hgt]. }
      assert (hp_ub : 2 ^ (nu4 + 1) <= 3 * nu2 + 6) by lia.
      assert (ha3_ub : oa s3 <= 3 * nu2 + 7) by lia.
      assert (hc2 : nu2 = 8 \/ nu2 = 9 \/ nu2 >= 10) by (clear - hnu2_ge8; lia).
      destruct hc2 as [h8 | [h9 | h10]].
      * assert (hnu4_le3 : nu4 <= 3).
        { assert (hc4 : nu4 <= 3 \/ nu4 = 4 \/ nu4 >= 5) by (clear; lia).
          destruct hc4 as [h3 | [-> | h5]]; [exact h3 | change (2 ^ (4 + 1)) with 32 in hp_ub; lia | pose proof (pow_two_ge_16 nu4 h5); lia]. }
        rewrite h8 in hm2_ge_pow, ha3_ub; change (2 ^ (8 + 1)) with 512 in hm2_ge_pow.
        assert (hc4 : nu4 = 1 \/ nu4 = 2 \/ nu4 = 3) by (clear - hnu4_ge1 hnu4_le3; lia).
        destruct hc4 as [-> | [-> | ->]];
          [change (2 ^ (1 + 1)) with 4 in hm4_pow
          | change (2 ^ (2 + 1)) with 8 in hm4_pow
          | change (2 ^ (3 + 1)) with 16 in hm4_pow]; lia.
      * assert (hnu4_le3 : nu4 <= 3).
        { assert (hc4 : nu4 <= 3 \/ nu4 = 4 \/ nu4 >= 5) by (clear; lia).
          destruct hc4 as [h3 | [-> | h5]]; [exact h3 | change (2 ^ (4 + 1)) with 32 in hdvd; lia | pose proof (pow_two_ge_16 nu4 h5); lia]. }
        rewrite h9 in hm2_ge_pow, ha3_ub; change (2 ^ (9 + 1)) with 1024 in hm2_ge_pow.
        assert (hc4 : nu4 = 1 \/ nu4 = 2 \/ nu4 = 3) by (clear - hnu4_ge1 hnu4_le3; lia).
        destruct hc4 as [-> | [-> | ->]];
          [change (2 ^ (1 + 1)) with 4 in hm4_pow
          | change (2 ^ (2 + 1)) with 8 in hm4_pow
          | change (2 ^ (3 + 1)) with 16 in hm4_pow]; lia.
      * assert (hprod : m4_2 <= (3 * nu2 + 6) * (3 * nu2 + 7)) by (clear - hm4_pow hp_ub ha3_ub; rewrite <- hm4_pow; nia).
        pose proof (quad_step2a_lt nu2 h10). lia.
  - (* Branch 3: m4_2 < m2_2 *)
    assert (hnu4_cmp : nu2 <= nu4 \/ nu4 < nu2) by (clear; lia).
    destruct hnu4_cmp as [hnu4_ge | hnu4_lt].
    + (* Subbranch 3a: nu2 <= nu4 *)
      assert (hdvd : 2 ^ (nu2 + 1) + m4_2 <= m2_2).
      { rewrite <- hm2_pow, <- hm4_pow.
        apply pow2_dvd_diff_ge; [clear - hnu4_ge; lia | clear; lia | rewrite hm4_pow, hm2_pow; exact hlt]. }
      assert (hquot : 2 ^ (nu4 - nu2) < oa s1).
      { assert (heq_pow : 2 ^ (nu2 + 1) * (2 ^ (nu4 - nu2) * oa s3) = m4_2).
        { rewrite <- hm4_pow, Nat.mul_assoc, <- Nat.pow_add_r.
          replace (nu2 + 1 + (nu4 - nu2)) with (nu4 + 1) by (clear - hnu4_ge; lia). reflexivity. }
        clear - hm2_pow heq_pow hlt ha3_odd Ha3_dm.
        assert (ha3_ge1 : oa s3 >= 1) by lia.
        assert (hd_le : 2 ^ (nu4 - nu2) <= 2 ^ (nu4 - nu2) * oa s3) by nia.
        set (y := 2 ^ (nu4 - nu2) * oa s3) in heq_pow, hd_le; clearbody y.
        clear ha3_odd Ha3_dm ha3_ge1.
        nia. }
      pose proof (pow_two_ge_succ (nu4 - nu2)). lia.
    + (* Subbranch 3b: 1 <= nu4 < nu2 *)
      assert (hdvd : 2 ^ (nu4 + 1) + m4_2 <= m2_2).
      { rewrite <- hm2_pow, <- hm4_pow.
        apply pow2_dvd_diff_ge; [clear; lia | clear - hnu4_lt; lia | rewrite hm4_pow, hm2_pow; exact hlt]. }
      assert (h2a3 : 2 ^ (nu4 + 1) + 2 * oa s3 <= 3 * nu2 + 3 * nu4 + 16) by lia.
      assert (ha3_ub : oa s3 <= 3 * nu2 + 7) by lia.
      assert (hc2 : nu2 = 8 \/ nu2 = 9 \/ nu2 = 10 \/ nu2 >= 11) by (clear - hnu2_ge8; lia).
      destruct hc2 as [h8 | [h9 | [h10 | h11]]].
      * assert (hnu4_le4 : nu4 <= 4).
        { assert (hc4 : nu4 <= 4 \/ nu4 >= 5) by (clear; lia).
          destruct hc4 as [h4 | h5]; [exact h4 | pose proof (pow_two_ge_16 nu4 h5); lia]. }
        rewrite h8 in hm2_ge_pow, h2a3, hb3_sum; change (2 ^ (8 + 1)) with 512 in hm2_ge_pow.
        assert (hc4 : nu4 = 1 \/ nu4 = 2 \/ nu4 = 3 \/ nu4 = 4) by (clear - hnu4_ge1 hnu4_le4; lia).
        destruct hc4 as [-> | [-> | [-> | ->]]];
          [change (2 ^ (1 + 1)) with 4 in hm4_pow, h2a3
          | change (2 ^ (2 + 1)) with 8 in hm4_pow, h2a3
          | change (2 ^ (3 + 1)) with 16 in hm4_pow, h2a3
          | change (2 ^ (4 + 1)) with 32 in hm4_pow, h2a3]; lia.
      * assert (hnu4_le4 : nu4 <= 4).
        { assert (hc4 : nu4 <= 4 \/ nu4 >= 5) by (clear; lia).
          destruct hc4 as [h4 | h5]; [exact h4 | pose proof (pow_two_ge_16 nu4 h5); lia]. }
        rewrite h9 in hm2_ge_pow, h2a3, hb3_sum; change (2 ^ (9 + 1)) with 1024 in hm2_ge_pow.
        assert (hc4 : nu4 = 1 \/ nu4 = 2 \/ nu4 = 3 \/ nu4 = 4) by (clear - hnu4_ge1 hnu4_le4; lia).
        destruct hc4 as [-> | [-> | [-> | ->]]];
          [change (2 ^ (1 + 1)) with 4 in hm4_pow, h2a3
          | change (2 ^ (2 + 1)) with 8 in hm4_pow, h2a3
          | change (2 ^ (3 + 1)) with 16 in hm4_pow, h2a3
          | change (2 ^ (4 + 1)) with 32 in hm4_pow, h2a3]; lia.
      * assert (hnu4_le4 : nu4 <= 4).
        { assert (hc4 : nu4 <= 4 \/ nu4 >= 5) by (clear; lia).
          destruct hc4 as [h4 | h5]; [exact h4 | pose proof (pow_two_ge_16 nu4 h5); lia]. }
        rewrite h10 in hm2_ge_pow, h2a3, hb3_sum; change (2 ^ (10 + 1)) with 2048 in hm2_ge_pow.
        assert (hc4 : nu4 = 1 \/ nu4 = 2 \/ nu4 = 3 \/ nu4 = 4) by (clear - hnu4_ge1 hnu4_le4; lia).
        destruct hc4 as [-> | [-> | [-> | ->]]];
          [change (2 ^ (1 + 1)) with 4 in hm4_pow, h2a3
          | change (2 ^ (2 + 1)) with 8 in hm4_pow, h2a3
          | change (2 ^ (3 + 1)) with 16 in hm4_pow, h2a3
          | change (2 ^ (4 + 1)) with 32 in hm4_pow, h2a3]; lia.
      * assert (hp_ub : 2 ^ (nu4 + 1) <= 6 * nu2 + 11) by lia.
        assert (hrem_ub : m2_2 <= m4_2 + 6 * nu2 + 11) by lia.
        assert (hprod : m4_2 <= (6 * nu2 + 11) * (3 * nu2 + 7)) by (clear - hm4_pow hp_ub ha3_ub; rewrite <- hm4_pow; nia).
        pose proof (quad_step2b_lt nu2 h11) as hq2b.
        clear - hprod hrem_ub hm2_ge_pow hq2b. nia.
Qed.

(* ========================================================================== *)
(* Section 5C: Analytic 1-Step Inverse, Finite Preimage Exhaustion & Nonhalt  *)
(* ========================================================================== *)

Definition candPreimage (s' : OddState) (nu beta : nat) : OddState :=
  let d := 2 - od s' in
  let b := 2 ^ (nu + 1) * oa s' - 2 + beta in
  let c :=
    if nu =? 0 then
      if b mod 4 =? 1 then ob s' - d / 2 else ob s' + d / 2 - 1
    else
      (if ob s' mod 2 =? 0 then ob s' - 2 else ob s') + sigma_true b d + nu in
  let M := c - sigma_true b d - nu in
  let a :=
    if nu =? 0 then
      if b mod 4 =? 1 then oc s' - oa s' - 1 else oc s' + 1 - oa s' - d
    else
      oc s' + 1 + oa s' - 2 * (b / 2 + 1) - 2 * nu -
        (if ((b mod 2 =? 1) && (d =? 2))%bool then 2 else 0) -
        (if M mod 2 =? 0 then 0 else 2) in
  mkOdd a b c d.

Lemma candPreimage_eq (s s' : OddState) (hs : InSdom s) (hr : R_odd s = Some s') :
  candPreimage s' (nu_of s) (ob s mod 2) = s.
Proof.
  pose proof (R_odd_props s s' hs hr) as hp.
  assert (h2m : 2 ^ (nu_of s + 1) * a_next_of s = 2 * (ob s / 2 + 1)).
  { rewrite <- (proj1 (proj2 hp)). exact (proj1 (proj2 (proj2 hp))). }
  clear hp.
  destruct hs as [[ha_odd [hb_ge1 [hc_ge3 [hc_odd hd]]]] hca].
  pose proof (div_mod_2_le (ob s)) as Hb_dm.
  pose proof (div_mod_2_le (oa s)) as Ha_dm.
  pose proof (div_mod_2_le (od s)) as Hd_dm.
  pose proof (div_mod_2_le (a_next_of s)) as Ha'_dm.
  unfold R_odd in hr; cbn zeta in hr.
  destruct (oc s <? sigma_true (ob s) (od s) + nu_of s) eqn:Elt; [discriminate hr |].
  assert (hElt_ge : oc s >= sigma_true (ob s) (od s) + nu_of s) by (clear - Elt; lia); clear Elt.
  set (d' := 2 - od s) in hr.
  assert (hd_rec : 2 - d' = od s) by (unfold d'; clear - hd; lia); clearbody d'.
  destruct (nu_of s =? 0) eqn:Enu0.
  - assert (hnu0 : nu_of s = 0) by (clear - Enu0; lia).
    cbn beta iota zeta in hr; apply some_inj in hr; subst s'.
    unfold candPreimage; cbn zeta; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
    rewrite Enu0; clear Enu0; cbn beta iota.
    assert (hb_rec : 2 ^ (nu_of s + 1) * a_next_of s - 2 + ob s mod 2 = ob s) by (clear - h2m Hb_dm; lia).
    rewrite hb_rec, hd_rec.
    assert (hc_rec :
      (if ob s mod 4 =? 1
       then (if ob s mod 4 =? 1 then oc s + od s / 2 else oc s + 1 - od s / 2) - od s / 2
       else (if ob s mod 4 =? 1 then oc s + od s / 2 else oc s + 1 - od s / 2) + od s / 2 - 1) = oc s)
      by (clear - hc_ge3 hd Hd_dm; destruct (ob s mod 4 =? 1); lia).
    assert (ha_rec :
      (if ob s mod 4 =? 1
       then (if ob s mod 4 =? 1 then oa s + a_next_of s + 1 else oa s + a_next_of s - 1 + od s) - a_next_of s - 1
       else (if ob s mod 4 =? 1 then oa s + a_next_of s + 1 else oa s + a_next_of s - 1 + od s) + 1 - a_next_of s - od s) = oa s)
      by (clear - ha_odd Ha_dm; destruct (ob s mod 4 =? 1); lia).
    rewrite hc_rec, ha_rec.
    destruct s; reflexivity.
  - cbn beta iota zeta in hr; apply some_inj in hr; subst s'.
    unfold candPreimage; cbn zeta; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
    rewrite Enu0; clear Enu0; cbn beta iota.
    assert (hb_rec : 2 ^ (nu_of s + 1) * a_next_of s - 2 + ob s mod 2 = ob s) by (clear - h2m Hb_dm; lia).
    rewrite hb_rec, hd_rec.
    set (M := oc s - sigma_true (ob s) (od s) - nu_of s).
    assert (hM_def : M = oc s - sigma_true (ob s) (od s) - nu_of s) by reflexivity.
    clearbody M.
    pose proof (div_mod_2_le M) as HM_dm.
    assert (hc_rec :
      (if (if M mod 2 =? 0 then M + 2 else M) mod 2 =? 0
       then (if M mod 2 =? 0 then M + 2 else M) - 2
       else (if M mod 2 =? 0 then M + 2 else M)) + sigma_true (ob s) (od s) + nu_of s = oc s).
    { destruct (M mod 2 =? 0) eqn:EM.
      - rewrite add_two_mod2, EM. clear - hM_def hElt_ge. lia.
      - rewrite EM. clear - hM_def hElt_ge. lia. }
    rewrite hc_rec, <- hM_def.
    assert (h2m_ge : 2 * (ob s / 2 + 1) >= a_next_of s).
    { clear - h2m. rewrite <- h2m. pose proof (one_le_pow2 (nu_of s + 1)). nia. }
    assert (ha_rec :
      (2 * (ob s / 2 + 1) - a_next_of s + oa s + 2 * nu_of s +
        (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0) +
        (if M mod 2 =? 0 then 0 else 2) - 1) + 1 + a_next_of s -
        2 * (ob s / 2 + 1) - 2 * nu_of s -
        (if ((ob s mod 2 =? 1) && (od s =? 2))%bool then 2 else 0) -
        (if M mod 2 =? 0 then 0 else 2) = oa s).
    { clear - h2m_ge ha_odd Ha_dm.
      destruct ((ob s mod 2 =? 1) && (od s =? 2))%bool; destruct (M mod 2 =? 0); lia. }
    rewrite ha_rec.
    destruct s; reflexivity.
Qed.

Lemma nu_le_of_R_odd (s s' : OddState) (hs : InSdom s) (hr : R_odd s = Some s') :
  (oc s' <= 15 -> nu_of s <= 4) /\ (oc s' <= 125 -> nu_of s <= 7).
Proof.
  pose proof (R_odd_props s s' hs hr) as [hs' [_ [h2m [_ [_ [_ [_ [_ hz_pos]]]]]]]].
  destruct hs' as [[ha'_odd _] _].
  destruct hs as [[ha_odd _] _].
  pose proof (div_mod_2_le (oa s')) as Ha'_dm.
  pose proof (div_mod_2_le (oa s)) as Ha_dm.
  split.
  - intros hc15.
    assert (hc : nu_of s <= 4 \/ nu_of s >= 5) by (clear; lia).
    destruct hc as [h4 | h5]; [exact h4 |].
    pose proof (hz_pos ltac:(lia)) as hz.
    pose proof (pow_two_ge_16 (nu_of s) h5) as hpow.
    assert (hm_ge : 2 * (ob s / 2 + 1) >= 2 ^ (nu_of s + 1)) by (clear - h2m ha'_odd Ha'_dm; nia).
    assert (h2m_2a : 2 * (ob s / 2 + 1) >= 2 * oa s').
    { clear - h2m h5. rewrite <- h2m. replace (nu_of s + 1) with (1 + nu_of s) by lia.
      rewrite Nat.pow_add_r. change (2 ^ 1) with 2.
      pose proof (one_le_pow2 (nu_of s)). nia. }
    lia.
  - intros hc125.
    assert (hc : nu_of s <= 7 \/ nu_of s >= 8) by (clear; lia).
    destruct hc as [h7 | h8]; [exact h7 |].
    pose proof (hz_pos ltac:(lia)) as hz.
    pose proof (pow2_mono 9 (nu_of s + 1) ltac:(lia)) as hpow.
    change (2 ^ 9) with 512 in hpow.
    assert (hm_ge : 2 * (ob s / 2 + 1) >= 2 ^ (nu_of s + 1)) by (clear - h2m ha'_odd Ha'_dm; nia).
    assert (h2m_2a : 2 * (ob s / 2 + 1) >= 2 * oa s').
    { clear - h2m h8. rewrite <- h2m. replace (nu_of s + 1) with (1 + nu_of s) by lia.
      rewrite Nat.pow_add_r. change (2 ^ 1) with 2.
      pose proof (one_le_pow2 (nu_of s)). nia. }
    lia.
Qed.

Definition oddState_eqb (x y : OddState) : bool :=
  ((oa x =? oa y) && (ob x =? ob y) && (oc x =? oc y) && (od x =? od y))%bool.

Lemma oddState_eqb_iff (x y : OddState) : oddState_eqb x y = true <-> x = y.
Proof.
  destruct x as [a1 b1 c1 d1], y as [a2 b2 c2 d2].
  unfold oddState_eqb; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk.
  split.
  - intro H. assert (a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2) as [-> [-> [-> ->]]] by lia. reflexivity.
  - intro H. inversion H; subst; lia.
Qed.

Definition optOddState_eqb (o1 o2 : option OddState) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => oddState_eqb x y
  | _, _ => false
  end.

Definition validPreimages (s' : OddState) (max_nu : nat) : list OddState :=
  filter (fun s => (bInSdom s && optOddState_eqb (R_odd s) (Some s'))%bool)
    (flat_map (fun nu => List.map (fun beta => candPreimage s' nu beta) [0; 1])
      (seq 0 (max_nu + 1))).

Lemma validPreimages_complete (s s' : OddState) (max_nu : nat)
    (hs : InSdom s) (hr : R_odd s = Some s') (hnu : nu_of s <= max_nu) :
  In s (validPreimages s' max_nu).
Proof.
  unfold validPreimages.
  apply filter_In. split.
  - apply in_flat_map.
    exists (nu_of s). split.
    + apply in_seq. lia.
    + apply in_map_iff.
      exists (ob s mod 2). split; [exact (candPreimage_eq s s' hs hr) |].
      destruct (proj2 (div_mod_2 (ob s))) as [h0 | h1];
        [rewrite h0; left; reflexivity | rewrite h1; right; left; reflexivity].
  - rewrite (proj2 (bInSdom_iff s) hs), hr; cbn [optOddState_eqb].
    rewrite (proj2 (oddState_eqb_iff s' s') eq_refl). reflexivity.
Qed.

Definition isHalt3Bool (s2 : OddState) : bool :=
  (bInSdom s2 &&
   match R_odd s2 with
   | None => false
   | Some s1 =>
     match R_odd s1 with
     | None => false
     | Some s0 => oc s0 <? sigma_true (ob s0) (od s0) + nu_of s0
     end
   end)%bool.

Definition halt3_window : list OddState :=
  filter isHalt3Bool
    (flat_map (fun nu2 =>
      flat_map (fun a1 =>
        flat_map (fun beta2 =>
          flat_map (fun c2 =>
            flat_map (fun a2 =>
              List.map (fun d2 => mkOdd a2 (2 ^ (nu2 + 1) * a1 - 2 + beta2) c2 d2) [0; 2])
            (filter (fun a2 => a2 <=? c2) [1; 3; 5; 7; 9; 11; 13]))
          (filter (fun c2 => ((nu2 <=? c2) && (2 * a1 + c2 <=? nu2 + 11))%bool) [3; 5; 7; 9; 11; 13]))
        [0; 1])
      [1; 3])
    [1; 2; 3; 4; 5; 6; 7]).

Definition w3_list : list OddState :=
  [mkOdd 3 6 3 2; mkOdd 1 7 3 0; mkOdd 5 31 5 0; mkOdd 3 62 7 0;
   mkOdd 3 63 7 2; mkOdd 3 126 7 2; mkOdd 1 127 7 0].

Lemma halt3_window_eq : halt3_window = w3_list.
Proof. vm_compute. reflexivity. Qed.

Definition halt4_window : list OddState :=
  flat_map (fun s2 => validPreimages s2 4) w3_list.

Definition w4_list : list OddState :=
  [mkOdd 1 4 5 0; mkOdd 3 5 61 2; mkOdd 3 5 63 0; mkOdd 5 4 125 0].

Lemma halt4_window_eq : halt4_window = w4_list.
Proof. vm_compute. reflexivity. Qed.

Definition halt5_window : list OddState :=
  flat_map (fun s3 => validPreimages s3 7) w4_list.

Definition w5_list : list OddState :=
  [mkOdd 3 1 3 2; mkOdd 1 2 3 2; mkOdd 9 46 9 0; mkOdd 9 47 9 2].

Lemma halt5_window_eq : halt5_window = w5_list.
Proof. vm_compute. reflexivity. Qed.

Definition halt6_window : list OddState :=
  flat_map (fun s4 => validPreimages s4 4) w5_list.

Lemma w3_list_c_le : forall s, In s w3_list -> oc s <= 15.
Proof.
  intros s Hm; repeat (destruct Hm as [<- | Hm]); try contradiction; cbn [oc]; lia.
Qed.

Lemma w4_list_c_le : forall s, In s w4_list -> oc s <= 125.
Proof.
  intros s Hm; repeat (destruct Hm as [<- | Hm]); try contradiction; cbn [oc]; lia.
Qed.

Lemma w5_list_c_le : forall s, In s w5_list -> oc s <= 15.
Proof.
  intros s Hm; repeat (destruct Hm as [<- | Hm]); try contradiction; cbn [oc]; lia.
Qed.

Lemma halt6_window_eq_nil : halt6_window = [].
Proof. vm_compute. reflexivity. Qed.

Lemma odd_mem_13 {x : nat} (hodd : x mod 2 = 1) (hlo : x >= 1) (hhi : x <= 13) :
  In x [1; 3; 5; 7; 9; 11; 13].
Proof.
  pose proof (div_mod_2_le x).
  assert (hc : x = 1 \/ x = 3 \/ x = 5 \/ x = 7 \/ x = 9 \/ x = 11 \/ x = 13) by lia.
  repeat (destruct hc as [-> | hc]; [cbn; auto 10 |]); subst; cbn; auto 10.
Qed.

Lemma odd_mem_3_13 {x : nat} (hodd : x mod 2 = 1) (hlo : x >= 3) (hhi : x <= 13) :
  In x [3; 5; 7; 9; 11; 13].
Proof.
  pose proof (div_mod_2_le x).
  assert (hc : x = 3 \/ x = 5 \/ x = 7 \/ x = 9 \/ x = 11 \/ x = 13) by lia.
  repeat (destruct hc as [-> | hc]; [cbn; auto 10 |]); subst; cbn; auto 10.
Qed.

Lemma halt5_s2_in_halt3_window (s4 s3 s2 s1 s0 : OddState)
    (hs4 : InSdom s4) (hr4 : R_odd s4 = Some s3) (hr3 : R_odd s3 = Some s2)
    (hr2 : R_odd s2 = Some s1) (hr1 : R_odd s1 = Some s0) (hr0 : R_odd s0 = None) :
  In s2 halt3_window.
Proof.
  pose proof (proj1 (R_odd_props s4 s3 hs4 hr4)) as hs3.
  pose proof (proj1 (R_odd_props s3 s2 hs3 hr3)) as hs2.
  pose proof (R_odd_props s2 s1 hs2 hr2) as [hs1 [_ [hm2_pow _]]].
  pose proof (halt5_nu2_le_7 s4 s3 s2 s1 s0 hs4 hr4 hr3 hr2 hr1 hr0) as hnu2_le7.
  pose proof (halt3_step1_bounds s2 s1 s0 hs2 hr2 hr1 hr0) as [hnu2_ge1 [_ [hb1_fn _]]].
  pose proof (hb1_fn hnu2_le7) as [ha1_le3 [hc2_le15 [h2a1_16 h2a1_nu2]]].
  assert (hnohalt2 : ~ (oc s2 < sigma_true (ob s2) (od s2) + nu_of s2)).
  { intros hlt. rewrite (proj2 (R_odd_halt_iff s2) hlt) in hr2. discriminate hr2. }
  destruct hs2 as [[ha2_odd [hb2_ge1 [hc2_ge3 [hc2_odd hd2]]]] ha2_le_c2].
  destruct hs1 as [[ha1_odd _] _].
  pose proof (div_mod_2_le (oa s1)) as Ha1_dm.
  pose proof (div_mod_2_le (oc s2)) as Hc2_dm.
  pose proof (div_mod_2_le (oa s2)) as Ha2_dm.
  pose proof (div_mod_2_le (ob s2)) as Hb2_dm.
  assert (hc2_le13 : oc s2 <= 13) by (clear - hc2_le15 hc2_odd Hc2_dm h2a1_16 ha1_odd Ha1_dm; lia).
  unfold halt3_window.
  apply filter_In. split.
  - apply in_flat_map. exists (nu_of s2). split.
    + assert (hc : nu_of s2 = 1 \/ nu_of s2 = 2 \/ nu_of s2 = 3 \/ nu_of s2 = 4 \/
                   nu_of s2 = 5 \/ nu_of s2 = 6 \/ nu_of s2 = 7) by (clear - hnu2_ge1 hnu2_le7; lia).
      repeat (destruct hc as [-> | hc]; [cbn; auto 10 |]); rewrite hc; cbn; auto 10.
    + apply in_flat_map. exists (oa s1). split.
      * assert (hc : oa s1 = 1 \/ oa s1 = 3) by (clear - ha1_le3 ha1_odd Ha1_dm; lia).
        destruct hc as [-> | ->]; cbn; auto.
      * apply in_flat_map. exists (ob s2 mod 2). split.
        -- destruct (proj2 (div_mod_2 (ob s2))) as [h0 | h1]; [rewrite h0 | rewrite h1]; cbn; auto.
        -- apply in_flat_map. exists (oc s2). split.
           ++ apply filter_In. split; [exact (odd_mem_3_13 hc2_odd hc2_ge3 hc2_le13) | clear - hnohalt2 h2a1_nu2; lia].
           ++ apply in_flat_map. exists (oa s2). split.
              ** apply filter_In. split;
                   [exact (odd_mem_13 ha2_odd ltac:(clear - ha2_odd Ha2_dm; lia) ltac:(clear - ha2_le_c2 hc2_le13; lia))
                   | clear - ha2_le_c2; lia].
              ** apply in_map_iff. exists (od s2). split.
                 --- assert (hb2_eq : 2 ^ (nu_of s2 + 1) * oa s1 - 2 + ob s2 mod 2 = ob s2)
                       by (clear - hm2_pow Hb2_dm; lia).
                     destruct s2 as [a2 b2 c2 d2]; rewrite ?oa_mk, ?ob_mk, ?oc_mk, ?od_mk in hb2_eq |- *.
                     rewrite hb2_eq. reflexivity.
                 --- destruct hd2 as [-> | ->]; cbn; auto.
  - unfold isHalt3Bool.
    assert (hs2_dom : InSdom s2) by (exact (conj (conj ha2_odd (conj hb2_ge1 (conj hc2_ge3 (conj hc2_odd hd2)))) ha2_le_c2)).
    rewrite (proj2 (bInSdom_iff s2) hs2_dom), hr2, hr1.
    pose proof (proj1 (R_odd_halt_iff s0) hr0) as hh0.
    clear - hh0; lia.
Qed.

Theorem no_halt6 (s5 s4 s3 s2 s1 s0 : OddState)
    (hs5 : InSdom s5) (hr5 : R_odd s5 = Some s4) (hr4 : R_odd s4 = Some s3)
    (hr3 : R_odd s3 = Some s2) (hr2 : R_odd s2 = Some s1)
    (hr1 : R_odd s1 = Some s0) (hr0 : R_odd s0 = None) : False.
Proof.
  pose proof (proj1 (R_odd_props s5 s4 hs5 hr5)) as hs4.
  pose proof (proj1 (R_odd_props s4 s3 hs4 hr4)) as hs3.
  pose proof (halt5_s2_in_halt3_window s4 s3 s2 s1 s0 hs4 hr4 hr3 hr2 hr1 hr0) as hm2.
  rewrite halt3_window_eq in hm2.
  pose proof (w3_list_c_le s2 hm2) as hc2.
  pose proof (proj1 (nu_le_of_R_odd s3 s2 hs3 hr3) hc2) as hnu3.
  assert (hm3 : In s3 halt4_window).
  { unfold halt4_window. apply in_flat_map. exists s2.
    exact (conj hm2 (validPreimages_complete s3 s2 4 hs3 hr3 hnu3)). }
  rewrite halt4_window_eq in hm3.
  pose proof (w4_list_c_le s3 hm3) as hc3.
  pose proof (proj2 (nu_le_of_R_odd s4 s3 hs4 hr4) hc3) as hnu4.
  assert (hm4 : In s4 halt5_window).
  { unfold halt5_window. apply in_flat_map. exists s3.
    exact (conj hm3 (validPreimages_complete s4 s3 7 hs4 hr4 hnu4)). }
  rewrite halt5_window_eq in hm4.
  pose proof (w5_list_c_le s4 hm4) as hc4.
  pose proof (proj1 (nu_le_of_R_odd s5 s4 hs5 hr5) hc4) as hnu5.
  assert (hm5 : In s5 halt6_window).
  { unfold halt6_window. apply in_flat_map. exists s4.
    exact (conj hm4 (validPreimages_complete s5 s4 4 hs5 hr5 hnu5)). }
  rewrite halt6_window_eq_nil in hm5.
  exact hm5.
Qed.

Definition P5 (s : OddState) : Prop :=
  InSdom s /\ exists s1 s2 s3 s4 s5,
    R_odd s = Some s1 /\ R_odd s1 = Some s2 /\ R_odd s2 = Some s3 /\
    R_odd s3 = Some s4 /\ R_odd s4 = Some s5.

Lemma P5_step (s : OddState) (h : P5 s) :
  exists s1, R_odd s = Some s1 /\ P5 s1.
Proof.
  destruct h as [hs [s1 [s2 [s3 [s4 [s5 [hr0 [hr1 [hr2 [hr3 hr4]]]]]]]]]].
  exists s1. split; [exact hr0 |].
  split; [exact (proj1 (R_odd_props s s1 hs hr0)) |].
  destruct (R_odd s5) as [s6 |] eqn:Er5.
  - exists s2, s3, s4, s5, s6. auto.
  - exfalso. exact (no_halt6 s s1 s2 s3 s4 s5 hs hr0 hr1 hr2 hr3 hr4 Er5).
Qed.

Definition s0_odd : OddState := mkOdd 1 1 5 0.

Lemma P5_s0_odd : P5 s0_odd.
Proof.
  split.
  - apply bInSdom_iff. vm_compute. reflexivity.
  - exists (mkOdd 1 5 3 2), (mkOdd 3 4 5 0), (mkOdd 3 6 5 2),
           (mkOdd 1 3 15 0), (mkOdd 1 16 5 2).
    repeat split; vm_compute; reflexivity.
Qed.

Lemma c319_eq_s0_odd :
  c319_sq = (h10B, [SA 1], enc_odd (oa s0_odd) (ob s0_odd) (oc s0_odd) (od s0_odd)).
Proof. reflexivity. Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct init_reaches_c319 as [n0 hinit].
  rewrite c319_eq_s0_odd in hinit.
  eapply multistep_nonhalt; [exact hinit |].
  apply (progress_nonhalt tm
    (fun cfg => exists n s, P5 s /\ cfg = decode_sq n (h10B, [SA 1], enc_odd (oa s) (ob s) (oc s) (od s)))).
  - intros cfg [n [s [hP5 ->]]].
    destruct (P5_step s hP5) as [s' [hr hP5']].
    destruct (sqReachesPlus_to_tm (R_odd_sound s s' (proj1 (proj1 hP5)) hr) n) as [n' hplus].
    exists (decode_sq n' (h10B, [SA 1], enc_odd (oa s') (ob s') (oc s') (od s'))).
    split; [exists n', s'; exact (conj hP5' eq_refl) | exact hplus].
  - exists n0, s0_odd. exact (conj P5_s0_odd eq_refl).
Qed.
