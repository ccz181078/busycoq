(** * 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF — Non-Halting Proof *)

From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN NArith ZArith PArith PeanoNat String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Set Default Goal Selector "!".

Open Scope string_scope.
Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.

Definition tm : TM := TM_from_str "1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF".
Arguments tm _ : simpl never.

Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Local Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Local Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Local Lemma petrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Local Lemma p_to_e {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac fast_steps :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

(* ========================================================================== *)
(* Layer 1: 2-Sided BEC Macro Alphabet & Exact TM Transitions                 *)
(* ========================================================================== *)

Inductive BecMode := hR | hR1 | hR11 | hL.
Inductive BecTokL := T1 | T000 | T100.
Inductive BecTokR := U100 | U1001 | U10011 | U10001.


Fixpoint becLeft (tl : list BecTokL) : side :=
  match tl with
  | [] => const 0
  | T1 :: rest => 1 >> becLeft rest
  | T000 :: rest => 0 >> 0 >> 0 >> 0 >> becLeft rest
  | T100 :: rest => 1 >> 0 >> 0 >> 0 >> becLeft rest
  end.

Fixpoint becRight (tr : list BecTokR) : side :=
  match tr with
  | [] => 1 >> const 0
  | U100 :: rest => 0 >> 1 >> 0 >> 1 >> becRight rest
  | U1001 :: rest => 1 >> 0 >> 1 >> 0 >> 1 >> becRight rest
  | U10011 :: rest => 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> becRight rest
  | U10001 :: rest => 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> becRight rest
  end.

Definition evalBecCfg (m : BecMode) (tl : list BecTokL) (tr : list BecTokR) : Q * tape :=
  match m with
  | hR => becLeft tl <{{A}} (1 >> 0 >> 1 >> becRight tr)
  | hR1 => becLeft tl <{{F}} (0 >> 1 >> 0 >> 1 >> becRight tr)
  | hR11 => becLeft tl <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> becRight tr)
  | hL => (0 >> 0 >> 0 >> becLeft tl) {{E}}> becRight tr
  end.

Local Lemma init_to_bec : c0 -->+ evalBecCfg hL [T100] [].
Proof. unfold c0, tape0, q0, s0, evalBecCfg, becLeft, becRight; cbn [BB62.q0 BB62.s0]; fast_steps. Qed.

Local Lemma step_hR_nil (tr : list BecTokR) :
  evalBecCfg hR [] tr -->+ evalBecCfg hL [T100] tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR_T1 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR (T1 :: tl) tr -->+ evalBecCfg hR1 tl tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR_T000 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR (T000 :: tl) tr -->+ evalBecCfg hL (T100 :: tl) tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR_T100 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR (T100 :: tl) tr -->+ evalBecCfg hR tl (U100 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hR1_nil (tr : list BecTokR) :
  evalBecCfg hR1 [] tr -->+ evalBecCfg hL [T000; T1] tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR1_T1 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR1 (T1 :: tl) tr -->+ evalBecCfg hR11 tl tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR1_T000 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR1 (T000 :: tl) tr -->+ evalBecCfg hL (T000 :: T1 :: tl) tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR1_T100 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR1 (T100 :: tl) tr -->+ evalBecCfg hR tl (U1001 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hR11_nil (tr : list BecTokR) :
  evalBecCfg hR11 [] tr -->+ evalBecCfg hL [T1; T100; T1] tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR11_T1_nil (tr : list BecTokR) :
  evalBecCfg hR11 [T1] tr -->+ evalBecCfg hR [] (U10011 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hR11_T1_T000 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR11 (T1 :: T000 :: tl) tr -->+ evalBecCfg hR1 tl (U10001 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hR11_T000 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR11 (T000 :: tl) tr -->+ evalBecCfg hL (T1 :: T100 :: T1 :: tl) tr.
Proof. unfold evalBecCfg, becLeft; fast_steps. Qed.

Local Lemma step_hR11_T100 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hR11 (T100 :: tl) tr -->+ evalBecCfg hR tl (U10011 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hL_nil (tl : list BecTokL) :
  evalBecCfg hL tl [] -->+ evalBecCfg hR1 tl [].
Proof. unfold evalBecCfg, becRight; fast_steps. Qed.

Local Lemma step_hL_U100 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hL tl (U100 :: tr) -->+ evalBecCfg hL (T000 :: tl) tr.
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hL_U1001 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hL tl (U1001 :: tr) -->+ evalBecCfg hL (T1 :: T100 :: tl) tr.
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hL_U10011 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hL tl (U10011 :: tr) -->+ evalBecCfg hR tl (U10001 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

Local Lemma step_hL_U10001 (tl : list BecTokL) (tr : list BecTokR) :
  evalBecCfg hL tl (U10001 :: tr) -->+ evalBecCfg hR1 tl (U1001 :: tr).
Proof. unfold evalBecCfg, becLeft, becRight; fast_steps. Qed.

(* ========================================================================== *)
(* Layer 2a: 1-Sided Left-Bounce Dictionary, RelT, and Universal Collar       *)
(* ========================================================================== *)

Open Scope N_scope.

Ltac div_lia :=
  Zify.zify; Z.to_euclidean_division_equations; lia.

Local Lemma N_ind_add1 (P : N -> Prop) (H0 : P 0) (Hs : forall n, P n -> P (n + 1)) :
  forall n, P n.
Proof.
  apply N.peano_ind; [exact H0 | intros n IH; rewrite <- N.add_1_r; exact (Hs n IH)].
Qed.

Local Lemma N_strong_ind (P : N -> Prop) (Hs : forall n, (forall m, m < n -> P m) -> P n) :
  forall n, P n.
Proof.
  exact (well_founded_ind N.lt_wf_0 P Hs).
Qed.

Local Lemma pow2_0 : 2 ^ 0 = 1.
Proof. reflexivity. Qed.

Local Lemma pow2_succ (n : N) : 2 ^ (n + 1) = 2 * (2 ^ n).
Proof.
  rewrite N.pow_add_r. change (2 ^ 1) with 2. lia.
Qed.

Local Lemma pow2_pos (n : N) : 0 < 2 ^ n.
Proof.
  induction n as [| n IH] using N_ind_add1.
  - cbn. lia.
  - rewrite pow2_succ. lia.
Qed.

Inductive BecTok1 := Tok0 | TokI | Tok1 | TokB.

Fixpoint decode1 (w : list BecTok1) : list BecTokL :=
  match w with
  | [] => []
  | Tok0 :: xs => T000 :: decode1 xs
  | TokI :: xs => T100 :: decode1 xs
  | Tok1 :: xs => T1 :: decode1 xs
  | TokB :: xs => T1 :: T100 :: decode1 xs
  end.

Local Lemma decode1_append (xs ys : list BecTok1) :
  decode1 (xs ++ ys) = decode1 xs ++ decode1 ys.
Proof.
  induction xs as [| t xs IH]; [reflexivity |].
  destruct t; cbn [app decode1]; rewrite IH; reflexivity.
Qed.

Definition consNorm (t : BecTok1) (xs : list BecTok1) : list BecTok1 :=
  match t, xs with
  | Tok1, TokI :: ys => TokB :: ys
  | _, _ => t :: xs
  end.

Fixpoint coalesce (w : list BecTok1) : list BecTok1 :=
  match w with
  | [] => []
  | t :: xs => consNorm t (coalesce xs)
  end.

Definition consTrim (t : BecTok1) (xs : list BecTok1) : list BecTok1 :=
  match t, xs with
  | Tok0, [] => []
  | _, _ => t :: xs
  end.

Fixpoint trimZero (w : list BecTok1) : list BecTok1 :=
  match w with
  | [] => []
  | t :: xs => consTrim t (trimZero xs)
  end.

Definition norm1 (w : list BecTok1) : list BecTok1 :=
  trimZero (coalesce w).

Local Lemma decode1_consNorm (t : BecTok1) (xs : list BecTok1) :
  decode1 (consNorm t xs) = decode1 (t :: xs).
Proof.
  destruct t; try reflexivity.
  destruct xs as [| u ys]; [reflexivity | destruct u; reflexivity].
Qed.

Local Lemma decode1_coalesce (w : list BecTok1) :
  decode1 (coalesce w) = decode1 w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [coalesce]. rewrite decode1_consNorm.
  destruct t; cbn [decode1]; rewrite IH; reflexivity.
Qed.

Local Lemma becLeft_decode1_consTrim (t : BecTok1) (xs : list BecTok1) :
  becLeft (decode1 (consTrim t xs)) = becLeft (decode1 (t :: xs)).
Proof.
  destruct t; try reflexivity.
  destruct xs as [| u ys]; [| reflexivity].
  cbn [consTrim decode1 becLeft].
  repeat rewrite <- const_unfold. reflexivity.
Qed.

Local Lemma becLeft_decode1_trimZero (w : list BecTok1) :
  becLeft (decode1 (trimZero w)) = becLeft (decode1 w).
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. rewrite becLeft_decode1_consTrim.
  destruct t; cbn [decode1 becLeft]; rewrite IH; reflexivity.
Qed.

Local Lemma becLeft_append_eq {xs ys zs : list BecTokL}
    (h : becLeft ys = becLeft zs) :
  becLeft (xs ++ ys) = becLeft (xs ++ zs).
Proof.
  induction xs as [| t xs IH]; [exact h |].
  destruct t; cbn [app becLeft]; rewrite IH; reflexivity.
Qed.

Local Lemma becLeft_decode1_norm1 (w : list BecTok1) :
  becLeft (decode1 (norm1 w)) = becLeft (decode1 w).
Proof.
  unfold norm1. rewrite becLeft_decode1_trimZero, decode1_coalesce. reflexivity.
Qed.

Local Lemma evalBecCfg_norm1 (m : BecMode) (w : list BecTok1) (tr : list BecTokR) :
  evalBecCfg m (decode1 (norm1 w)) tr = evalBecCfg m (decode1 w) tr.
Proof.
  destruct m; unfold evalBecCfg; rewrite becLeft_decode1_norm1; reflexivity.
Qed.

Inductive TMode := M0 | M1 | M2.

Definition modeOf (j : TMode) : BecMode :=
  match j with
  | M0 => hR
  | M1 => hR1
  | M2 => hR11
  end.

Inductive RelT : TMode -> list BecTok1 -> list BecTok1 -> Prop :=
  | rt_t0_nil : RelT M0 [] [TokI]
  | rt_t0_k0 (w : list BecTok1) : RelT M0 (Tok0 :: w) (TokI :: w)
  | rt_t0_kI {w w' : list BecTok1} : RelT M0 w w' -> RelT M0 (TokI :: w) (Tok0 :: w')
  | rt_t0_kB {w w' : list BecTok1} : RelT M0 w w' -> RelT M0 (TokB :: w) (TokB :: w')
  | rt_t0_k1 {w w' : list BecTok1} : RelT M1 w w' -> RelT M0 (Tok1 :: w) w'
  | rt_t1_nil : RelT M1 [] [Tok0; Tok1]
  | rt_t1_k0 (w : list BecTok1) : RelT M1 (Tok0 :: w) (Tok0 :: Tok1 :: w)
  | rt_t1_kI {w w' : list BecTok1} : RelT M0 w w' -> RelT M1 (TokI :: w) (TokB :: w')
  | rt_t1_kB {w u v v' : list BecTok1} :
      RelT M0 w u -> RelT M0 u v -> RelT M1 v v' -> RelT M1 (TokB :: w) (TokB :: v')
  | rt_t1_k1 {w w' : list BecTok1} : RelT M2 w w' -> RelT M1 (Tok1 :: w) w'
  | rt_t2_nil : RelT M2 [] [TokB; Tok1]
  | rt_t2_k0 (w : list BecTok1) : RelT M2 (Tok0 :: w) (TokB :: Tok1 :: w)
  | rt_t2_kI {w u v v' : list BecTok1} :
      RelT M0 w u -> RelT M0 u v -> RelT M1 v v' -> RelT M2 (TokI :: w) (TokB :: v')
  | rt_t2_k1_nil : RelT M2 [Tok1] [TokB; Tok0; TokB]
  | rt_t2_k1_k0 {w u v : list BecTok1} :
      RelT M1 w u -> RelT M1 u v -> RelT M2 (Tok1 :: Tok0 :: w) (TokB :: v)
  | rt_norm_in {j : TMode} {w w' : list BecTok1} :
      RelT j (norm1 w) w' -> RelT j w w'
  | rt_norm_out {j : TMode} {w w' : list BecTok1} :
      RelT j w w' -> RelT j w (norm1 w').

Local Lemma RelT_sound {j : TMode} {w w' : list BecTok1} (h : RelT j w w') :
  forall tr : list BecTokR,
    evalBecCfg (modeOf j) (decode1 w) tr -->+ evalBecCfg hL (decode1 w') tr.
Proof.
  induction h; intro tr; cbn [modeOf decode1].
  - exact (step_hR_nil tr).
  - exact (step_hR_T000 (decode1 w) tr).
  - exact (ptrans (step_hR_T100 (decode1 w) tr)
      (ptrans (IHh (U100 :: tr)) (step_hL_U100 (decode1 w') tr))).
  - exact (ptrans (step_hR_T1 (T100 :: decode1 w) tr)
      (ptrans (step_hR1_T100 (decode1 w) tr)
        (ptrans (IHh (U1001 :: tr)) (step_hL_U1001 (decode1 w') tr)))).
  - exact (ptrans (step_hR_T1 (decode1 w) tr) (IHh tr)).
  - exact (step_hR1_nil tr).
  - exact (step_hR1_T000 (decode1 w) tr).
  - exact (ptrans (step_hR1_T100 (decode1 w) tr)
      (ptrans (IHh (U1001 :: tr)) (step_hL_U1001 (decode1 w') tr))).
  - exact (ptrans (step_hR1_T1 (T100 :: decode1 w) tr)
      (ptrans (step_hR11_T100 (decode1 w) tr)
        (ptrans (IHh1 (U10011 :: tr))
          (ptrans (step_hL_U10011 (decode1 u) tr)
            (ptrans (IHh2 (U10001 :: tr))
              (ptrans (step_hL_U10001 (decode1 v) tr)
                (ptrans (IHh3 (U1001 :: tr)) (step_hL_U1001 (decode1 v') tr)))))))).
  - exact (ptrans (step_hR1_T1 (decode1 w) tr) (IHh tr)).
  - exact (step_hR11_nil tr).
  - exact (step_hR11_T000 (decode1 w) tr).
  - exact (ptrans (step_hR11_T100 (decode1 w) tr)
      (ptrans (IHh1 (U10011 :: tr))
        (ptrans (step_hL_U10011 (decode1 u) tr)
          (ptrans (IHh2 (U10001 :: tr))
            (ptrans (step_hL_U10001 (decode1 v) tr)
              (ptrans (IHh3 (U1001 :: tr)) (step_hL_U1001 (decode1 v') tr))))))).
  - exact (ptrans (step_hR11_T1_nil tr)
      (ptrans (step_hR_nil (U10011 :: tr))
        (ptrans (step_hL_U10011 [T100] tr)
          (ptrans (step_hR_T100 [] (U10001 :: tr))
            (ptrans (step_hR_nil (U100 :: U10001 :: tr))
              (ptrans (step_hL_U100 [T100] (U10001 :: tr))
                (ptrans (step_hL_U10001 [T000; T100] tr)
                  (ptrans (step_hR1_T000 [T100] (U1001 :: tr))
                    (step_hL_U1001 [T000; T1; T100] tr))))))))).
  - exact (ptrans (step_hR11_T1_T000 (decode1 w) tr)
      (ptrans (IHh1 (U10001 :: tr))
        (ptrans (step_hL_U10001 (decode1 u) tr)
          (ptrans (IHh2 (U1001 :: tr)) (step_hL_U1001 (decode1 v) tr))))).
  - rewrite <- evalBecCfg_norm1. exact (IHh tr).
  - rewrite evalBecCfg_norm1. exact (IHh tr).
Qed.

Definition repB (k : N) : list BecTok1 :=
  match k with
  | N0 => []
  | Npos p => Pos.iter (cons TokB) [] p
  end.

Local Lemma repB_0 : repB 0 = [].
Proof. reflexivity. Qed.

Local Lemma repB_succ (k : N) : repB (k + 1) = TokB :: repB k.
Proof.
  rewrite N.add_1_r.
  destruct k as [| p]; [reflexivity |].
  cbn [N.succ repB]. rewrite Pos.iter_succ. reflexivity.
Qed.

Local Lemma repB_add (m n : N) : repB (m + n) = repB m ++ repB n.
Proof.
  induction m as [| m IH] using N_ind_add1.
  - cbn. reflexivity.
  - replace (m + 1 + n) with ((m + n) + 1) by lia.
    rewrite repB_succ, repB_succ, IH. reflexivity.
Qed.

Inductive RelT0Pow : N -> list BecTok1 -> list BecTok1 -> Prop :=
  | rt0_zero (w : list BecTok1) : RelT0Pow 0 w w
  | rt0_succ {n : N} {w u v : list BecTok1} :
      RelT M0 w u -> RelT0Pow n u v -> RelT0Pow (n + 1) w v.

Local Lemma RelT0Pow_0_inv {w v : list BecTok1} (h : RelT0Pow 0 w v) : v = w.
Proof.
  remember 0 as z eqn:Hz.
  destruct h; [reflexivity | lia].
Qed.

Local Lemma RelT0Pow_succ_inv {n : N} {w v : list BecTok1} (h : RelT0Pow (n + 1) w v) :
  exists u, RelT M0 w u /\ RelT0Pow n u v.
Proof.
  remember (n + 1) as z eqn:Hz.
  destruct h as [w | n0 w u v h1 h2]; [lia |].
  assert (n0 = n) by lia; subst n0.
  exists u; exact (conj h1 h2).
Qed.

Local Lemma RelT0Pow_1_inv {w v : list BecTok1} (h : RelT0Pow 1 w v) : RelT M0 w v.
Proof.
  change 1 with (0 + 1) in h.
  destruct (RelT0Pow_succ_inv h) as [u [h1 h0]].
  rewrite (RelT0Pow_0_inv h0) in *. exact h1.
Qed.

Local Lemma RelT0Pow_2_inv {w v : list BecTok1} (h : RelT0Pow 2 w v) :
  exists u, RelT M0 w u /\ RelT M0 u v.
Proof.
  change 2 with (1 + 1) in h.
  destruct (RelT0Pow_succ_inv h) as [u [h1 h0]].
  exists u; exact (conj h1 (RelT0Pow_1_inv h0)).
Qed.

Local Lemma RelT0Pow_trans {m n : N} {w u v : list BecTok1}
    (h1 : RelT0Pow m w u) (h2 : RelT0Pow n u v) : RelT0Pow (m + n) w v.
Proof.
  induction h1 as [w | m w x u hm _ IH].
  - replace (0 + n) with n by lia. exact h2.
  - replace (m + 1 + n) with ((m + n) + 1) by lia.
    exact (rt0_succ hm (IH h2)).
Qed.

Local Lemma RelT_t0_repB (k : N) {w w' : list BecTok1} (h : RelT M0 w w') :
  RelT M0 (repB k ++ w) (repB k ++ w').
Proof.
  induction k as [| k IH] using N_ind_add1.
  - exact h.
  - rewrite !repB_succ. cbn [app]. exact (rt_t0_kB IH).
Qed.

Local Lemma RelT0Pow_repB (k : N) {n : N} {w w' : list BecTok1} (h : RelT0Pow n w w') :
  RelT0Pow n (repB k ++ w) (repB k ++ w').
Proof.
  induction h as [w | n w u v h1 _ IH].
  - exact (rt0_zero _).
  - exact (rt0_succ (RelT_t0_repB k h1) IH).
Qed.

Local Lemma RelT_t1_repB (k : N) :
  forall {w u v : list BecTok1},
    RelT0Pow (2 * k) w u -> RelT M1 u v ->
    RelT M1 (repB k ++ w) (repB k ++ v).
Proof.
  induction k as [| k IH] using N_ind_add1; intros w u v h0 h1.
  - cbn in h0 |- *. rewrite (RelT0Pow_0_inv h0) in *. exact h1.
  - replace (2 * (k + 1)) with ((2 * k + 1) + 1) in h0 by lia.
    destruct (RelT0Pow_succ_inv h0) as [x1 [ha h0']].
    destruct (RelT0Pow_succ_inv h0') as [x2 [hb hrem]].
    rewrite !repB_succ. cbn [app].
    exact (rt_t1_kB (RelT_t0_repB k ha) (RelT_t0_repB k hb) (IH _ _ _ hrem h1)).
Qed.

Fixpoint leadB (w : list BecTok1) : N :=
  match w with
  | TokB :: xs => leadB xs + 1
  | _ => 0
  end.

Fixpoint dropB (w : list BecTok1) : list BecTok1 :=
  match w with
  | TokB :: xs => dropB xs
  | _ => w
  end.

Local Lemma rep_leadB_dropB (w : list BecTok1) :
  repB (leadB w) ++ dropB w = w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try reflexivity.
  cbn [leadB dropB]. rewrite repB_succ. cbn [app]. rewrite IH. reflexivity.
Qed.

Definition cfgCollar (k_col : N) (tail : list BecTok1) : Q * tape :=
  evalBecCfg hL (decode1 ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ tail)) [].

Local Lemma collar_step (k_col : N) {tail u v v' : list BecTok1}
    (hpow : RelT0Pow (2 * k_col) tail u) (ht1 : RelT M1 u v) (ht0 : RelT M0 v v') :
  cfgCollar k_col tail -->+ cfgCollar (k_col + leadB (norm1 v')) (dropB (norm1 v')).
Proof.
  assert (hz1 : RelT M1 (repB k_col ++ tail) (repB k_col ++ v)) by exact (RelT_t1_repB k_col hpow ht1).
  assert (hz2 : RelT M0 (repB k_col ++ v) (repB k_col ++ v')) by exact (RelT_t0_repB k_col ht0).
  assert (hp1 : RelT M0 (Tok0 :: Tok1 :: (repB k_col ++ tail)) (TokI :: Tok1 :: (repB k_col ++ tail)))
    by exact (rt_t0_k0 _).
  assert (hp2 : RelT M0 (TokI :: Tok1 :: (repB k_col ++ tail)) (Tok0 :: (repB k_col ++ v)))
    by exact (rt_t0_kI (rt_t0_k1 hz1)).
  assert (hp3 : RelT M0 (Tok0 :: (repB k_col ++ v)) (TokI :: (repB k_col ++ v)))
    by exact (rt_t0_k0 _).
  assert (hp4 : RelT M0 (TokI :: (repB k_col ++ v)) (Tok0 :: (repB k_col ++ v')))
    by exact (rt_t0_kI hz2).
  assert (hp5 : RelT M1 (Tok0 :: (repB k_col ++ v')) (Tok0 :: Tok1 :: (repB k_col ++ v')))
    by exact (rt_t1_k0 _).
  assert (hmid : RelT M1 (TokB :: Tok0 :: (repB k_col ++ v)) (TokB :: Tok0 :: Tok1 :: (repB k_col ++ v')))
    by exact (rt_t1_kB hp3 hp4 hp5).
  set (pfx := [TokB; TokB; Tok0; Tok1] ++ repB k_col).
  assert (hfull : RelT M1 (pfx ++ tail) (pfx ++ v')).
  { unfold pfx; rewrite <- !app_assoc; cbn [app].
    exact (rt_t1_kB (rt_t0_kB hp1) (rt_t0_kB hp2) hmid). }
  assert (h1 : cfgCollar k_col tail -->+ evalBecCfg (modeOf M1) (decode1 (pfx ++ tail)) []).
  { unfold cfgCollar, pfx. rewrite <- app_assoc. exact (step_hL_nil _). }
  assert (hreach : cfgCollar k_col tail -->+ evalBecCfg hL (decode1 (pfx ++ v')) [])
    by exact (ptrans h1 (RelT_sound hfull [])).
  assert (heq : evalBecCfg hL (decode1 (pfx ++ v')) [] =
                cfgCollar (k_col + leadB (norm1 v')) (dropB (norm1 v'))).
  { unfold cfgCollar, pfx, evalBecCfg.
    replace ([TokB; TokB; Tok0; Tok1] ++ repB (k_col + leadB (norm1 v')) ++ dropB (norm1 v'))
      with (([TokB; TokB; Tok0; Tok1] ++ repB k_col) ++ norm1 v')
      by (rewrite repB_add, <- !app_assoc, rep_leadB_dropB; reflexivity).
    rewrite !decode1_append.
    rewrite (becLeft_append_eq (eq_sym (becLeft_decode1_norm1 v'))). reflexivity. }
  rewrite <- heq. exact hreach.
Qed.

(* ========================================================================== *)
(* Layer 2b: Canonical L_0 Algebra, Valuations, t0Pow, InC0/InC1 & Branch I   *)
(* ========================================================================== *)

Fixpoint noK1 (w : list BecTok1) : bool :=
  match w with
  | [] => true
  | Tok1 :: _ => false
  | _ :: xs => noK1 xs
  end.

Fixpoint hasI (w : list BecTok1) : bool :=
  match w with
  | [] => false
  | TokI :: _ => true
  | _ :: xs => hasI xs
  end.

Definition notHeadI (w : list BecTok1) : bool :=
  match w with
  | TokI :: _ => false
  | _ => true
  end.

Fixpoint noTrailZero (w : list BecTok1) : bool :=
  match w with
  | [] => true
  | [Tok0] => false
  | _ :: xs => noTrailZero xs
  end.

Fixpoint countB (w : list BecTok1) : N :=
  match w with
  | [] => 0
  | TokB :: xs => countB xs + 1
  | _ :: xs => countB xs
  end.

Fixpoint evalPhi (cB : N) (w : list BecTok1) : N :=
  match w with
  | [] => 0
  | Tok0 :: xs => 2 * evalPhi cB xs
  | TokI :: xs => 1 + 2 * evalPhi cB xs
  | TokB :: xs => cB + evalPhi cB xs
  | Tok1 :: xs => evalPhi cB xs
  end.

Local Lemma conservation_22 (w : list BecTok1) :
  11 * evalPhi 2 w = 10 * evalPhi 0 w + evalPhi 22 w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; cbn [evalPhi]; lia.
Qed.

Local Lemma coalesce_eq_of_noK1 {w : list BecTok1} (h : noK1 w = true) :
  coalesce w = w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h; cbn [coalesce]; rewrite (IH h); reflexivity.
Qed.

Local Lemma noK1_trimZero {w : list BecTok1} (h : noK1 w = true) :
  noK1 (trimZero w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - specialize (IH h). cbn [trimZero].
    destruct (trimZero xs); [reflexivity | exact IH].
  - exact (IH h).
  - exact (IH h).
Qed.

Local Lemma noK1_norm1 {w : list BecTok1} (h : noK1 w = true) :
  noK1 (norm1 w) = true.
Proof.
  unfold norm1. rewrite (coalesce_eq_of_noK1 h). exact (noK1_trimZero h).
Qed.

Local Lemma noK1_dropB {w : list BecTok1} (h : noK1 w = true) :
  noK1 (dropB w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; [exact h | exact h | exact h | cbn [noK1] in h; exact (IH h)].
Qed.

Local Lemma notHeadB_dropB (w : list BecTok1) :
  forall rest, dropB w <> TokB :: rest.
Proof.
  induction w as [| t xs IH]; [intros rest H; discriminate H |].
  destruct t; try (intros rest H; discriminate H).
  exact IH.
Qed.

Local Lemma noTrailZero_consTrim (t : BecTok1) (xs : list BecTok1)
    (h : noTrailZero xs = true) : noTrailZero (consTrim t xs) = true.
Proof.
  destruct xs as [| u ys]; destruct t; try reflexivity; exact h.
Qed.

Local Lemma noTrailZero_trimZero (w : list BecTok1) :
  noTrailZero (trimZero w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. exact (noTrailZero_consTrim t (trimZero xs) IH).
Qed.

Local Lemma noTrailZero_norm1 (w : list BecTok1) :
  noTrailZero (norm1 w) = true.
Proof.
  exact (noTrailZero_trimZero (coalesce w)).
Qed.

Local Lemma noTrailZero_dropB {w : list BecTok1} (h : noTrailZero w = true) :
  noTrailZero (dropB w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try exact h.
  cbn [dropB]. apply IH. destruct xs; [reflexivity | exact h].
Qed.

Local Lemma evalPhi_consTrim (cB : N) (t : BecTok1) (xs : list BecTok1) :
  evalPhi cB (consTrim t xs) = evalPhi cB (t :: xs).
Proof.
  destruct t; destruct xs; reflexivity.
Qed.

Local Lemma evalPhi_trimZero (cB : N) (w : list BecTok1) :
  evalPhi cB (trimZero w) = evalPhi cB w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. rewrite evalPhi_consTrim.
  destruct t; cbn [evalPhi]; rewrite IH; reflexivity.
Qed.

Local Lemma evalPhi_norm1_of_noK1 (cB : N) {w : list BecTok1} (h : noK1 w = true) :
  evalPhi cB (norm1 w) = evalPhi cB w.
Proof.
  unfold norm1. rewrite (coalesce_eq_of_noK1 h), evalPhi_trimZero. reflexivity.
Qed.

Local Lemma evalPhi_leadB_dropB (cB : N) (w : list BecTok1) :
  evalPhi cB w = cB * leadB w + evalPhi cB (dropB w).
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; try (cbn [leadB dropB]; lia).
  cbn [leadB dropB evalPhi]. rewrite IH. lia.
Qed.

Local Lemma hasI_consTrim (t : BecTok1) (xs : list BecTok1) :
  hasI (consTrim t xs) = hasI (t :: xs).
Proof.
  destruct t; destruct xs; reflexivity.
Qed.

Local Lemma hasI_trimZero (w : list BecTok1) : hasI (trimZero w) = hasI w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. rewrite hasI_consTrim.
  destruct t; cbn [hasI]; try reflexivity; exact IH.
Qed.

Local Lemma trimZero_ne_nil_of_hasI {w : list BecTok1} (h : hasI w = true) :
  trimZero w <> [].
Proof.
  intros Hemp. pose proof (hasI_trimZero w) as H1.
  rewrite Hemp, h in H1. discriminate H1.
Qed.

Local Lemma notHeadI_trimZero {w : list BecTok1}
    (h : notHeadI w = true) (hI : hasI w = true) :
  notHeadI (trimZero w) = true.
Proof.
  destruct w as [| t xs]; [discriminate hI |].
  destruct t; [| discriminate h | reflexivity | reflexivity].
  cbn [hasI] in hI. pose proof (trimZero_ne_nil_of_hasI hI) as Hne.
  cbn [trimZero]. destruct (trimZero xs); [contradiction | reflexivity].
Qed.

Local Lemma hasI_of_evalPhi_zero_pos {w : list BecTok1}
    (hno : noK1 w = true) (hw : 0 < evalPhi 0 w) : hasI w = true.
Proof.
  induction w as [| t xs IH]; [cbn in hw; lia |].
  destruct t.
  - cbn [noK1] in hno. cbn [evalPhi] in hw. apply (IH hno); lia.
  - reflexivity.
  - discriminate hno.
  - cbn [noK1] in hno. cbn [evalPhi] in hw. apply (IH hno); lia.
Qed.

Fixpoint t0One (w : list BecTok1) : list BecTok1 :=
  match w with
  | [] => [TokI]
  | Tok0 :: xs => TokI :: xs
  | TokI :: xs => Tok0 :: t0One xs
  | TokB :: xs => TokB :: t0One xs
  | Tok1 :: xs => Tok1 :: xs
  end.

Local Lemma t0One_ne_nil (w : list BecTok1) : t0One w <> [].
Proof.
  destruct w as [| t xs]; [discriminate | destruct t; discriminate].
Qed.

Local Lemma RelT_t0One {w : list BecTok1} (h : noK1 w = true) :
  RelT M0 w (t0One w).
Proof.
  induction w as [| t xs IH]; [exact rt_t0_nil |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - exact (rt_t0_k0 xs).
  - exact (rt_t0_kI (IH h)).
  - exact (rt_t0_kB (IH h)).
Qed.

Local Lemma noK1_t0One {w : list BecTok1} (h : noK1 w = true) :
  noK1 (t0One w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h; [exact h | exact (IH h) | exact (IH h)].
Qed.

Local Lemma noTrailZero_t0One {w : list BecTok1}
    (h : noK1 w = true) (htz : noTrailZero w = true) :
  noTrailZero (t0One w) = true.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - destruct xs; [discriminate htz | exact htz].
  - assert (htz' : noTrailZero xs = true) by (destruct xs; [reflexivity | exact htz]).
    specialize (IH h htz'). pose proof (t0One_ne_nil xs) as Hne.
    cbn [t0One]. destruct (t0One xs); [contradiction | exact IH].
  - assert (htz' : noTrailZero xs = true) by (destruct xs; [reflexivity | exact htz]).
    specialize (IH h htz'). pose proof (t0One_ne_nil xs) as Hne.
    cbn [t0One]. destruct (t0One xs); [contradiction | exact IH].
Qed.

Local Lemma countB_t0One {w : list BecTok1} (h : noK1 w = true) :
  countB (t0One w) = countB w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - reflexivity.
  - exact (IH h).
  - cbn [t0One countB]. rewrite (IH h). reflexivity.
Qed.

Local Lemma evalPhi_t0One (cB : N) {w : list BecTok1} (h : noK1 w = true) :
  evalPhi cB (t0One w) = evalPhi cB w + 1.
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; try discriminate h; cbn [noK1] in h; cbn [t0One evalPhi]; try rewrite (IH h); lia.
Qed.

Local Lemma evalPhi_zero_t0One {w : list BecTok1} (h : noK1 w = true) :
  evalPhi 0 (t0One w) = evalPhi 0 w + 1.
Proof. exact (evalPhi_t0One 0 h). Qed.

Local Lemma evalPhi_le_t0One (cB : N) {w : list BecTok1} (h : noK1 w = true) :
  evalPhi cB (t0One w) <= evalPhi cB w + 1.
Proof. rewrite (evalPhi_t0One cB h); lia. Qed.

Definition t0Pow (n : N) (w : list BecTok1) : list BecTok1 :=
  match n with
  | N0 => w
  | Npos p => Pos.iter t0One w p
  end.

Local Lemma t0Pow_0 (w : list BecTok1) : t0Pow 0 w = w.
Proof. reflexivity. Qed.

Local Lemma t0Pow_succ_out (n : N) (w : list BecTok1) :
  t0Pow (n + 1) w = t0One (t0Pow n w).
Proof.
  rewrite N.add_1_r.
  destruct n as [| p]; [reflexivity |].
  cbn [N.succ t0Pow]. rewrite Pos.iter_succ. reflexivity.
Qed.

Local Lemma t0Pow_succ (n : N) (w : list BecTok1) :
  t0Pow (n + 1) w = t0Pow n (t0One w).
Proof.
  induction n as [| n IH] using N_ind_add1.
  - reflexivity.
  - rewrite (t0Pow_succ_out (n + 1) w), IH, <- t0Pow_succ_out. reflexivity.
Qed.

Local Lemma RelT0Pow_t0Pow (n : N) :
  forall {w : list BecTok1}, noK1 w = true -> RelT0Pow n w (t0Pow n w).
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h.
  - exact (rt0_zero w).
  - rewrite t0Pow_succ. exact (rt0_succ (RelT_t0One h) (IH _ (noK1_t0One h))).
Qed.

Local Lemma noK1_t0Pow (n : N) :
  forall {w : list BecTok1}, noK1 w = true -> noK1 (t0Pow n w) = true.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h; [exact h |].
  rewrite t0Pow_succ. exact (IH _ (noK1_t0One h)).
Qed.

Local Lemma noTrailZero_t0Pow (n : N) :
  forall {w : list BecTok1}, noK1 w = true -> noTrailZero w = true -> noTrailZero (t0Pow n w) = true.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h htz; [exact htz |].
  rewrite t0Pow_succ. exact (IH _ (noK1_t0One h) (noTrailZero_t0One h htz)).
Qed.

Local Lemma countB_t0Pow (n : N) :
  forall {w : list BecTok1}, noK1 w = true -> countB (t0Pow n w) = countB w.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h; [reflexivity |].
  rewrite t0Pow_succ, (IH _ (noK1_t0One h)), (countB_t0One h). reflexivity.
Qed.

Local Lemma evalPhi_t0Pow (cB n : N) :
  forall {w : list BecTok1}, noK1 w = true -> evalPhi cB (t0Pow n w) = evalPhi cB w + n.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h; [cbn; lia |].
  rewrite t0Pow_succ, (IH _ (noK1_t0One h)), (evalPhi_t0One cB h). lia.
Qed.

Local Lemma evalPhi_zero_t0Pow (n : N) {w : list BecTok1} (h : noK1 w = true) :
  evalPhi 0 (t0Pow n w) = evalPhi 0 w + n.
Proof. exact (evalPhi_t0Pow 0 n h). Qed.

Local Lemma evalPhi_le_t0Pow (cB n : N) {w : list BecTok1} (h : noK1 w = true) :
  evalPhi cB (t0Pow n w) <= evalPhi cB w + n.
Proof. rewrite (evalPhi_t0Pow cB n h); lia. Qed.

Definition InC0 (k_col : N) (tail : list BecTok1) : Prop :=
  64 <= k_col /\ noK1 tail = true /\ noTrailZero tail = true /\
  2 * evalPhi 0 tail < 10 * k_col /\ evalPhi 22 tail < 101 * k_col.

Definition InC1 (k_col : N) (tail : list BecTok1) : Prop :=
  64 <= k_col /\ exists M : list BecTok1,
    tail = TokI :: Tok1 :: M /\ noK1 M = true /\ noTrailZero M = true /\
    notHeadI M = true /\ hasI M = true /\
    2 * evalPhi 0 M < 7 * k_col /\ evalPhi 22 M < 52 * k_col.

Definition InvCfg (c : Q * tape) : Prop :=
  exists k_col tail, c = cfgCollar k_col tail /\ (InC0 k_col tail \/ InC1 k_col tail).

Local Lemma coalesce_repB_append (m : N) (v : list BecTok1) :
  coalesce (repB m ++ v) = repB m ++ coalesce v.
Proof.
  induction m as [| m IH] using N_ind_add1; [reflexivity |].
  rewrite !repB_succ. cbn [app coalesce consNorm]. rewrite IH. reflexivity.
Qed.

Local Lemma trimZero_repB_append (m : N) (v : list BecTok1) :
  trimZero (repB m ++ v) = repB m ++ trimZero v.
Proof.
  induction m as [| m IH] using N_ind_add1; [reflexivity |].
  rewrite !repB_succ. cbn [app trimZero consTrim]. rewrite IH. reflexivity.
Qed.

Local Lemma leadB_repB_append (m : N) (v : list BecTok1) :
  leadB (repB m ++ v) = m + leadB v.
Proof.
  induction m as [| m IH] using N_ind_add1; [cbn; lia |].
  rewrite repB_succ. cbn [app leadB]. rewrite IH. lia.
Qed.

Local Lemma dropB_repB_append (m : N) (v : list BecTok1) :
  dropB (repB m ++ v) = dropB v.
Proof.
  induction m as [| m IH] using N_ind_add1; [reflexivity |].
  rewrite repB_succ. cbn [app dropB]. exact IH.
Qed.

Local Lemma trimZero_i1_of_hasI {M : list BecTok1} (hI : hasI M = true) :
  trimZero (TokI :: Tok1 :: M) = TokI :: Tok1 :: trimZero M.
Proof.
  pose proof (trimZero_ne_nil_of_hasI hI) as Hne.
  cbn [trimZero]. destruct (trimZero M); [contradiction | reflexivity].
Qed.

Local Lemma branch1_inner :
  forall (b : N) (z : list BecTok1),
    countB z = b -> noK1 z = true -> 0 < evalPhi 0 z ->
    exists v v' : list BecTok1,
      RelT M1 z v /\ RelT M0 v v' /\
      (exists m : N, exists rw : list BecTok1,
        coalesce v' = repB m ++ rw /\
        ((noK1 rw = true /\ 2 * evalPhi 0 rw <= evalPhi 0 z + 2 * m + 1 /\
            2 * evalPhi 22 rw + 20 * m <= evalPhi 22 z + 88) \/
         (exists M : list BecTok1,
            rw = TokI :: Tok1 :: M /\ noK1 M = true /\ notHeadI M = true /\ hasI M = true /\
            2 * evalPhi 0 M = evalPhi 0 z + 2 * m /\
            2 * evalPhi 22 M + 20 * m <= evalPhi 22 z))).
Proof.
  induction b as [b IH] using N_strong_ind.
  intros z hb hno hpos.
  destruct z as [| t M]; [cbn in hpos; lia |].
  destruct t.
  - (* Tok0 *)
    cbn [noK1] in hno.
    destruct M as [| u M']; [cbn in hpos; lia |].
    destruct u.
    + (* Tok0 :: Tok0 :: M' *)
      assert (hno' : noK1 M' = true) by exact hno.
      assert (hIM : hasI (Tok0 :: M') = true).
      { apply (hasI_of_evalPhi_zero_pos hno). cbn [evalPhi] in hpos |- *. lia. }
      exists (Tok0 :: Tok1 :: Tok0 :: M'), (TokI :: Tok1 :: Tok0 :: M').
      refine (conj (rt_t1_k0 _) (conj (rt_t0_k0 _) _)).
      exists 0, (TokI :: Tok1 :: Tok0 :: M'). split.
      * cbn [coalesce consNorm repB app]. rewrite (coalesce_eq_of_noK1 hno'). reflexivity.
      * right. exists (Tok0 :: M').
        refine (conj eq_refl (conj hno (conj eq_refl (conj hIM _)))).
        cbn [evalPhi]; split; lia.
    + (* Tok0 :: TokI :: M' *)
      cbn [noK1] in hno.
      exists (Tok0 :: Tok1 :: TokI :: M'), (TokI :: Tok1 :: TokI :: M').
      refine (conj (rt_t1_k0 _) (conj (rt_t0_k0 _) _)).
      exists 0, (TokI :: TokB :: M'). split.
      * cbn [coalesce consNorm repB app]. rewrite (coalesce_eq_of_noK1 hno). reflexivity.
      * left. refine (conj hno _); cbn [evalPhi]; split; lia.
    + (* Tok0 :: Tok1 *)
      discriminate hno.
    + (* Tok0 :: TokB :: M' *)
      cbn [noK1] in hno.
      assert (hIM : hasI (TokB :: M') = true).
      { apply (hasI_of_evalPhi_zero_pos hno). cbn [evalPhi] in hpos |- *. lia. }
      exists (Tok0 :: Tok1 :: TokB :: M'), (TokI :: Tok1 :: TokB :: M').
      refine (conj (rt_t1_k0 _) (conj (rt_t0_k0 _) _)).
      exists 0, (TokI :: Tok1 :: TokB :: M'). split.
      * cbn [coalesce consNorm repB app]. rewrite (coalesce_eq_of_noK1 hno). reflexivity.
      * right. exists (TokB :: M').
        refine (conj eq_refl (conj hno (conj eq_refl (conj hIM _)))).
        cbn [evalPhi]; split; lia.
  - (* TokI *)
    cbn [noK1] in hno.
    pose proof (noK1_t0Pow 2 hno) as hno2.
    exists (TokB :: t0One M), (TokB :: t0Pow 2 M).
    refine (conj (rt_t1_kI (RelT_t0One hno)) (conj (rt_t0_kB (RelT_t0One (noK1_t0One hno))) _)).
    exists 1, (t0Pow 2 M). split.
    + cbn [coalesce consNorm repB app]. rewrite (coalesce_eq_of_noK1 hno2). reflexivity.
    + left. refine (conj hno2 _).
      pose proof (evalPhi_zero_t0Pow 2 hno) as hw.
      pose proof (evalPhi_le_t0Pow 22 2 hno) as hp.
      cbn [evalPhi] in *; split; lia.
  - (* Tok1 *)
    discriminate hno.
  - (* TokB *)
    cbn [noK1 countB] in hno, hb.
    assert (hb' : countB (t0Pow 2 M) < b) by (rewrite (countB_t0Pow 2 hno); lia).
    assert (hpos' : 0 < evalPhi 0 (t0Pow 2 M)) by (rewrite (evalPhi_zero_t0Pow 2 hno); lia).
    destruct (IH (countB (t0Pow 2 M)) hb' (t0Pow 2 M) eq_refl (noK1_t0Pow 2 hno) hpos')
      as [v0 [v0' [ht1 [ht0 [m [rw [hv0' hcases]]]]]]].
    exists (TokB :: v0), (TokB :: v0').
    refine (conj (rt_t1_kB (RelT_t0One hno) (RelT_t0One (noK1_t0One hno)) ht1)
                 (conj (rt_t0_kB ht0) _)).
    exists (m + 1), rw. split.
    + rewrite repB_succ. cbn [coalesce consNorm app]. rewrite hv0'. reflexivity.
    + pose proof (evalPhi_zero_t0Pow 2 hno) as hw2.
      pose proof (evalPhi_le_t0Pow 22 2 hno) as hp2.
      cbn [evalPhi] in *.
      destruct hcases as [[hnoR [hwR hpR]] | [M0 [hR [hnoM [hnhM [hIM [hwM hpM]]]]]]].
      * left; refine (conj hnoR _); split; lia.
      * right; exists M0; refine (conj hR (conj hnoM (conj hnhM (conj hIM _)))); split; lia.
Qed.

Local Lemma branch1_step {k_col : N} {tail : list BecTok1} (h0 : InC0 k_col tail) :
  exists k_col' tail', cfgCollar k_col tail -->+ cfgCollar k_col' tail' /\
    (InC0 k_col' tail' \/ InC1 k_col' tail').
Proof.
  destruct h0 as [hK [hno [_htz [hw hp]]]].
  pose proof (RelT0Pow_t0Pow (2 * k_col) hno) as hpow.
  pose proof (noK1_t0Pow (2 * k_col) hno) as hnoZ.
  pose proof (evalPhi_zero_t0Pow (2 * k_col) hno) as hwZ.
  pose proof (evalPhi_le_t0Pow 22 (2 * k_col) hno) as hpZ.
  assert (hposZ : 0 < evalPhi 0 (t0Pow (2 * k_col) tail)) by lia.
  destruct (branch1_inner (countB (t0Pow (2 * k_col) tail)) (t0Pow (2 * k_col) tail) eq_refl hnoZ hposZ)
    as [v [v' [ht1 [ht0 [m [rw [hcoal hcases]]]]]]].
  pose proof (collar_step k_col hpow ht1 ht0) as hstep.
  assert (hnorm : norm1 v' = repB m ++ trimZero rw).
  { unfold norm1. rewrite hcoal, trimZero_repB_append. reflexivity. }
  rewrite hnorm, leadB_repB_append, dropB_repB_append in hstep.
  destruct hcases as [[hnoR [hwR hpR]] | [M [hR [hnoM [hnhM [hIM [hwM hpM]]]]]]].
  - exists (k_col + (m + leadB (trimZero rw))), (dropB (trimZero rw)).
    refine (conj hstep (or_introl _)).
    pose proof (noK1_trimZero hnoR) as hnoR'.
    pose proof (noTrailZero_trimZero rw) as htzR'.
    pose proof (evalPhi_trimZero 0 rw) as hw_tr.
    pose proof (evalPhi_trimZero 22 rw) as hp_tr.
    pose proof (evalPhi_leadB_dropB 0 (trimZero rw)) as hw_dr.
    pose proof (evalPhi_leadB_dropB 22 (trimZero rw)) as hp_dr.
    unfold InC0. refine (conj _ (conj (noK1_dropB hnoR') (conj (noTrailZero_dropB htzR') _))); lia.
  - subst rw. rewrite (trimZero_i1_of_hasI hIM) in hstep.
    cbn [leadB dropB] in hstep.
    replace (k_col + (m + 0)) with (k_col + m) in hstep by lia.
    exists (k_col + m), (TokI :: Tok1 :: trimZero M).
    refine (conj hstep (or_intror _)).
    pose proof (evalPhi_trimZero 0 M) as hw_tr.
    pose proof (evalPhi_trimZero 22 M) as hp_tr.
    assert (hIM_tr : hasI (trimZero M) = true) by (rewrite hasI_trimZero; exact hIM).
    unfold InC1. split; [lia |].
    exists (trimZero M).
    refine (conj eq_refl (conj (noK1_trimZero hnoM) (conj (noTrailZero_trimZero M)
      (conj (notHeadI_trimZero hnhM hIM) (conj hIM_tr _))))); lia.
Qed.

(* ========================================================================== *)
(* Layer 2c: Verified Fuel-Bounded execT Evaluator & 67-Bounce Entry          *)
(* ========================================================================== *)

Local Lemma RelT0Pow_norm_out {n : N} {w v : list BecTok1}
    (hn : 0 < n) (h : RelT0Pow n w v) : RelT0Pow n w (norm1 v).
Proof.
  induction h as [w | m w u v h1 hrem IH].
  - lia.
  - destruct (N.eq_dec m 0) as [Hm0 | Hm0].
    + subst m. rewrite (RelT0Pow_0_inv hrem) in *.
      exact (rt0_succ (rt_norm_out h1) (rt0_zero _)).
    + exact (rt0_succ h1 (IH ltac:(lia))).
Qed.

Local Lemma RelT0Pow_bit {q : N} {w w' : list BecTok1} (h : RelT0Pow q w w') :
  RelT0Pow (2 * q) (Tok0 :: w) (Tok0 :: w') /\
  RelT0Pow (2 * q + 1) (Tok0 :: w) (TokI :: w') /\
  RelT0Pow (2 * q) (TokI :: w) (TokI :: w').
Proof.
  induction h as [w | r w u w' h1 _ [ih0e [ih0o _]]].
  - exact (conj (rt0_zero _) (conj (rt0_succ (rt_t0_k0 w) (rt0_zero _)) (rt0_zero _))).
  - assert (hIo : RelT0Pow (2 * r + 1) (TokI :: w) (Tok0 :: w'))
      by exact (rt0_succ (rt_t0_kI h1) ih0e).
    replace (2 * (r + 1)) with ((2 * r + 1) + 1) by lia.
    replace ((2 * r + 1 + 1) + 1) with (((2 * r + 1) + 1) + 1) by lia.
    refine (conj (rt0_succ (rt_t0_k0 w) hIo)
      (conj (rt0_succ (rt_t0_k0 w) (rt0_succ (rt_t0_kI h1) ih0o))
            (rt0_succ (rt_t0_kI h1) ih0o))).
Qed.

Local Lemma RelT0Pow_kI_odd {r : N} {w w' : list BecTok1}
    (h : RelT0Pow (r + 1) w w') : RelT0Pow (2 * r + 1) (TokI :: w) (Tok0 :: w').
Proof.
  destruct (RelT0Pow_succ_inv h) as [u [h1 hrem]].
  exact (rt0_succ (rt_t0_kI h1) (proj1 (RelT0Pow_bit hrem))).
Qed.

Fixpoint binWord (fuel : nat) (n : N) : option (list BecTok1) :=
  if n =? 0 then Some []
  else match fuel with
  | O => None
  | S fuel' =>
    let bt := if (n mod 2) =? 1 then TokI else Tok0 in
    match binWord fuel' (n / 2) with
    | None => None
    | Some ws => Some (bt :: ws)
    end
  end.

Local Lemma binWord_sound :
  forall (fuel : nat) (n : N) (ws : list BecTok1),
    binWord fuel n = Some ws -> RelT0Pow n [] ws.
Proof.
  induction fuel as [| fuel IH]; intros n ws h; cbn [binWord] in h.
  - destruct (n =? 0) eqn:En; [injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero []) | discriminate].
  - destruct (n =? 0) eqn:En.
    + injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero []).
    + apply N.eqb_neq in En.
      destruct (binWord fuel (n / 2)) as [qs |] eqn:Hbw; [| discriminate].
      specialize (IH (n / 2) qs Hbw).
      destruct ((n mod 2) =? 1) eqn:Emod; injection h as <-.
      * apply N.eqb_eq in Emod.
        assert (Hn : n = 2 * (n / 2) + 1) by div_lia.
        rewrite Hn. exact (rt0_succ rt_t0_nil (proj2 (proj2 (RelT0Pow_bit IH)))).
      * apply N.eqb_neq in Emod.
        assert (Hmod0 : n mod 2 = 0) by div_lia.
        assert (Hqpos : 1 <= n / 2) by div_lia.
        set (k := (n / 2) - 1).
        assert (Hq : n / 2 = k + 1) by (unfold k; lia).
        rewrite Hq in IH.
        assert (Hn : n = (2 * k + 1) + 1) by (unfold k; div_lia).
        rewrite Hn. exact (rt0_succ rt_t0_nil (RelT0Pow_kI_odd IH)).
Qed.

Fixpoint splitLeadB (acc : N) (w : list BecTok1) : N * list BecTok1 :=
  match w with
  | TokB :: xs => splitLeadB (acc + 1) xs
  | _ => (acc, w)
  end.

Local Lemma splitLeadB_spec :
  forall (acc : N) (xs : list BecTok1),
    splitLeadB acc xs = (acc + leadB xs, dropB xs).
Proof.
  intros acc xs; revert acc.
  induction xs as [| t xs IH]; intro acc; [cbn; f_equal; lia |].
  destruct t; try (cbn; f_equal; lia).
  cbn [splitLeadB leadB dropB]. rewrite IH. f_equal; lia.
Qed.

Fixpoint execT (fuel : nat) (mode : nat) (n : N) (w : list BecTok1) : option (list BecTok1) :=
  match fuel with
  | O => None
  | S fuel' =>
    match mode with
    | O =>
      if n =? 0 then Some w
      else match w with
      | [] => binWord 64%nat n
      | TokB :: xs =>
        let '(k, rest) := splitLeadB 1 xs in
        match execT fuel' 0%nat n rest with
        | None => None
        | Some ys => Some (repB k ++ ys)
        end
      | Tok0 :: xs =>
        let bt := if (n mod 2) =? 1 then TokI else Tok0 in
        match execT fuel' 0%nat (n / 2) xs with
        | None => None
        | Some ys => Some (bt :: ys)
        end
      | TokI :: xs =>
        if (n mod 2) =? 0 then
          match execT fuel' 0%nat (n / 2) xs with
          | None => None
          | Some ys => Some (TokI :: ys)
          end
        else
          match execT fuel' 0%nat ((n / 2) + 1) xs with
          | None => None
          | Some ys => Some (Tok0 :: ys)
          end
      | Tok1 :: xs =>
        match execT fuel' 1%nat 0 xs with
        | None => None
        | Some xs' => execT fuel' 0%nat (n - 1) xs'
        end
      end
    | S O =>
      match w with
      | [] => Some [Tok0; Tok1]
      | Tok0 :: xs => Some (norm1 (Tok0 :: Tok1 :: xs))
      | TokI :: xs =>
        match execT fuel' 0%nat 1 xs with
        | None => None
        | Some ys => Some (norm1 (TokB :: ys))
        end
      | TokB :: xs =>
        let '(k, rest) := splitLeadB 1 xs in
        match execT fuel' 0%nat (2 * k) rest with
        | None => None
        | Some u =>
          match execT fuel' 1%nat 0 (norm1 u) with
          | None => None
          | Some v => Some (norm1 (repB k ++ v))
          end
        end
      | Tok1 :: xs => execT fuel' 2%nat 0 xs
      end
    | S (S O) =>
      match w with
      | [] => Some [TokB; Tok1]
      | Tok0 :: xs => Some (norm1 (TokB :: Tok1 :: xs))
      | TokI :: xs =>
        match execT fuel' 0%nat 2 xs with
        | None => None
        | Some u =>
          match execT fuel' 1%nat 0 (norm1 u) with
          | None => None
          | Some v => Some (norm1 (TokB :: v))
          end
        end
      | [Tok1] => Some [TokB; Tok0; TokB]
      | Tok1 :: Tok0 :: xs =>
        match execT fuel' 1%nat 0 xs with
        | None => None
        | Some u =>
          match execT fuel' 1%nat 0 u with
          | None => None
          | Some v => Some (norm1 (TokB :: v))
          end
        end
      | _ => None
      end
    | _ => None
    end
  end.

Local Lemma execT_sound :
  forall (fuel : nat),
    (forall (n : N) (xs ys : list BecTok1),
      execT fuel 0%nat n xs = Some ys -> RelT0Pow n xs ys) /\
    (forall (n : N) (xs ys : list BecTok1),
      execT fuel 1%nat n xs = Some ys -> RelT M1 xs ys) /\
    (forall (n : N) (xs ys : list BecTok1),
      execT fuel 2%nat n xs = Some ys -> RelT M2 xs ys).
Proof.
  induction fuel as [| fuel [ih0 [ih1 ih2]]].
  - repeat split; intros; discriminate.
  - repeat split.
    + (* mode 0 *)
      intros n xs ys h; cbn [execT] in h.
      destruct (n =? 0) eqn:En.
      * injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero _).
      * apply N.eqb_neq in En.
        destruct xs as [| t rest]; [exact (binWord_sound 64%nat n ys h) |].
        destruct t.
        -- (* Tok0 *)
           destruct (execT fuel 0%nat (n / 2) rest) as [u |] eqn:Hex; [| discriminate].
           specialize (ih0 (n / 2) rest u Hex).
           destruct ((n mod 2) =? 1) eqn:Emod; injection h as <-.
           ++ apply N.eqb_eq in Emod.
              replace n with (2 * (n / 2) + 1) by div_lia.
              exact (proj1 (proj2 (RelT0Pow_bit ih0))).
           ++ apply N.eqb_neq in Emod.
              replace n with (2 * (n / 2)) by div_lia.
              exact (proj1 (RelT0Pow_bit ih0)).
        -- (* TokI *)
           destruct ((n mod 2) =? 0) eqn:Emod.
           ++ apply N.eqb_eq in Emod.
              destruct (execT fuel 0%nat (n / 2) rest) as [u |] eqn:Hex; [| discriminate].
              injection h as <-. specialize (ih0 (n / 2) rest u Hex).
              replace n with (2 * (n / 2)) by div_lia.
              exact (proj2 (proj2 (RelT0Pow_bit ih0))).
           ++ apply N.eqb_neq in Emod.
              destruct (execT fuel 0%nat (n / 2 + 1) rest) as [u |] eqn:Hex; [| discriminate].
              injection h as <-. specialize (ih0 (n / 2 + 1) rest u Hex).
              replace n with (2 * (n / 2) + 1) by div_lia.
              exact (RelT0Pow_kI_odd ih0).
        -- (* Tok1 *)
           destruct (execT fuel 1%nat 0 rest) as [xs' |] eqn:Hex; [| discriminate].
           replace n with ((n - 1) + 1) by lia.
           exact (rt0_succ (rt_t0_k1 (ih1 0 rest xs' Hex)) (ih0 (n - 1) xs' ys h)).
        -- (* TokB *)
           rewrite splitLeadB_spec in h.
           replace (1 + leadB rest) with (leadB rest + 1) in h by lia.
           destruct (execT fuel 0%nat n (dropB rest)) as [u |] eqn:Hex; [| discriminate].
           injection h as <-.
           pose proof (RelT0Pow_repB (leadB rest + 1) (ih0 n (dropB rest) u Hex)) as Hrep.
           replace (repB (leadB rest + 1) ++ dropB rest) with (TokB :: rest) in Hrep
             by (rewrite repB_succ; cbn [app]; rewrite (rep_leadB_dropB rest); reflexivity).
           exact Hrep.
    + (* mode 1 *)
      intros n xs ys h; cbn [execT] in h.
      destruct xs as [| t rest]; [injection h as <-; exact rt_t1_nil |].
      destruct t.
      * injection h as <-; exact (rt_norm_out (rt_t1_k0 rest)).
      * destruct (execT fuel 0%nat 1 rest) as [u |] eqn:Hex; [| discriminate].
        injection h as <-.
        exact (rt_norm_out (rt_t1_kI (RelT0Pow_1_inv (ih0 1 rest u Hex)))).
      * exact (rt_t1_k1 (ih2 0 rest ys h)).
      * rewrite splitLeadB_spec in h.
        replace (1 + leadB rest) with (leadB rest + 1) in h by lia.
        destruct (execT fuel 0%nat (2 * (leadB rest + 1)) (dropB rest)) as [u |] eqn:Hex0; [| discriminate].
        destruct (execT fuel 1%nat 0 (norm1 u)) as [v |] eqn:Hex1; [| discriminate].
        injection h as <-.
        assert (Hpos : 0 < 2 * (leadB rest + 1)) by lia.
        pose proof (RelT0Pow_norm_out Hpos (ih0 _ _ _ Hex0)) as Hpow.
        pose proof (ih1 0 (norm1 u) v Hex1) as Hv.
        pose proof (RelT_t1_repB (leadB rest + 1) Hpow Hv) as Hrep.
        replace (repB (leadB rest + 1) ++ dropB rest) with (TokB :: rest) in Hrep
          by (rewrite repB_succ; cbn [app]; rewrite (rep_leadB_dropB rest); reflexivity).
        exact (rt_norm_out Hrep).
    + (* mode 2 *)
      intros n xs ys h; cbn [execT] in h.
      destruct xs as [| t rest]; [injection h as <-; exact rt_t2_nil |].
      destruct t.
      * injection h as <-; exact (rt_norm_out (rt_t2_k0 rest)).
      * destruct (execT fuel 0%nat 2 rest) as [u |] eqn:Hex0; [| discriminate].
        destruct (execT fuel 1%nat 0 (norm1 u)) as [v |] eqn:Hex1; [| discriminate].
        injection h as <-.
        assert (Hpos : 0 < 2) by lia.
        pose proof (RelT0Pow_norm_out Hpos (ih0 2 rest u Hex0)) as Hpow.
        destruct (RelT0Pow_2_inv Hpow) as [x [ha hb]].
        exact (rt_norm_out (rt_t2_kI ha hb (ih1 0 (norm1 u) v Hex1))).
      * destruct rest as [| t2 rest2]; [injection h as <-; exact rt_t2_k1_nil |].
        destruct t2; try discriminate.
        destruct (execT fuel 1%nat 0 rest2) as [u |] eqn:Hex1; [| discriminate].
        destruct (execT fuel 1%nat 0 u) as [v |] eqn:Hex2; [| discriminate].
        injection h as <-.
        exact (rt_norm_out (rt_t2_k1_k0 (ih1 0 rest2 u Hex1) (ih1 0 u v Hex2))).
      * discriminate.
Qed.

Local Lemma execT_t0_sound {fuel : nat} {n : N} {xs ys : list BecTok1}
    (h : execT fuel 0%nat n xs = Some ys) : RelT0Pow n xs ys.
Proof. exact (proj1 (execT_sound fuel) n xs ys h). Qed.

Local Lemma execT_t1_sound {fuel : nat} {xs ys : list BecTok1}
    (h : execT fuel 1%nat 0 xs = Some ys) : RelT M1 xs ys.
Proof. exact (proj1 (proj2 (execT_sound fuel)) 0 xs ys h). Qed.

Fixpoint addL0 (fuel : nat) (n : N) (w : list BecTok1) : option (list BecTok1) :=
  if n =? 0 then Some w
  else match fuel with
  | O => None
  | S fuel' =>
    match w with
    | [] => addL0 fuel' (n - 1) [TokI]
    | TokB :: xs =>
      match addL0 fuel' n xs with
      | None => None
      | Some u => Some (TokB :: u)
      end
    | Tok0 :: xs =>
      match addL0 fuel' (n / 2) xs with
      | None => None
      | Some u => Some ((if (n mod 2) =? 0 then Tok0 else TokI) :: u)
      end
    | TokI :: xs =>
      match addL0 fuel' ((n + 1) / 2) xs with
      | None => None
      | Some u => Some ((if (n mod 2) =? 0 then TokI else Tok0) :: u)
      end
    | Tok1 :: _ => None
    end
  end.

Local Lemma addL0_sound :
  forall (fuel : nat) (n : N) (xs ys : list BecTok1),
    addL0 fuel n xs = Some ys -> RelT0Pow n xs ys.
Proof.
  induction fuel as [| fuel IH]; intros n xs ys h; cbn [addL0] in h.
  - destruct (n =? 0) eqn:En; [injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero _) | discriminate].
  - destruct (n =? 0) eqn:En.
    + injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero _).
    + apply N.eqb_neq in En.
      destruct xs as [| t rest].
      * replace n with ((n - 1) + 1) by lia.
        exact (rt0_succ rt_t0_nil (IH (n - 1) [TokI] ys h)).
      * destruct t.
        -- (* Tok0 *)
           destruct (addL0 fuel (n / 2) rest) as [u |] eqn:Ha; [| discriminate].
           specialize (IH (n / 2) rest u Ha).
           destruct ((n mod 2) =? 0) eqn:Emod; injection h as <-.
           ++ apply N.eqb_eq in Emod.
              replace n with (2 * (n / 2)) by div_lia.
              exact (proj1 (RelT0Pow_bit IH)).
           ++ apply N.eqb_neq in Emod.
              replace n with (2 * (n / 2) + 1) by div_lia.
              exact (proj1 (proj2 (RelT0Pow_bit IH))).
        -- (* TokI *)
           destruct (addL0 fuel ((n + 1) / 2) rest) as [u |] eqn:Ha; [| discriminate].
           specialize (IH ((n + 1) / 2) rest u Ha).
           destruct ((n mod 2) =? 0) eqn:Emod; injection h as <-.
           ++ apply N.eqb_eq in Emod.
              assert (Heq : (n + 1) / 2 = n / 2) by div_lia.
              rewrite Heq in IH.
              replace n with (2 * (n / 2)) by div_lia.
              exact (proj2 (proj2 (RelT0Pow_bit IH))).
           ++ apply N.eqb_neq in Emod.
              assert (Heq : (n + 1) / 2 = n / 2 + 1) by div_lia.
              rewrite Heq in IH.
              replace n with (2 * (n / 2) + 1) by div_lia.
              exact (RelT0Pow_kI_odd IH).
        -- (* Tok1 *)
           discriminate.
        -- (* TokB *)
           destruct (addL0 fuel n rest) as [u |] eqn:Ha; [| discriminate].
           injection h as <-.
           pose proof (RelT0Pow_repB 1 (IH n rest u Ha)) as Hrep.
           cbn [repB Pos.iter app] in Hrep. exact Hrep.
Qed.

Definition execT0 (fuel : nat) (n : N) (xs : list BecTok1) : option (list BecTok1) :=
  match addL0 fuel n xs with
  | Some ys => Some ys
  | None => execT fuel 0%nat n xs
  end.

Local Lemma execT0_sound {fuel : nat} {n : N} {xs ys : list BecTok1}
    (h : execT0 fuel n xs = Some ys) : RelT0Pow n xs ys.
Proof.
  unfold execT0 in h.
  destruct (addL0 fuel n xs) as [u |] eqn:Ha.
  - injection h as <-. exact (addL0_sound fuel n xs u Ha).
  - exact (execT_t0_sound h).
Qed.

Definition t0PowNorm (fuel : nat) (n : N) (xs : list BecTok1) : option (list BecTok1) :=
  if n =? 0 then Some xs
  else
    match execT0 fuel n xs with
    | None => None
    | Some ys => Some (norm1 ys)
    end.

Local Lemma t0PowNorm_sound {fuel : nat} {n : N} {xs ys : list BecTok1}
    (h : t0PowNorm fuel n xs = Some ys) : RelT0Pow n xs ys.
Proof.
  unfold t0PowNorm in h.
  destruct (n =? 0) eqn:En.
  - injection h as <-; apply N.eqb_eq in En; subst; exact (rt0_zero _).
  - apply N.eqb_neq in En.
    destruct (execT0 fuel n xs) as [u |] eqn:Hex; [| discriminate].
    injection h as <-.
    assert (Hpos : 0 < n) by lia.
    exact (RelT0Pow_norm_out Hpos (execT0_sound Hex)).
Qed.

Definition t0Step1 (fuel : nat) (w : list BecTok1) : option (list BecTok1) :=
  if noK1 w then Some (t0One w) else t0PowNorm fuel 1 w.

Local Lemma t0Step1_sound {fuel : nat} {w w' : list BecTok1}
    (h : t0Step1 fuel w = Some w') : RelT M0 w w'.
Proof.
  unfold t0Step1 in h.
  destruct (noK1 w) eqn:Hno.
  - injection h as <-. exact (RelT_t0One Hno).
  - exact (RelT0Pow_1_inv (t0PowNorm_sound h)).
Qed.

Fixpoint iterBounce (fuel k : nat) (w : list BecTok1) : option (list BecTok1) :=
  match k with
  | O => Some w
  | S k' =>
    match execT fuel 1%nat 0 w with
    | None => None
    | Some w' => iterBounce fuel k' w'
    end
  end.

Local Lemma iterBounce_sound :
  forall (fuel k : nat) (w w' : list BecTok1),
    iterBounce fuel k w = Some w' ->
    evalBecCfg hL (decode1 w) [] -->* evalBecCfg hL (decode1 w') [].
Proof.
  intros fuel k; induction k as [| k IH]; intros w w' h; cbn [iterBounce] in h.
  - injection h as <-. apply evstep_refl.
  - destruct (execT fuel 1%nat 0 w) as [u |] eqn:Hex; [| discriminate].
    pose proof (execT_t1_sound Hex) as H1.
    pose proof (ptrans (step_hL_nil (decode1 w)) (RelT_sound H1 [])) as Hstep.
    exact (etrans (p_to_e Hstep) (IH u w' h)).
Qed.

Definition stepCollar1 (fuel : nat) (k_col : N) (tail : list BecTok1) : option (N * list BecTok1) :=
  match t0PowNorm fuel (2 * k_col) tail with
  | None => None
  | Some u =>
    match execT fuel 1%nat 0 u with
    | None => None
    | Some v =>
      match t0Step1 fuel v with
      | None => None
      | Some v' =>
        let nv := norm1 v' in
        Some (k_col + leadB nv, dropB nv)
      end
    end
  end.

Local Lemma stepCollar1_sound {fuel : nat} {k_col k_col' : N} {tail tail' : list BecTok1}
    (h : stepCollar1 fuel k_col tail = Some (k_col', tail')) :
  cfgCollar k_col tail -->+ cfgCollar k_col' tail'.
Proof.
  unfold stepCollar1 in h.
  destruct (t0PowNorm fuel (2 * k_col) tail) as [u |] eqn:Hu; [| discriminate].
  destruct (execT fuel 1%nat 0 u) as [v |] eqn:Hv; [| discriminate].
  destruct (t0Step1 fuel v) as [v' |] eqn:Hv'; [| discriminate].
  injection h as <- <-.
  exact (collar_step k_col (t0PowNorm_sound Hu) (execT_t1_sound Hv) (t0Step1_sound Hv')).
Qed.

Fixpoint iterCollar (fuel steps : nat) (k_col : N) (tail : list BecTok1) : option (N * list BecTok1) :=
  match steps with
  | O => Some (k_col, tail)
  | S steps' =>
    match stepCollar1 fuel k_col tail with
    | None => None
    | Some (k_next, tail1) => iterCollar fuel steps' k_next tail1
    end
  end.

Local Lemma iterCollar_sound :
  forall (fuel steps : nat) (k_col k_col' : N) (tail tail' : list BecTok1),
    iterCollar fuel steps k_col tail = Some (k_col', tail') ->
    cfgCollar k_col tail -->* cfgCollar k_col' tail'.
Proof.
  intros fuel steps; induction steps as [| steps IH]; intros k_col k_col' tail tail' h; cbn [iterCollar] in h.
  - injection h as <- <-. apply evstep_refl.
  - destruct (stepCollar1 fuel k_col tail) as [[k1 t1] |] eqn:Hs; [| discriminate].
    exact (etrans (p_to_e (stepCollar1_sound Hs)) (IH k1 k_col' t1 tail' h)).
Qed.

Definition ct0 : list BecTok1 := [Tok0; TokI; TokI; TokI].
Definition tail67 : list BecTok1 := [Tok0; TokI; Tok0; TokI; TokI; TokI; TokI].
Definition bw12 : list BecTok1 := [TokB; TokB; Tok0; Tok1] ++ repB 9 ++ ct0.

Local Lemma bounce12_eq : iterBounce 256%nat 12%nat [TokI] = Some bw12.
Proof. vm_compute; reflexivity. Qed.

Local Lemma collar55_eq : iterCollar 128%nat 55%nat 9 ct0 = Some (64, tail67).
Proof. vm_compute; reflexivity. Qed.

#[local] Opaque iterBounce iterCollar.

Local Lemma init_reaches_inv :
  exists c, c0 -->+ c /\ InvCfg c.
Proof.
  pose proof init_to_bec as h0.
  change [T100] with (decode1 [TokI]) in h0.
  pose proof (iterBounce_sound 256%nat 12%nat [TokI] bw12 bounce12_eq) as h12.
  change (evalBecCfg hL (decode1 bw12) []) with (cfgCollar 9 ct0) in h12.
  pose proof (iterCollar_sound 128%nat 55%nat 9 64 ct0 tail67 collar55_eq) as h67.
  exists (cfgCollar 64 tail67). split.
  - exact (petrans h0 (etrans h12 h67)).
  - exists 64, tail67. refine (conj eq_refl (or_introl _)).
    unfold InC0, tail67; cbn [noK1 noTrailZero evalPhi].
    repeat split; lia.
Qed.

(* ========================================================================== *)
(* Layer 3a: L_0 Prefix Euclidean Algebra, Wave Conservation & allRQ          *)
(* ========================================================================== *)

Fixpoint countBin (w : list BecTok1) : N :=
  match w with
  | [] => 0
  | Tok0 :: xs => countBin xs + 1
  | TokI :: xs => countBin xs + 1
  | TokB :: xs => countBin xs
  | Tok1 :: xs => countBin xs
  end.

Fixpoint deltaB (w : list BecTok1) : N :=
  match w with
  | [] => 0
  | Tok0 :: xs => 2 * deltaB xs
  | TokI :: xs => 2 * deltaB xs
  | TokB :: xs => 1 + deltaB xs
  | Tok1 :: xs => deltaB xs
  end.

Local Lemma evalPhi_eq_zero_add_deltaB (cB : N) (w : list BecTok1) :
  evalPhi cB w = evalPhi 0 w + cB * deltaB w.
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; cbn [evalPhi deltaB]; rewrite IH; lia.
Qed.

Local Lemma countBin_append (xs ys : list BecTok1) :
  countBin (xs ++ ys) = countBin xs + countBin ys.
Proof.
  induction xs as [| t xs IH]; [cbn; lia |].
  destruct t; cbn [app countBin]; rewrite IH; lia.
Qed.

Local Lemma noK1_append (xs ys : list BecTok1) :
  noK1 (xs ++ ys) = (noK1 xs && noK1 ys).
Proof.
  induction xs as [| t xs IH]; [reflexivity |].
  destruct t; cbn [app noK1]; [exact IH | exact IH | reflexivity | exact IH].
Qed.

Local Lemma evalPhi_append (cB : N) (xs ys : list BecTok1) :
  evalPhi cB (xs ++ ys) = evalPhi cB xs + (2 ^ countBin xs) * evalPhi cB ys.
Proof.
  induction xs as [| t xs IH]; [cbn [app evalPhi countBin]; rewrite pow2_0; lia |].
  destruct t; cbn [app evalPhi countBin]; try rewrite pow2_succ; rewrite IH; lia.
Qed.

Local Lemma deltaB_append (xs ys : list BecTok1) :
  deltaB (xs ++ ys) = deltaB xs + (2 ^ countBin xs) * deltaB ys.
Proof.
  induction xs as [| t xs IH]; [cbn [app deltaB countBin]; rewrite pow2_0; lia |].
  destruct t; cbn [app deltaB countBin]; try rewrite pow2_succ; rewrite IH; lia.
Qed.

Local Lemma evalPhi_zero_lt_pow_countBin (w : list BecTok1) :
  evalPhi 0 w < 2 ^ countBin w.
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; cbn [evalPhi countBin]; try rewrite pow2_succ; lia.
Qed.

Local Lemma evalPhi_zero_pos_of_hasI {w : list BecTok1} (h : hasI w = true) :
  0 < evalPhi 0 w.
Proof.
  induction w as [| t xs IH]; [discriminate h |].
  destruct t; cbn [evalPhi]; [cbn [hasI] in h; specialize (IH h); lia | lia
    | cbn [hasI] in h; exact (IH h) | cbn [hasI] in h; specialize (IH h); lia].
Qed.

Local Lemma deltaB_t0One {w : list BecTok1} (h : noK1 w = true) :
  deltaB (t0One w) = deltaB w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - reflexivity.
  - cbn [t0One deltaB]; rewrite (IH h); reflexivity.
  - cbn [t0One deltaB]; rewrite (IH h); reflexivity.
Qed.

Local Lemma deltaB_t0Pow (n : N) :
  forall {w : list BecTok1}, noK1 w = true -> deltaB (t0Pow n w) = deltaB w.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h; [reflexivity |].
  rewrite t0Pow_succ, (IH _ (noK1_t0One h)), (deltaB_t0One h). reflexivity.
Qed.

Local Lemma countBin_t0One_of_lt {w : list BecTok1}
    (h : noK1 w = true) (hlt : evalPhi 0 w + 1 < 2 ^ countBin w) :
  countBin (t0One w) = countBin w.
Proof.
  induction w as [| t xs IH]; [cbn in hlt; lia |].
  destruct t; try discriminate h; cbn [noK1] in h.
  - reflexivity.
  - cbn [evalPhi countBin] in hlt. rewrite pow2_succ in hlt.
    cbn [t0One countBin]. rewrite (IH h ltac:(lia)). reflexivity.
  - cbn [evalPhi countBin] in hlt.
    cbn [t0One countBin]. rewrite (IH h ltac:(lia)). reflexivity.
Qed.

Local Lemma countBin_t0Pow_of_lt (n : N) :
  forall {w : list BecTok1},
    noK1 w = true -> evalPhi 0 w + n < 2 ^ countBin w ->
    countBin (t0Pow n w) = countBin w.
Proof.
  induction n as [| n IH] using N_ind_add1; intros w h hlt; [reflexivity |].
  pose proof (countBin_t0One_of_lt h ltac:(lia)) as hc1.
  pose proof (evalPhi_zero_t0One h) as hw1.
  assert (hlt' : evalPhi 0 (t0One w) + n < 2 ^ countBin (t0One w))
    by (rewrite hc1, hw1; lia).
  rewrite t0Pow_succ, (IH _ (noK1_t0One h) hlt'), hc1. reflexivity.
Qed.

Local Lemma deltaB_consTrim (t : BecTok1) (xs : list BecTok1) :
  deltaB (consTrim t xs) = deltaB (t :: xs).
Proof.
  destruct t; destruct xs; reflexivity.
Qed.

Local Lemma deltaB_trimZero (w : list BecTok1) :
  deltaB (trimZero w) = deltaB w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. rewrite deltaB_consTrim.
  destruct t; cbn [deltaB]; rewrite IH; reflexivity.
Qed.

Local Lemma deltaB_leadB_dropB (w : list BecTok1) :
  deltaB w = leadB w + deltaB (dropB w).
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; try (cbn [leadB dropB]; lia).
  cbn [deltaB leadB dropB]; rewrite IH; lia.
Qed.

Local Lemma countBin_dropB (w : list BecTok1) :
  countBin (dropB w) = countBin w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try reflexivity; exact IH.
Qed.

Local Lemma leadB_consTrim (t : BecTok1) (xs : list BecTok1) :
  leadB (consTrim t xs) = leadB (t :: xs).
Proof.
  destruct t; destruct xs; reflexivity.
Qed.

Local Lemma leadB_trimZero (w : list BecTok1) :
  leadB (trimZero w) = leadB w.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  cbn [trimZero]. rewrite leadB_consTrim.
  destruct t; try reflexivity.
  cbn [leadB]; rewrite IH; reflexivity.
Qed.

Local Lemma dropB_trimZero (w : list BecTok1) :
  dropB (trimZero w) = trimZero (dropB w).
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t.
  - cbn [dropB trimZero]. destruct (trimZero xs); reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [trimZero consTrim dropB]. exact IH.
Qed.

Local Lemma coalesce_append_of_noK1 {P : list BecTok1} (hP : noK1 P = true) (Y : list BecTok1) :
  coalesce (P ++ Y) = P ++ coalesce Y.
Proof.
  induction P as [| t xs IH]; [reflexivity |].
  destruct t; try discriminate hP; cbn [noK1] in hP;
    cbn [app coalesce]; rewrite (IH hP); reflexivity.
Qed.

Local Lemma trimZero_append_of_ne_nil (P : list BecTok1) {Y : list BecTok1} (hY : trimZero Y <> []) :
  trimZero (P ++ Y) = P ++ trimZero Y.
Proof.
  induction P as [| t xs IH]; [reflexivity |].
  cbn [app trimZero]. rewrite IH.
  destruct (xs ++ trimZero Y) as [| u us] eqn:Hxy.
  - destruct xs; [contradiction | discriminate Hxy].
  - destruct t; reflexivity.
Qed.

Local Lemma cfgCollar_norm1 (k_col : N) (w : list BecTok1) :
  cfgCollar (k_col + leadB (norm1 w)) (dropB (norm1 w)) = cfgCollar k_col w.
Proof.
  unfold cfgCollar, evalBecCfg.
  replace ([TokB; TokB; Tok0; Tok1] ++ repB (k_col + leadB (norm1 w)) ++ dropB (norm1 w))
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col) ++ norm1 w)
    by (rewrite repB_add, <- !app_assoc, rep_leadB_dropB; reflexivity).
  replace ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ w)
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col) ++ w)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite !decode1_append, (becLeft_append_eq (becLeft_decode1_norm1 w)).
  reflexivity.
Qed.

Local Lemma cfgCollar_eq_norm1 (k_col : N) (w : list BecTok1) :
  cfgCollar k_col (norm1 w) = cfgCollar k_col w.
Proof.
  unfold cfgCollar, evalBecCfg.
  replace ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ norm1 w)
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col) ++ norm1 w)
    by (rewrite <- !app_assoc; reflexivity).
  replace ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ w)
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col) ++ w)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite !decode1_append, (becLeft_append_eq (becLeft_decode1_norm1 w)).
  reflexivity.
Qed.

Local Lemma cfgCollar_repB (k_col m : N) (w : list BecTok1) :
  cfgCollar k_col (repB m ++ w) = cfgCollar (k_col + m) w.
Proof.
  unfold cfgCollar. rewrite repB_add, <- !app_assoc. reflexivity.
Qed.

Local Lemma leadB_append_of_countBin_pos {P : list BecTok1}
    (hno : noK1 P = true) (hpos : 0 < countBin P) (Y : list BecTok1) :
  leadB (P ++ Y) = leadB P /\ dropB (P ++ Y) = dropB P ++ Y.
Proof.
  induction P as [| t xs IH]; [cbn in hpos; lia |].
  destruct t; try discriminate hno.
  - exact (conj eq_refl eq_refl).
  - exact (conj eq_refl eq_refl).
  - cbn [noK1 countBin] in hno, hpos.
    destruct (IH hno hpos) as [hl hd].
    cbn [app leadB dropB]; rewrite hl, hd; exact (conj eq_refl eq_refl).
Qed.

Local Lemma div_mod_unique {x d q r : N} (hx : x = d * q + r) (hr : r < d) :
  x / d = q /\ x mod d = r.
Proof.
  assert (hd0 : d <> 0) by lia.
  pose proof (N.div_unique x d q r hr hx) as Hq.
  pose proof (N.mod_unique x d q r hr hx) as Hr.
  exact (conj (eq_sym Hq) (eq_sym Hr)).
Qed.

Local Lemma div_mod_spec (x d : N) (hd : 0 < d) :
  exists q r : N, x / d = q /\ x mod d = r /\ x = d * q + r /\ r < d.
Proof.
  assert (hd0 : d <> 0) by lia.
  exists (x / d), (x mod d).
  exact (conj eq_refl (conj eq_refl (conj (N.div_mod x d hd0) (N.mod_lt x d hd0)))).
Qed.

Local Lemma mod2_dichotomy (n : N) :
  exists q : N, n / 2 = q /\
    ((n mod 2 = 0 /\ (n + 1) / 2 = q /\ n = 2 * q) \/
     (n mod 2 = 1 /\ (n + 1) / 2 = q + 1 /\ n = 2 * q + 1)).
Proof.
  exists (n / 2). split; [reflexivity |].
  destruct (N.eq_dec (n mod 2) 0) as [E0 | E1].
  - left; repeat split; [exact E0 | div_lia | div_lia].
  - right; repeat split; [div_lia | div_lia | div_lia].
Qed.

Local Lemma RelT0Pow_prefix_div :
  forall (P : list BecTok1), noK1 P = true ->
    forall (n : N) {Y Y' : list BecTok1},
      RelT0Pow ((evalPhi 0 P + n) / (2 ^ countBin P)) Y Y' ->
      exists P' : list BecTok1,
        RelT0Pow n (P ++ Y) (P' ++ Y') /\
        noK1 P' = true /\
        countBin P' = countBin P /\
        deltaB P' = deltaB P /\
        evalPhi 0 P' = (evalPhi 0 P + n) mod (2 ^ countBin P) /\
        leadB P' = leadB P /\
        countB P' = countB P.
Proof.
  intros P hP.
  induction P as [| t xs IH].
  - intros n Y Y' hY.
    cbn [evalPhi countBin] in hY |- *.
    rewrite pow2_0, N.add_0_l, N.div_1_r in hY.
    rewrite pow2_0, N.add_0_l, N.mod_1_r.
    exists (@nil BecTok1); repeat split; try reflexivity; exact hY.
  - destruct t; try discriminate hP; cbn [noK1] in hP.
    + (* Tok0 *)
      intros n Y Y' hY.
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as M eqn:hM_def.
      assert (hpow : 2 ^ countBin (Tok0 :: xs) = 2 * M)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      rewrite hpow in hY |- *.
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]]]];
      destruct (div_mod_spec (evalPhi 0 xs + nh) M hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) / (2 * M) = Q0 /\
                      (evalPhi 0 (Tok0 :: xs) + n) mod (2 * M) = 2 * R0).
        { apply div_mod_unique; [replace (2 * M * Q0) with (2 * (M * Q0)) by ring; cbn [evalPhi]; lia | lia]. }
        rewrite (proj1 hdm) in hY.
        destruct (IH hP nh Y Y' (ltac:(rewrite hQ0; exact hY))) as [xs' [hrel [hno [hcb [hdb [hw [_ hcntb]]]]]]].
        exists (Tok0 :: xs').
        refine (conj _ (conj hno (conj _ (conj _ (conj _ (conj eq_refl hcntb)))))).
        -- rewrite hn_eq. exact (proj1 (RelT0Pow_bit hrel)).
        -- cbn [countBin]; rewrite hcb; reflexivity.
        -- cbn [deltaB]; rewrite hdb; reflexivity.
        -- rewrite (proj2 hdm); cbn [evalPhi]; rewrite hw, hR0; reflexivity.
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) / (2 * M) = Q0 /\
                      (evalPhi 0 (Tok0 :: xs) + n) mod (2 * M) = 1 + 2 * R0).
        { apply div_mod_unique; [replace (2 * M * Q0) with (2 * (M * Q0)) by ring; cbn [evalPhi]; lia | lia]. }
        rewrite (proj1 hdm) in hY.
        destruct (IH hP nh Y Y' (ltac:(rewrite hQ0; exact hY))) as [xs' [hrel [hno [hcb [hdb [hw [_ hcntb]]]]]]].
        exists (TokI :: xs').
        refine (conj _ (conj hno (conj _ (conj _ (conj _ (conj eq_refl hcntb)))))).
        -- rewrite hn_eq. exact (proj1 (proj2 (RelT0Pow_bit hrel))).
        -- cbn [countBin]; rewrite hcb; reflexivity.
        -- cbn [deltaB]; rewrite hdb; reflexivity.
        -- rewrite (proj2 hdm); cbn [evalPhi]; rewrite hw, hR0; reflexivity.
    + (* TokI *)
      intros n Y Y' hY.
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as M eqn:hM_def.
      assert (hpow : 2 ^ countBin (TokI :: xs) = 2 * M)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      rewrite hpow in hY |- *.
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]]]].
      * destruct (div_mod_spec (evalPhi 0 xs + nh) M hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) / (2 * M) = Q0 /\
                      (evalPhi 0 (TokI :: xs) + n) mod (2 * M) = 1 + 2 * R0).
        { apply div_mod_unique; [replace (2 * M * Q0) with (2 * (M * Q0)) by ring; cbn [evalPhi]; lia | lia]. }
        rewrite (proj1 hdm) in hY.
        destruct (IH hP nh Y Y' (ltac:(rewrite hQ0; exact hY))) as [xs' [hrel [hno [hcb [hdb [hw [_ hcntb]]]]]]].
        exists (TokI :: xs').
        refine (conj _ (conj hno (conj _ (conj _ (conj _ (conj eq_refl hcntb)))))).
        -- rewrite hn_eq. exact (proj2 (proj2 (RelT0Pow_bit hrel))).
        -- cbn [countBin]; rewrite hcb; reflexivity.
        -- cbn [deltaB]; rewrite hdb; reflexivity.
        -- rewrite (proj2 hdm); cbn [evalPhi]; rewrite hw, hR0; reflexivity.
      * destruct (div_mod_spec (evalPhi 0 xs + (nh + 1)) M hM) as [Q1 [R1 [hQ1 [hR1 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) / (2 * M) = Q1 /\
                      (evalPhi 0 (TokI :: xs) + n) mod (2 * M) = 2 * R1).
        { apply div_mod_unique; [replace (2 * M * Q1) with (2 * (M * Q1)) by ring; cbn [evalPhi]; lia | lia]. }
        rewrite (proj1 hdm) in hY.
        destruct (IH hP (nh + 1) Y Y' (ltac:(rewrite hQ1; exact hY))) as [xs' [hrel [hno [hcb [hdb [hw [_ hcntb]]]]]]].
        exists (Tok0 :: xs').
        refine (conj _ (conj hno (conj _ (conj _ (conj _ (conj eq_refl hcntb)))))).
        -- rewrite hn_eq. exact (RelT0Pow_kI_odd hrel).
        -- cbn [countBin]; rewrite hcb; reflexivity.
        -- cbn [deltaB]; rewrite hdb; reflexivity.
        -- rewrite (proj2 hdm); cbn [evalPhi]; rewrite hw, hR1; reflexivity.
    + (* TokB *)
      intros n Y Y' hY.
      cbn [evalPhi countBin] in hY |- *. rewrite N.add_0_l in hY |- *.
      destruct (IH hP n Y Y' hY) as [xs' [hrel [hno [hcb [hdb [hw [hlb hcntb]]]]]]].
      exists (TokB :: xs').
      refine (conj _ (conj hno (conj hcb (conj _ (conj _ (conj _ _)))))).
      * pose proof (RelT0Pow_repB 1 hrel) as Hrep.
        cbn [repB Pos.iter app] in Hrep. exact Hrep.
      * cbn [deltaB]; rewrite hdb; reflexivity.
      * cbn [evalPhi]; rewrite hw; lia.
      * cbn [leadB]; rewrite hlb; reflexivity.
      * cbn [countB]; rewrite hcntb; reflexivity.
Qed.

Local Lemma norm1_split_notHeadI {P rw : list BecTok1}
    (hP : noK1 P = true) (hR : noK1 rw = true) (hnh : notHeadI rw = true) (hI : hasI rw = true) :
  norm1 (P ++ [Tok1] ++ rw) = P ++ [Tok1] ++ trimZero rw.
Proof.
  unfold norm1. rewrite (coalesce_append_of_noK1 hP).
  assert (hcoal : coalesce ([Tok1] ++ rw) = Tok1 :: rw).
  { cbn [app coalesce]. rewrite (coalesce_eq_of_noK1 hR).
    destruct rw as [| u us]; [reflexivity | destruct u; [reflexivity | discriminate hnh | reflexivity | reflexivity]]. }
  rewrite hcoal.
  assert (hne : trimZero (Tok1 :: rw) <> []) by (cbn [trimZero consTrim]; discriminate).
  rewrite (trimZero_append_of_ne_nil P hne).
  cbn [trimZero consTrim app]. reflexivity.
Qed.

Local Lemma t1_l0_decomp :
  forall (b : N) (z : list BecTok1),
    countB z = b -> noK1 z = true -> hasI z = true ->
    (exists W : list BecTok1,
      RelT M1 z W /\ noK1 W = true /\
      2 * evalPhi 0 W <= evalPhi 2 z + 1 /\
      10 * evalPhi 22 W <= 11 * evalPhi 22 z + 418) \/
    (exists P0 R0 : list BecTok1,
      RelT M1 z (P0 ++ [Tok1] ++ R0) /\
      noK1 P0 = true /\ countBin P0 = 1 /\ evalPhi 0 P0 = 0 /\
      noK1 R0 = true /\ noTrailZero R0 = true /\ notHeadI R0 = true /\ hasI R0 = true /\
      evalPhi 2 z = 2 * evalPhi 2 R0 /\
      evalPhi 0 z + 2 * deltaB P0 = 2 * evalPhi 0 R0 /\
      evalPhi 22 z = 20 * deltaB P0 + 2 * evalPhi 22 R0).
Proof.
  induction b as [b IH] using N_strong_ind.
  intros z hb hno hI.
  destruct z as [| t rw]; [discriminate hI |].
  destruct t.
  - (* Tok0 *)
    cbn [noK1 hasI] in hno, hI.
    destruct (notHeadI rw) eqn:Hnh.
    + pose proof (rt_norm_out (rt_t1_k0 rw)) as ht1.
      change (Tok0 :: Tok1 :: rw) with ([Tok0] ++ [Tok1] ++ rw) in ht1.
      rewrite (@norm1_split_notHeadI [Tok0] rw eq_refl hno Hnh hI) in ht1.
      right. exists [Tok0], (trimZero rw).
      refine (conj ht1 (conj eq_refl (conj eq_refl (conj eq_refl
        (conj (noK1_trimZero hno) (conj (noTrailZero_trimZero rw)
          (conj (notHeadI_trimZero Hnh hI) _))))))).
      rewrite hasI_trimZero, !evalPhi_trimZero.
      cbn [evalPhi deltaB]; split; [exact hI | repeat split; lia].
    + destruct rw as [| u xs]; [discriminate Hnh |].
      destruct u; try discriminate Hnh.
      cbn [noK1] in hno.
      pose proof (rt_norm_out (rt_t1_k0 (TokI :: xs))) as ht1.
      assert (hnorm : norm1 (Tok0 :: Tok1 :: TokI :: xs) = trimZero (Tok0 :: TokB :: xs)).
      { unfold norm1; cbn [coalesce consNorm]; rewrite (coalesce_eq_of_noK1 hno); reflexivity. }
      rewrite hnorm in ht1.
      left. exists (trimZero (Tok0 :: TokB :: xs)).
      refine (conj ht1 (conj (noK1_trimZero hno) _)).
      rewrite !evalPhi_trimZero.
      pose proof (evalPhi_eq_zero_add_deltaB 2 xs).
      cbn [evalPhi]; split; lia.
  - (* TokI *)
    cbn [noK1] in hno.
    left. exists (TokB :: t0One rw).
    refine (conj (rt_t1_kI (RelT_t0One hno)) (conj (noK1_t0One hno) _)).
    pose proof (evalPhi_zero_t0One hno).
    pose proof (evalPhi_t0One 22 hno).
    pose proof (evalPhi_eq_zero_add_deltaB 2 rw).
    cbn [evalPhi]; split; lia.
  - (* Tok1 *)
    discriminate hno.
  - (* TokB *)
    cbn [noK1 countB] in hno, hb.
    assert (hb' : countB (t0Pow 2 rw) < b) by (rewrite (countB_t0Pow 2 hno); lia).
    pose proof (noK1_t0Pow 2 hno) as hno'.
    assert (hI' : hasI (t0Pow 2 rw) = true)
      by (apply (hasI_of_evalPhi_zero_pos hno'); rewrite (evalPhi_zero_t0Pow 2 hno); lia).
    pose proof (evalPhi_t0Pow 0 2 hno) as hw2.
    pose proof (evalPhi_t0Pow 2 2 hno) as hpsi2.
    pose proof (evalPhi_t0Pow 22 2 hno) as hphi2.
    destruct (IH (countB (t0Pow 2 rw)) hb' (t0Pow 2 rw) eq_refl hno' hI')
      as [[W' [ht1 [hnoW [hwW hpW]]]] |
          [P0' [R0 [ht1 [hnoP [hcbP [hwP [hnoR [htzR [hnhR [hIR [ec2 [ec0 ec22]]]]]]]]]]]]].
    + left. exists (TokB :: W').
      refine (conj (rt_t1_kB (RelT_t0One hno) (RelT_t0One (noK1_t0One hno)) ht1) (conj hnoW _)).
      cbn [evalPhi]; split; lia.
    + right. exists (TokB :: P0'), R0.
      refine (conj (rt_t1_kB (RelT_t0One hno) (RelT_t0One (noK1_t0One hno)) ht1)
        (conj hnoP (conj hcbP (conj _ (conj hnoR (conj htzR (conj hnhR (conj hIR _)))))))).
      * cbn [evalPhi]; lia.
      * cbn [evalPhi deltaB]; repeat split; lia.
Qed.

Local Lemma t0Pow_t1_decomp :
  forall (n : N) (z : list BecTok1),
    noK1 z = true -> hasI z = true ->
    (exists W Qw : list BecTok1,
      RelT M1 z W /\ RelT0Pow n W Qw /\ noK1 Qw = true /\
      2 * evalPhi 0 Qw <= evalPhi 2 z + 2 * n + 1 /\
      10 * evalPhi 22 Qw <= 11 * evalPhi 22 z + 420 * n + 418) \/
    (exists W PQ RQ : list BecTok1,
      RelT M1 z W /\ RelT0Pow n W (PQ ++ [Tok1] ++ RQ) /\
      noK1 PQ = true /\ 1 <= countBin PQ /\
      evalPhi 0 PQ + (2 ^ countBin PQ) = n + 2 /\
      noK1 RQ = true /\ noTrailZero RQ = true /\ notHeadI RQ = true /\ hasI RQ = true /\
      evalPhi 2 z = (2 ^ countBin PQ) * evalPhi 2 RQ /\
      evalPhi 0 z + 2 * deltaB PQ = (2 ^ countBin PQ) * evalPhi 0 RQ /\
      evalPhi 22 z = 20 * deltaB PQ + (2 ^ countBin PQ) * evalPhi 22 RQ).
Proof.
  induction n as [n IH] using N_strong_ind.
  intros z hnoZ hIZ.
  destruct (t1_l0_decomp (countB z) z eq_refl hnoZ hIZ)
    as [[W [ht1 [hnoW [hwW hpW]]]] |
        [P0 [R0 [ht1 [hnoP0 [hcbP0 [hwP0 [hnoR0 [htzR0 [hnhR0 [hIR0 [ec2 [ec0 ec22]]]]]]]]]]]]].
  - left. exists W, (t0Pow n W).
    refine (conj ht1 (conj (RelT0Pow_t0Pow n hnoW) (conj (noK1_t0Pow n hnoW) _))).
    rewrite (evalPhi_t0Pow 0 n hnoW), (evalPhi_t0Pow 22 n hnoW); split; lia.
  - assert (hpowP0 : 2 ^ countBin P0 = 2) by (rewrite hcbP0; reflexivity).
    destruct (N.ltb n 2) eqn:En2.
    + apply N.ltb_lt in En2.
      assert (hdiv0 : (evalPhi 0 P0 + n) / (2 ^ countBin P0) = 0)
        by (rewrite hwP0, hpowP0, N.add_0_l; exact (N.div_small n 2 En2)).
      assert (hmod : (evalPhi 0 P0 + n) mod (2 ^ countBin P0) = n)
        by (rewrite hwP0, hpowP0, N.add_0_l; exact (N.mod_small n 2 En2)).
      assert (h0rel : RelT0Pow ((evalPhi 0 P0 + n) / (2 ^ countBin P0)) ([Tok1] ++ R0) ([Tok1] ++ R0))
        by (rewrite hdiv0; exact (rt0_zero _)).
      destruct (RelT0Pow_prefix_div P0 hnoP0 n h0rel)
        as [PQ [hrel [hnoPQ [hcbPQ [hdbPQ [hwPQ [_ _]]]]]]].
      right. exists (P0 ++ [Tok1] ++ R0), PQ, R0.
      refine (conj ht1 (conj hrel (conj hnoPQ (conj _ (conj _
        (conj hnoR0 (conj htzR0 (conj hnhR0 (conj hIR0 _))))))))).
      * lia.
      * rewrite hwPQ, hmod, hcbPQ, hpowP0; lia.
      * rewrite hcbPQ, hpowP0, hdbPQ; repeat split; lia.
    + apply N.ltb_ge in En2.
      destruct (div_mod_spec n 2 ltac:(lia)) as [q [r [hq_eq [hr_eq [hqr hr_lt]]]]].
      assert (hq_ge : 1 <= q) by lia.
      assert (hqm1_lt : q - 1 < n) by lia.
      assert (hdiv_eq : (evalPhi 0 P0 + n) / (2 ^ countBin P0) = q)
        by (rewrite hwP0, hpowP0, N.add_0_l; exact hq_eq).
      assert (hmod_eq : (evalPhi 0 P0 + n) mod (2 ^ countBin P0) = r)
        by (rewrite hwP0, hpowP0, N.add_0_l; exact hr_eq).
      destruct (IH (q - 1) hqm1_lt R0 hnoR0 hIR0)
        as [[Wsub [Qsub [ht1_sub [hpow_sub [hnoQsub [hwQsub hpQsub]]]]]] |
            [Wsub [Psub [RQ [ht1_sub [hpow_sub [hnoPsub [hcbPsub [hwPsub
              [hnoRQ [htzRQ [hnhRQ [hIRQ [s2 [s0 s22]]]]]]]]]]]]]]].
      * assert (hq_rel : RelT0Pow ((evalPhi 0 P0 + n) / (2 ^ countBin P0)) ([Tok1] ++ R0) Qsub).
        { rewrite hdiv_eq. replace q with ((q - 1) + 1) by lia.
          exact (rt0_succ (rt_t0_k1 ht1_sub) hpow_sub). }
        destruct (RelT0Pow_prefix_div P0 hnoP0 n hq_rel)
          as [P' [hrel [hnoP' [hcbP' [hdbP' [hwP' [_ _]]]]]]].
        left. exists (P0 ++ [Tok1] ++ R0), (P' ++ Qsub).
        refine (conj ht1 (conj hrel (conj _ _))).
        -- rewrite noK1_append, hnoP', hnoQsub; reflexivity.
        -- rewrite (evalPhi_append 0), (evalPhi_append 22), (evalPhi_eq_zero_add_deltaB 22 P'),
                   hcbP', hcbP0, hdbP', hwP', hmod_eq.
           change (2 ^ 1) with 2.
           split; lia.
      * assert (hq_rel : RelT0Pow ((evalPhi 0 P0 + n) / (2 ^ countBin P0)) ([Tok1] ++ R0) (Psub ++ [Tok1] ++ RQ)).
        { rewrite hdiv_eq. replace q with ((q - 1) + 1) by lia.
          exact (rt0_succ (rt_t0_k1 ht1_sub) hpow_sub). }
        destruct (RelT0Pow_prefix_div P0 hnoP0 n hq_rel)
          as [P' [hrel [hnoP' [hcbP' [hdbP' [hwP' [_ _]]]]]]].
        set (PQ := P' ++ Psub).
        assert (hnoPQ : noK1 PQ = true) by (unfold PQ; rewrite noK1_append, hnoP', hnoPsub; reflexivity).
        assert (hcbPQ : countBin PQ = countBin Psub + 1)
          by (unfold PQ; rewrite countBin_append, hcbP', hcbP0; lia).
        assert (hpowPQ : 2 ^ countBin PQ = 2 * (2 ^ countBin Psub))
          by (rewrite hcbPQ, pow2_succ; reflexivity).
        assert (hdbPQ : deltaB PQ = deltaB P0 + 2 * deltaB Psub)
          by (unfold PQ; rewrite deltaB_append, hdbP', hcbP', hcbP0; reflexivity).
        assert (hwPQ : evalPhi 0 PQ = r + 2 * evalPhi 0 Psub)
          by (unfold PQ; rewrite (evalPhi_append 0), hwP', hmod_eq, hcbP', hcbP0; reflexivity).
        right. exists (P0 ++ [Tok1] ++ R0), PQ, RQ.
        refine (conj ht1 (conj _ (conj hnoPQ (conj _ (conj _
          (conj hnoRQ (conj htzRQ (conj hnhRQ (conj hIRQ _))))))))).
        -- unfold PQ; rewrite <- app_assoc; exact hrel.
        -- lia.
        -- lia.
        -- rewrite hpowPQ, hdbPQ; repeat split.
           ++ rewrite ec2, s2; ring.
           ++ replace (2 * (2 ^ countBin Psub) * evalPhi 0 RQ) with (2 * ((2 ^ countBin Psub) * evalPhi 0 RQ)) by ring; lia.
           ++ rewrite ec22, s22; ring.
Qed.

Local Lemma collar_step_inC1 {k_col : N} {M W Qw u1 u2 : list BecTok1}
    (hK : 1 <= k_col) (ht1 : RelT M1 M W) (hpow : RelT0Pow (k_col - 1) W Qw)
    (hs1 : RelT M0 Qw u1) (hs2 : RelT M0 u1 u2) :
  cfgCollar k_col (TokI :: Tok1 :: M) -->+
    cfgCollar (k_col + 1 + leadB (norm1 u2)) (dropB (norm1 u2)).
Proof.
  assert (hk_rel : RelT0Pow k_col (Tok1 :: M) Qw).
  { replace k_col with ((k_col - 1) + 1) by lia. exact (rt0_succ (rt_t0_k1 ht1) hpow). }
  pose proof (proj2 (proj2 (RelT0Pow_bit hk_rel))) as h2k.
  pose proof (collar_step k_col h2k (rt_t1_kI hs1) (rt_t0_kB hs2)) as hstep.
  change (norm1 (TokB :: u2)) with (TokB :: norm1 u2) in hstep.
  cbn [leadB dropB] in hstep.
  replace (k_col + (leadB (norm1 u2) + 1)) with (k_col + 1 + leadB (norm1 u2)) in hstep by lia.
  exact hstep.
Qed.

Local Lemma branch2_absorbed_step {k_col : N} {M W Qw : list BecTok1}
    (hK : 64 <= k_col) (hwM : 2 * evalPhi 0 M < 7 * k_col) (hpM : evalPhi 22 M < 52 * k_col)
    (ht1 : RelT M1 M W) (hpow : RelT0Pow (k_col - 1) W Qw)
    (hnoQ : noK1 Qw = true)
    (hwQ : 2 * evalPhi 0 Qw <= evalPhi 2 M + 2 * (k_col - 1) + 1)
    (hpQ : 10 * evalPhi 22 Qw <= 11 * evalPhi 22 M + 420 * (k_col - 1) + 418) :
  exists k_col' tail', cfgCollar k_col (TokI :: Tok1 :: M) -->+ cfgCollar k_col' tail' /\
    InC0 k_col' tail'.
Proof.
  set (u1 := t0One Qw).
  set (u2 := t0One u1).
  pose proof (RelT_t0One hnoQ) as hs1.
  pose proof (noK1_t0One hnoQ) as hno1.
  pose proof (RelT_t0One hno1) as hs2.
  pose proof (noK1_t0One hno1) as hno2.
  assert (hK1 : 1 <= k_col) by lia.
  pose proof (collar_step_inC1 hK1 ht1 hpow hs1 hs2) as hstep.
  exists (k_col + 1 + leadB (norm1 u2)), (dropB (norm1 u2)).
  refine (conj hstep _).
  pose proof (conservation_22 M) as hcons.
  assert (hw_u2 : evalPhi 0 (norm1 u2) = evalPhi 0 Qw + 2)
    by (unfold u2, u1; rewrite (evalPhi_norm1_of_noK1 0 hno2), (evalPhi_t0One 0 hno1), (evalPhi_t0One 0 hnoQ); lia).
  assert (hp_u2 : evalPhi 22 (norm1 u2) = evalPhi 22 Qw + 2)
    by (unfold u2, u1; rewrite (evalPhi_norm1_of_noK1 22 hno2), (evalPhi_t0One 22 hno1), (evalPhi_t0One 22 hnoQ); lia).
  pose proof (evalPhi_leadB_dropB 0 (norm1 u2)) as hw_dr.
  pose proof (evalPhi_leadB_dropB 22 (norm1 u2)) as hp_dr.
  unfold InC0.
  refine (conj _ (conj (noK1_dropB (noK1_norm1 hno2)) (conj (noTrailZero_dropB (noTrailZero_norm1 u2)) _))); lia.
Qed.

(* Forward length-stratified generator for allRQ (74 canonical R_Q words) *)

Definition isEmptyWord (w : list BecTok1) : bool :=
  match w with [] => true | _ => false end.

Definition extendL0Word (xs : list BecTok1) : list (list BecTok1) :=
  let r2 :=
    let w := TokB :: xs in
    if (evalPhi 2 w <=? 15) && (evalPhi 22 w <=? 103) then [w] else [] in
  let r1 :=
    let w := TokI :: xs in
    if (evalPhi 2 w <=? 15) && (evalPhi 22 w <=? 103) then w :: r2 else r2 in
  if isEmptyWord xs then r1
  else
    let w := Tok0 :: xs in
    if (evalPhi 2 w <=? 15) && (evalPhi 22 w <=? 103) then w :: r1 else r1.

Fixpoint stepAndCollect (cur : list (list BecTok1)) : list (list BecTok1) * list (list BecTok1) :=
  match cur with
  | [] => ([], [])
  | xs :: rest =>
    let '(nxt, rqs) := stepAndCollect rest in
    (extendL0Word xs ++ nxt, if notHeadI xs && hasI xs then xs :: rqs else rqs)
  end.

Fixpoint genRQIter (k : nat) (cur : list (list BecTok1)) : list (list BecTok1) :=
  match k with
  | O => List.filter (fun w => notHeadI w && hasI w) cur
  | S k' =>
    let '(nxt, rqs) := stepAndCollect cur in
    rqs ++ genRQIter k' nxt
  end.

Definition allRQ : list (list BecTok1) := genRQIter 15%nat [[]].

Local Lemma evalPhi_two_pos_of_nonempty {w : list BecTok1}
    (hno : noK1 w = true) (htz : noTrailZero w = true) (hne : w <> []) :
  1 <= evalPhi 2 w.
Proof.
  induction w as [| t xs IH]; [contradiction |].
  destruct t; try discriminate hno.
  - cbn [noK1] in hno.
    destruct xs as [| u ys]; [discriminate htz |].
    assert (htz' : noTrailZero (u :: ys) = true) by exact htz.
    specialize (IH hno htz' ltac:(discriminate)).
    change (evalPhi 2 (Tok0 :: u :: ys)) with (2 * evalPhi 2 (u :: ys)); lia.
  - cbn [evalPhi]; lia.
  - cbn [evalPhi]; lia.
Qed.

Local Lemma length_le_evalPhi_two {w : list BecTok1}
    (hno : noK1 w = true) (htz : noTrailZero w = true) :
  N.of_nat (List.length w) <= evalPhi 2 w.
Proof.
  induction w as [| t xs IH]; [cbn; lia |].
  destruct t; try discriminate hno; cbn [noK1] in hno.
  - destruct xs as [| u ys]; [discriminate htz |].
    assert (htz' : noTrailZero (u :: ys) = true) by exact htz.
    pose proof (IH hno htz') as ihx.
    pose proof (evalPhi_two_pos_of_nonempty hno htz' ltac:(discriminate)) as hpos.
    change (List.length (Tok0 :: u :: ys)) with (S (List.length (u :: ys))).
    change (evalPhi 2 (Tok0 :: u :: ys)) with (2 * evalPhi 2 (u :: ys)).
    lia.
  - assert (htz' : noTrailZero xs = true) by (destruct xs; [reflexivity | exact htz]).
    pose proof (IH hno htz') as ihx. cbn [List.length evalPhi]; lia.
  - assert (htz' : noTrailZero xs = true) by (destruct xs; [reflexivity | exact htz]).
    pose proof (IH hno htz') as ihx. cbn [List.length evalPhi]; lia.
Qed.

Definition L0Bounded (d : nat) (w : list BecTok1) : Prop :=
  List.length w = d /\ noK1 w = true /\ noTrailZero w = true /\
  evalPhi 2 w <= 15 /\ evalPhi 22 w <= 103.

Local Lemma mem_extendL0Word {t : BecTok1} {xs : list BecTok1}
    (hno : noK1 (t :: xs) = true) (htz : noTrailZero (t :: xs) = true)
    (h2 : evalPhi 2 (t :: xs) <= 15) (h22 : evalPhi 22 (t :: xs) <= 103) :
  In (t :: xs) (extendL0Word xs).
Proof.
  assert (hb : ((evalPhi 2 (t :: xs) <=? 15) && (evalPhi 22 (t :: xs) <=? 103)) = true)
    by (apply Bool.andb_true_iff; split; apply N.leb_le; assumption).
  unfold extendL0Word.
  destruct t; try discriminate hno.
  - assert (hne : isEmptyWord xs = false)
      by (destruct xs; [discriminate htz | reflexivity]).
    rewrite hne, hb. left; reflexivity.
  - rewrite hb.
    destruct (isEmptyWord xs); [left; reflexivity |].
    destruct ((evalPhi 2 (Tok0 :: xs) <=? 15) && (evalPhi 22 (Tok0 :: xs) <=? 103));
      [right; left; reflexivity | left; reflexivity].
  - rewrite hb.
    assert (hmem1 : In (TokB :: xs)
      (if (evalPhi 2 (TokI :: xs) <=? 15) && (evalPhi 22 (TokI :: xs) <=? 103)
       then (TokI :: xs) :: [TokB :: xs] else [TokB :: xs])).
    { destruct ((evalPhi 2 (TokI :: xs) <=? 15) && (evalPhi 22 (TokI :: xs) <=? 103));
        [right; left; reflexivity | left; reflexivity]. }
    destruct (isEmptyWord xs); [exact hmem1 |].
    destruct ((evalPhi 2 (Tok0 :: xs) <=? 15) && (evalPhi 22 (Tok0 :: xs) <=? 103));
      [right; exact hmem1 | exact hmem1].
Qed.

Local Lemma stepAndCollect_spec (cur : list (list BecTok1)) :
  (forall xs, In xs cur -> forall u, In u (extendL0Word xs) -> In u (fst (stepAndCollect cur))) /\
  (forall w, In w cur -> notHeadI w = true -> hasI w = true -> In w (snd (stepAndCollect cur))).
Proof.
  induction cur as [| x rest [ih1 ih2]]; [cbn; split; intros; contradiction |].
  cbn [stepAndCollect]. destruct (stepAndCollect rest) as [nxt rqs]; cbn [fst snd] in *.
  split.
  - intros xs [<- | hmem] u hu; apply in_or_app; [left; exact hu | right; exact (ih1 xs hmem u hu)].
  - intros w [<- | hmem] hnh hI.
    + rewrite hnh, hI; left; reflexivity.
    + destruct (notHeadI x && hasI x); [right; exact (ih2 w hmem hnh hI) | exact (ih2 w hmem hnh hI)].
Qed.

Local Lemma stepAndCollect_layer {d : nat} {cur : list (list BecTok1)}
    (hcur : forall u, L0Bounded d u -> In u cur) :
  forall w, L0Bounded (S d) w -> In w (fst (stepAndCollect cur)).
Proof.
  intros [| t xs] [hlen [hno [htz [h2 h22]]]]; [discriminate hlen |].
  injection hlen as hlen'.
  assert (hno' : noK1 xs = true) by (destruct t; try discriminate hno; exact hno).
  assert (htz' : noTrailZero xs = true).
  { destruct t; [destruct xs; [discriminate htz | exact htz] | ..];
      (destruct xs; [reflexivity | exact htz]). }
  assert (h2' : evalPhi 2 xs <= 15) by (destruct t; try discriminate hno; cbn [evalPhi] in h2; lia).
  assert (h22' : evalPhi 22 xs <= 103) by (destruct t; try discriminate hno; cbn [evalPhi] in h22; lia).
  exact (proj1 (stepAndCollect_spec cur) xs (hcur xs (conj hlen' (conj hno' (conj htz' (conj h2' h22')))))
           (t :: xs) (mem_extendL0Word hno htz h2 h22)).
Qed.

Local Lemma genRQIter_complete :
  forall (k d : nat) (cur : list (list BecTok1)) (w : list BecTok1),
    (forall u, L0Bounded d u -> In u cur) ->
    (d <= List.length w)%nat -> (List.length w <= d + k)%nat ->
    noK1 w = true -> noTrailZero w = true ->
    evalPhi 2 w <= 15 -> evalPhi 22 w <= 103 ->
    notHeadI w = true -> hasI w = true ->
    In w (genRQIter k cur).
Proof.
  induction k as [| k IH]; intros d cur w hcur hd1 hd2 hno htz h2 h22 hnh hI; cbn [genRQIter].
  - assert (hlen : List.length w = d) by lia.
    apply filter_In; split; [exact (hcur w (conj hlen (conj hno (conj htz (conj h2 h22))))) | rewrite hnh, hI; reflexivity].
  - destruct (stepAndCollect cur) as [nxt rqs] eqn:Hsc.
    pose proof (stepAndCollect_spec cur) as [_ hsc2].
    pose proof (stepAndCollect_layer hcur) as hlayer.
    rewrite Hsc in hsc2, hlayer; cbn [fst snd] in hsc2, hlayer.
    apply in_or_app.
    destruct (Nat.eq_dec (List.length w) d) as [Heq | Hne].
    + left. exact (hsc2 w (hcur w (conj Heq (conj hno (conj htz (conj h2 h22))))) hnh hI).
    + right. exact (IH (S d) nxt w hlayer ltac:(lia) ltac:(lia) hno htz h2 h22 hnh hI).
Qed.

Local Lemma allRQ_complete {w : list BecTok1}
    (hno : noK1 w = true) (htz : noTrailZero w = true)
    (hnh : notHeadI w = true) (hI : hasI w = true)
    (h2 : evalPhi 2 w <= 15) (h22 : evalPhi 22 w <= 103) :
  In w allRQ.
Proof.
  pose proof (length_le_evalPhi_two hno htz) as Hlen.
  unfold allRQ.
  apply (genRQIter_complete 15%nat 0%nat [[]] w); try assumption; try lia.
  intros [| t xs] [hlen _]; [left; reflexivity | discriminate hlen].
Qed.

#[local] Arguments genRQIter : simpl never.


(* ========================================================================== *)
(* Layer 3b: SymWaveNode, JBounds, MemoTree, verifyWaveNode, checkOneRQ       *)
(* ========================================================================== *)

Definition wordFuel : nat := 32%nat.

Definition t1Norm (fuel : nat) (xs : list BecTok1) : option (list BecTok1) :=
  match execT fuel 1%nat 0 xs with
  | None => None
  | Some ys => Some (norm1 ys)
  end.

Record JBounds := mkJBounds {
  jb_at1 : N;
  jb_at2 : N;
  jb_at3 : N;
  jb_at4 : N;
  jb_u5_u : N;
  jb_u5_c : Z;
  jb_inf_u : N;
  jb_inf_c : Z
}.

Definition emptyJB : JBounds := mkJBounds 0 0 0 0 0 0%Z 0 0%Z.

Record SymWaveNode := mkWaveNode {
  nd_s : N;
  nd_db_shift : N;
  nd_has_i1_front : bool;
  nd_k_lo_u : N;
  nd_k_lo_c : Z;
  nd_k_hi_u : N;
  nd_k_hi_c : Z;
  nd_w_lo_u : N;
  nd_w_lo_c : Z;
  nd_w_hi_u : N;
  nd_w_hi_c : Z;
  nd_extra_B : N;
  nd_scaled_db_u : N;
  nd_scaled_db_c : N;
  nd_kj_hi_u : N;
  nd_kj_hi_c : Z;
  nd_wj_k : N;
  nd_wj_hi_u : N;
  nd_wj_hi_c : Z;
  nd_jb : JBounds;
  nd_Y : list BecTok1;
  nd_wRQ : N;
  nd_pRQ : N
}.

Definition tokCode (t : BecTok1) : N :=
  match t with Tok0 => 0 | TokI => 1 | Tok1 => 2 | TokB => 3 end.

Definition eqTok1 (a b : BecTok1) : bool :=
  match a, b with
  | Tok0, Tok0 | TokI, TokI | Tok1, Tok1 | TokB, TokB => true
  | _, _ => false
  end.

Fixpoint eqWord1 (a b : list BecTok1) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => eqTok1 x y && eqWord1 xs ys
  | _, _ => false
  end.

Inductive MemoColor := CRed | CBlk.

Inductive MemoTree :=
  | MLeaf
  | MNode (c : MemoColor) (l : MemoTree) (hk : N) (vals : list SymWaveNode) (r : MemoTree).

Definition balance (c : MemoColor) (l : MemoTree) (k : N) (v : list SymWaveNode) (r : MemoTree) : MemoTree :=
  match c, l, k, v, r with
  | CBlk, MNode CRed (MNode CRed a xk xv b) yk yv cc, zk, zv, d =>
    MNode CRed (MNode CBlk a xk xv b) yk yv (MNode CBlk cc zk zv d)
  | CBlk, MNode CRed a xk xv (MNode CRed b yk yv cc), zk, zv, d =>
    MNode CRed (MNode CBlk a xk xv b) yk yv (MNode CBlk cc zk zv d)
  | CBlk, a, xk, xv, MNode CRed (MNode CRed b yk yv cc) zk zv d =>
    MNode CRed (MNode CBlk a xk xv b) yk yv (MNode CBlk cc zk zv d)
  | CBlk, a, xk, xv, MNode CRed b yk yv (MNode CRed cc zk zv d) =>
    MNode CRed (MNode CBlk a xk xv b) yk yv (MNode CBlk cc zk zv d)
  | _, _, _, _, _ => MNode c l k v r
  end.

Definition toNatClip (x : Z) : N := Z.to_N x.

Definition cdivNat (x : Z) (d : N) : Z :=
  if (d =? 0)%N then 0%Z
  else if (0 <=? x)%Z then (x / Z.of_N d)%Z
  else (- ((- x) / Z.of_N d))%Z.

Definition fdivNat (x : Z) (d : N) : Z :=
  if (d =? 0)%N then 0%Z else (x / Z.of_N d)%Z.

Definition addJBound (jb : JBounds) (ju jc : Z) : JBounds :=
  let a1 := N.max (jb_at1 jb) (toNatClip (ju + jc)%Z) in
  let a2 := N.max (jb_at2 jb) (toNatClip (2 * ju + jc)%Z) in
  let a3 := N.max (jb_at3 jb) (toNatClip (3 * ju + jc)%Z) in
  let a4 := N.max (jb_at4 jb) (toNatClip (4 * ju + jc)%Z) in
  if (0 <? ju)%Z || ((ju =? 0)%Z && (0 <? jc)%Z) then
    let juNat := Z.to_N ju in
    let lhs5 := (Z.of_N (5 * juNat) + jc)%Z in
    let rhs5 := (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb)%Z in
    let upd5 := (rhs5 <? lhs5)%Z || ((lhs5 =? rhs5)%Z && (jb_u5_u jb <? juNat)) in
    let updi := (jb_inf_u jb <? juNat) || ((juNat =? jb_inf_u jb) && (jb_inf_c jb <? jc)%Z) in
    let u5u := if upd5 then juNat else jb_u5_u jb in
    let u5c := if upd5 then jc else jb_u5_c jb in
    let iu := if updi then juNat else jb_inf_u jb in
    let ic := if updi then jc else jb_inf_c jb in
    mkJBounds a1 a2 a3 a4 u5u u5c iu ic
  else
    mkJBounds a1 a2 a3 a4 (jb_u5_u jb) (jb_u5_c jb) (jb_inf_u jb) (jb_inf_c jb).

Definition holdsAtU (K0 : N) (alpha beta0 gamma0 : Z) (jCoeff jv : N)
    (k_lo_u : N) (k_lo_c : Z) (k_hi_u : N) (k_hi_c : Z) (u : N) : bool :=
  let klo := Z.max (Z.of_N K0) (Z.of_N (k_lo_u * u) + k_lo_c)%Z in
  let khi := (Z.of_N (k_hi_u * u) + k_hi_c)%Z in
  if (klo <=? khi)%Z then
    let base := (Z.of_N u * beta0 + gamma0 - Z.of_N (jCoeff * jv))%Z in
    ((alpha * klo + base <=? 0)%Z && (alpha * khi + base <=? 0)%Z)
  else true.

Definition holdsLinearAllUK (K0 : N) (alpha beta gamma : Z)
    (k_lo_u : N) (k_lo_c : Z) (k_hi_u : N) (k_hi_c : Z) : bool :=
  holdsAtU K0 alpha beta gamma 0 0 k_lo_u k_lo_c k_hi_u k_hi_c 1 &&
  holdsAtU K0 alpha beta gamma 0 0 k_lo_u k_lo_c k_hi_u k_hi_c 2 &&
  holdsAtU K0 alpha beta gamma 0 0 k_lo_u k_lo_c k_hi_u k_hi_c 3 &&
  holdsAtU K0 alpha beta gamma 0 0 k_lo_u k_lo_c k_hi_u k_hi_c 4 &&
  let age := (0 <=? alpha)%Z in
  let ku := if age then k_hi_u else k_lo_u in
  let kc := if age then k_hi_c else k_lo_c in
  let c1 := (Z.of_N ku * alpha + beta)%Z in
  let cz := (alpha * kc + gamma)%Z in
  (c1 <=? 0)%Z && (5 * c1 + cz <=? 0)%Z.

Definition holdsWithJBounds (K0 : N) (alpha beta0 gamma0 : Z) (jCoeff : N) (jb : JBounds)
    (k_lo_u : N) (k_lo_c : Z) (k_hi_u : N) (k_hi_c : Z) : bool :=
  holdsAtU K0 alpha beta0 gamma0 jCoeff (jb_at1 jb) k_lo_u k_lo_c k_hi_u k_hi_c 1 &&
  holdsAtU K0 alpha beta0 gamma0 jCoeff (jb_at2 jb) k_lo_u k_lo_c k_hi_u k_hi_c 2 &&
  holdsAtU K0 alpha beta0 gamma0 jCoeff (jb_at3 jb) k_lo_u k_lo_c k_hi_u k_hi_c 3 &&
  holdsAtU K0 alpha beta0 gamma0 jCoeff (jb_at4 jb) k_lo_u k_lo_c k_hi_u k_hi_c 4 &&
  let age := (0 <=? alpha)%Z in
  let ku := if age then k_hi_u else k_lo_u in
  let kc := if age then k_hi_c else k_lo_c in
  let base_u := (Z.of_N ku * alpha + beta0)%Z in
  let base_c := (alpha * kc + gamma0)%Z in
  let c1_5 := (base_u - Z.of_N (jCoeff * jb_u5_u jb))%Z in
  let cz_5 := (base_c - Z.of_N jCoeff * jb_u5_c jb)%Z in
  let c1_i := (base_u - Z.of_N (jCoeff * jb_inf_u jb))%Z in
  let cz_i := (base_c - Z.of_N jCoeff * jb_inf_c jb)%Z in
  (((c1_5 <=? 0)%Z && (5 * c1_5 + cz_5 <=? 0)%Z) ||
   ((c1_i <=? 0)%Z && (5 * c1_i + cz_i <=? 0)%Z)).

Definition floorMinU1 (num_u num_c : Z) (den_u : N) : N :=
  let b0 := if (0 <=? num_u)%Z then (toNatClip num_u) / den_u else 0 in
  if (num_c <? 0)%Z then
    let v1 := (num_u + num_c)%Z in
    if (0 <=? v1)%Z then (toNatClip v1) / den_u else 0
  else b0.

Definition floorMaxU1 (num_u num_c : Z) (den_u : N) : N :=
  if (num_c <=? 0)%Z then
    if (0 <=? num_u)%Z then (toNatClip num_u) / den_u else 0
  else
    let v1 := (num_u + num_c)%Z in
    if (0 <=? v1)%Z then (toNatClip v1) / den_u else 0.

Definition pow2N (n : N) : N := N.shiftl 1 n.
Definition msOf (s : N) : N := N.shiftr 64 s.

Fixpoint encodeWordN (w : list BecTok1) : N :=
  match w with
  | [] => 0
  | t :: ts => encodeWordN ts * 5 + tokCode t + 1
  end.

Definition z2n (z : Z) : N :=
  if (0 <=? z)%Z then 2 * Z.to_N z else 3 * Z.to_N (- z)%Z.

Definition hashNode (nd : SymWaveNode) : N :=
  let m := 65521 in
  let mix (h v : N) : N := (h * 257 + (v mod 65521) + 17) mod m in
  let h := mix 53 (nd_s nd + nd_db_shift nd * 16 + (if nd_has_i1_front nd then 256 else 0)) in
  let h := mix h (nd_k_lo_u nd + 257 * z2n (nd_k_lo_c nd)) in
  let h := mix h (nd_k_hi_u nd + 257 * z2n (nd_k_hi_c nd)) in
  let h := mix h (nd_w_lo_u nd + 257 * z2n (nd_w_lo_c nd)) in
  let h := mix h (nd_w_hi_u nd + 257 * z2n (nd_w_hi_c nd)) in
  let h := mix h (nd_extra_B nd + 257 * nd_scaled_db_u nd + 65537 * nd_scaled_db_c nd) in
  let h := mix h (nd_kj_hi_u nd + 257 * z2n (nd_kj_hi_c nd)) in
  let h := mix h (nd_wj_k nd + 257 * nd_wj_hi_u nd + 65537 * z2n (nd_wj_hi_c nd)) in
  let jb := nd_jb nd in
  let h := mix h (jb_at1 jb + 3 * jb_at4 jb + 7 * jb_u5_u jb + 11 * z2n (jb_u5_c jb) +
                  13 * jb_inf_u jb + 17 * z2n (jb_inf_c jb)) in
  let h := mix h (encodeWordN (nd_Y nd)) in
  mix h (nd_wRQ nd + 1024 * nd_pRQ nd).

Definition eqJB (a b : JBounds) : bool :=
  (jb_at1 a =? jb_at1 b) && (jb_at2 a =? jb_at2 b) &&
  (jb_at3 a =? jb_at3 b) && (jb_at4 a =? jb_at4 b) &&
  (jb_u5_u a =? jb_u5_u b) && (jb_u5_c a =? jb_u5_c b)%Z &&
  (jb_inf_u a =? jb_inf_u b) && (jb_inf_c a =? jb_inf_c b)%Z.

Definition eqWaveNode (a b : SymWaveNode) : bool :=
  eqWord1 (nd_Y a) (nd_Y b) &&
  (nd_s a =? nd_s b) && (nd_db_shift a =? nd_db_shift b) &&
  Bool.eqb (nd_has_i1_front a) (nd_has_i1_front b) &&
  (nd_k_lo_u a =? nd_k_lo_u b) && (nd_k_lo_c a =? nd_k_lo_c b)%Z &&
  (nd_k_hi_u a =? nd_k_hi_u b) && (nd_k_hi_c a =? nd_k_hi_c b)%Z &&
  (nd_w_lo_u a =? nd_w_lo_u b) && (nd_w_lo_c a =? nd_w_lo_c b)%Z &&
  (nd_w_hi_u a =? nd_w_hi_u b) && (nd_w_hi_c a =? nd_w_hi_c b)%Z &&
  (nd_extra_B a =? nd_extra_B b) &&
  (nd_scaled_db_u a =? nd_scaled_db_u b) && (nd_scaled_db_c a =? nd_scaled_db_c b) &&
  (nd_kj_hi_u a =? nd_kj_hi_u b) && (nd_kj_hi_c a =? nd_kj_hi_c b)%Z &&
  (nd_wj_k a =? nd_wj_k b) && (nd_wj_hi_u a =? nd_wj_hi_u b) &&
  (nd_wj_hi_c a =? nd_wj_hi_c b)%Z &&
  eqJB (nd_jb a) (nd_jb b) &&
  (nd_wRQ a =? nd_wRQ b) && (nd_pRQ a =? nd_pRQ b).

Fixpoint listHasNode (nd : SymWaveNode) (vs : list SymWaveNode) : bool :=
  match vs with
  | [] => false
  | x :: xs => if eqWaveNode nd x then true else listHasNode nd xs
  end.

Fixpoint memoContainsAux (hk : N) (nd : SymWaveNode) (m : MemoTree) : bool :=
  match m with
  | MLeaf => false
  | MNode _ l k vs r =>
    if hk <? k then memoContainsAux hk nd l
    else if k <? hk then memoContainsAux hk nd r
    else listHasNode nd vs
  end.

Definition memoContains (m : MemoTree) (nd : SymWaveNode) : bool :=
  memoContainsAux (hashNode nd) nd m.

Fixpoint insAux (hk : N) (nd : SymWaveNode) (m : MemoTree) : MemoTree :=
  match m with
  | MLeaf => MNode CRed MLeaf hk [nd] MLeaf
  | MNode c l k vs r =>
    if hk <? k then balance c (insAux hk nd l) k vs r
    else if k <? hk then balance c l k vs (insAux hk nd r)
    else if listHasNode nd vs then MNode c l k vs r
    else MNode c l k (nd :: vs) r
  end.

Definition memoInsert (m : MemoTree) (nd : SymWaveNode) : MemoTree :=
  match insAux (hashNode nd) nd m with
  | MLeaf => MLeaf
  | MNode _ l k vs r => MNode CBlk l k vs r
  end.

Definition twoDInitHiU (nd : SymWaveNode) : N :=
  let u1 := 64 * nd_wRQ nd in
  let diff := (Z.of_N (52 * nd_k_hi_u nd) - Z.of_N (64 * nd_pRQ nd))%Z in
  let u2 := toNatClip (cdivNat diff 10 + 1)%Z in
  N.min u1 u2.

Definition checkAbstract (nd : SymWaveNode) (isL0 isHI : bool) (wy py_hi : N) : bool :=
  if negb isL0 then false
  else if nd_has_i1_front nd && negb isHI then false
  else
    let ms := msOf (nd_s nd) in
    let denom := 20 * pow2N (nd_db_shift nd) in
    let gw := if nd_has_i1_front nd then 7 else 10 in
    let ap := if nd_has_i1_front nd then 52 else 101 in
    let wAlpha := (- Z.of_N (2 * gw))%Z in
    let wBeta := Z.of_N (4 * (nd_w_hi_u nd + ms * wy)) in
    let wGamma := (4 * nd_w_hi_c nd + 2 - Z.of_N (2 * gw * nd_extra_B nd))%Z in
    if negb (holdsWithJBounds 64 wAlpha wBeta wGamma gw (nd_jb nd)
               (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) then false
    else
      let ba := (Z.of_N (2 * 22 * 52) - Z.of_N (2 * denom * ap))%Z in
      let bb := (Z.of_N (2 * (denom * (nd_w_hi_u nd + ms * py_hi) + 440 * nd_scaled_db_u nd)) -
                 Z.of_N (2 * 64 * 22 * nd_pRQ nd))%Z in
      let bg1 := (Z.of_N (2 * denom) * (nd_w_hi_c nd + 1 - Z.of_N (ap * nd_extra_B nd)))%Z in
      let bg2 := (Z.of_N (2 * 22 * 20 * nd_scaled_db_c nd) - Z.of_N (2 * 22))%Z in
      let bg := (bg1 + bg2)%Z in
      let jCoeff := 440 + denom * ap in
      holdsWithJBounds 64 ba bb bg jCoeff (nd_jb nd)
        (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd).

Definition dominantJuMin (jb : JBounds) (jc0 : Z) : N :=
  let m0 := N.max (toNatClip (- jc0)%Z) (N.max (jb_u5_u jb + 1) (jb_inf_u jb + 1)) in
  let r1 := toNatClip (Z.of_N (jb_at1 jb) - jc0)%Z in
  let r2 := (toNatClip (Z.of_N (jb_at2 jb) - jc0)%Z + 1) / 2 in
  let r3 := (toNatClip (Z.of_N (jb_at3 jb) - jc0)%Z + 2) / 3 in
  let r4 := (toNatClip (Z.of_N (jb_at4 jb) - jc0)%Z + 3) / 4 in
  let r5 := (toNatClip (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb - jc0)%Z + 4) / 5 in
  N.max m0 (N.max (N.max r1 r2) (N.max r3 (N.max r4 r5))).

Fixpoint findL0AnchorWalk (fuel : nat) (y_cur : list BecTok1) (q_cur q_max : N)
    : option (N * N * N) :=
  match fuel with
  | O => None
  | S fuel' =>
    if q_max <? q_cur then None
    else if noK1 y_cur && hasI y_cur then
      Some (q_cur, evalPhi 0 y_cur, evalPhi 22 y_cur)
    else if (Nat.eqb fuel' 0%nat) || (q_max <? q_cur + 1) then None
    else
      match t0PowNorm wordFuel 1 y_cur with
      | Some y_next => findL0AnchorWalk fuel' y_next (q_cur + 1) q_max
      | None => None
      end
  end.

Definition findL0Anchor (fuel : nat) (w_y : list BecTok1) (q_cur q_max : N)
    : option (N * N * N) :=
  if q_max <? q_cur then None
  else
    match t0PowNorm wordFuel q_cur w_y with
    | Some y_cur => findL0AnchorWalk fuel y_cur q_cur q_max
    | None => None
    end.

Definition withJB (nd : SymWaveNode) (jb' : JBounds) : SymWaveNode :=
  mkWaveNode (nd_s nd) (nd_db_shift nd) (nd_has_i1_front nd)
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    (nd_w_lo_u nd) (nd_w_lo_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
    (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    jb' (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd).

Definition findChildQStop (nxTpl : SymWaveNode)
    (ms k_hi_u : N) (k_hi_c : Z) (w_hi_u : N) (w_hi_c : Z) (extra_B_parent : N)
    (q_anc wy0 py0 q_max : N) : option N :=
  if q_max <? q_anc then Some q_anc
  else if checkAbstract nxTpl true true (wy0 + (q_max - q_anc)) (py0 + (q_max - q_anc)) then
    Some q_anc
  else
    let jc0 := (- (2 * k_hi_c + w_hi_c + Z.of_N (2 * extra_B_parent)))%Z in
    let min_ju := dominantJuMin (nd_jb nxTpl) jc0 in
    let need := 2 * k_hi_u + w_hi_u + min_ju in
    let q_right := N.max q_anc ((need + ms - 1) / ms) in
    if q_right <=? q_max then
      let ju_r := (Z.of_N (q_right * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z in
      let nx_r := withJB nxTpl (addJBound (nd_jb nxTpl) ju_r jc0) in
      if checkAbstract nx_r true true (wy0 + (q_right - q_anc)) (py0 + (q_right - q_anc)) then
        if q_right <=? q_anc then Some q_anc
        else if checkAbstract nxTpl true true (wy0 + (q_right - 1 - q_anc)) (py0 + (q_right - 1 - q_anc)) then
          Some q_anc
        else Some q_right
      else None
    else None.

Definition runBeforeStop (q : N) (st : option N) : bool :=
  match st with
  | None => true
  | Some q_stop => q <? q_stop
  end.

Definition canonNode (nd : SymWaveNode) : SymWaveNode :=
  if negb (nd_has_i1_front nd) then
    mkWaveNode (nd_s nd) (nd_db_shift nd) (nd_has_i1_front nd)
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      (nd_w_lo_u nd) (nd_w_lo_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
      (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      0 0%Z 0 0 0%Z
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd)
  else
    mkWaveNode (nd_s nd) (nd_db_shift nd) (nd_has_i1_front nd)
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z (nd_w_hi_u nd) (nd_w_hi_c nd)
      (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd).

Fixpoint runRange (d : nat) (body : N -> MemoTree -> bool * MemoTree)
    (cur rem : N) (memo : MemoTree) : bool * MemoTree :=
  if rem =? 0 then (true, memo)
  else match d with
  | O =>
    if rem =? 1 then body cur memo else (false, memo)
  | S d' =>
    let h := N.div2 rem in
    let '(ok1, m1) := runRange d' body cur h memo in
    if negb ok1 then (false, m1)
    else runRange d' body (cur + h) (rem - h) m1
  end.

Definition stepQBody (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms ms_next : N) (st1 st2 st3 st4 : option N)
    (q : N) (memo : MemoTree) : bool * MemoTree :=
  let b1 := runBeforeStop q st1 in
  let b2 := runBeforeStop q st2 in
  let b3 := runBeforeStop q st3 in
  let b4 := runBeforeStop q st4 in
  if negb (b1 || b2 || b3 || b4) then (true, memo)
  else if holdsWithJBounds 64 (-2)%Z (Z.of_N ((q + 1) * ms) - Z.of_N (nd_w_lo_u nd))%Z
            (- Z.of_N (2 * nd_extra_B nd) - nd_w_lo_c nd)%Z 1 (nd_jb nd)
            (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) then
    (true, memo)
  else
    match t0PowNorm wordFuel q (nd_Y nd) with
    | None => (false, memo)
    | Some yp =>
      let ju := (Z.of_N (q * ms) - Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd))%Z in
      let jc := (- (2 * nd_k_hi_c nd + nd_w_hi_c nd + Z.of_N (2 * nd_extra_B nd)))%Z in
      let jb' := addJBound (nd_jb nd) ju jc in
      let '(ok1, m1) :=
        if b1 then
          let nx1 := mkWaveNode
            (nd_s nd + 1) (nd_db_shift nd + 1) false
            (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
            0 0%Z ms_next (-1)%Z
            (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
            (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
            jb' yp (nd_wRQ nd) (nd_pRQ nd) in
          stepFn nx1 memo
        else (true, memo) in
      if negb ok1 then (false, m1)
      else
        let '(ok2, m2) :=
          if b2 then
            match t0PowNorm wordFuel 1 yp with
            | None => (false, m1)
            | Some yp1 =>
              let nx2 := mkWaveNode
                (nd_s nd + 1) (nd_db_shift nd + 1) false
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
                0 0%Z 0 1%Z
                (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
                (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
                jb' yp1 (nd_wRQ nd) (nd_pRQ nd) in
              stepFn nx2 m1
            end
          else (true, m1) in
        if negb ok2 then (false, m2)
        else
          let '(ok3, m3) :=
            if b3 then
              let nx3 := mkWaveNode
                (nd_s nd + 1) (nd_db_shift nd + 1) false
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
                0 0%Z ms_next (-1)%Z
                (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd + pow2N (nd_db_shift nd + 2))
                (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
                jb' yp (nd_wRQ nd) (nd_pRQ nd) in
              stepFn nx3 m2
            else (true, m2) in
          if negb ok3 then (false, m3)
          else
            if b4 then
              let sh1 := pow2N (nd_s nd + 1) in
              let nx4 := mkWaveNode
                (nd_s nd + 1) (nd_db_shift nd + 1) true
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
                0 0%Z ms_next (-1)%Z
                (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
                ((q + 1) * ms) (- Z.of_N (2 * nd_extra_B nd + 2))%Z
                sh1 (64 * (q + 1)) (- Z.of_N (sh1 * (nd_extra_B nd + 1)))%Z
                jb' yp (nd_wRQ nd) (nd_pRQ nd) in
              stepFn nx4 m3
            else (true, m3)
    end.

Definition stepQABody (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms_next : N) (qa : N) (memo : MemoTree) : bool * MemoTree :=
  match t0PowNorm wordFuel qa (nd_Y nd) with
  | None => (false, memo)
  | Some ya =>
    let nx := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms_next (-1)%Z
      (nd_extra_B nd + 1) (nd_scaled_db_u nd + pow2N (nd_db_shift nd) * ms_next) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) ya (nd_wRQ nd) (nd_pRQ nd) in
    stepFn nx memo
  end.

Definition stepQSBody (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms sh4 ct : N) (tyc : list BecTok1) (next_jb : JBounds)
    (qs : N) (memo : MemoTree) : bool * MemoTree :=
  if holdsWithJBounds 64 (-2)%Z (Z.of_N (2 * (qs + 3) * ms))
       (- Z.of_N (2 * (nd_extra_B nd + 3)))%Z 1 next_jb
       (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) then
    (true, memo)
  else if (nd_s nd =? nd_db_shift nd) &&
          holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
            (Z.of_N (128 * ct + 256 * (qs + 3)) - Z.of_N (128 * nd_wRQ nd))%Z
            (- Z.of_N (sh4 * (nd_extra_B nd + 3)))%Z
            (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) then
    (true, memo)
  else
    match t0PowNorm wordFuel qs tyc with
    | None => (false, memo)
    | Some yq =>
      let ju := (Z.of_N (2 * (qs + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z in
      let jc := (- (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3))))%Z in
      let jb' := addJBound next_jb ju jc in
      let nx := mkWaveNode
        (nd_s nd) (nd_db_shift nd) false
        (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
        0 0%Z ms (-1)%Z
        (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
        (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
        jb' yq (nd_wRQ nd) (nd_pRQ nd) in
      stepFn nx memo
    end.

Definition qsStopOpt (nd : SymWaveNode) (ms qs_lo qs_hi : N)
    (tyc : list BecTok1) (next_jb : JBounds) : option N :=
  match findL0Anchor 7%nat tyc qs_lo qs_hi with
  | None => None
  | Some (qs0, wys0, pys0) =>
    let nxTpl := mkWaveNode
      (nd_s nd) (nd_db_shift nd) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms (-1)%Z
      (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      next_jb (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    if checkAbstract nxTpl true true (wys0 + (qs_hi - qs0)) (pys0 + (qs_hi - qs0)) then
      Some qs0
    else
      let jc_qs := (- (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3))))%Z in
      let min_ju := dominantJuMin next_jb jc_qs in
      let need_qs := nd_k_hi_u nd + (min_ju + 1) / 2 in
      let req_qsr2 := (need_qs + ms - 1) / ms in
      let qs_r := N.max qs0 (req_qsr2 - 2) in
      if qs_r <=? qs_hi then
        let ju_r := (Z.of_N (2 * (qs_r + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z in
        let nx_r := withJB nxTpl (addJBound next_jb ju_r jc_qs) in
        if checkAbstract nx_r true true (wys0 + (qs_r - qs0)) (pys0 + (qs_r - qs0)) then
          if qs_r <=? qs0 then Some qs0
          else if checkAbstract nxTpl true true (wys0 + (qs_r - 1 - qs0)) (pys0 + (qs_r - 1 - qs0)) then
            Some qs0
          else Some qs_r
        else None
      else None
  end.

Definition stepCTInner (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms qs_hi sh2 sh4 ct : N) (tyc : list BecTok1)
    (memo : MemoTree) : bool * MemoTree :=
  let raw_ju := (Z.of_N (128 * nd_wRQ nd) - Z.of_N (7 * nd_k_hi_u nd + 128 * (ct + 1)))%Z in
  let raw_jc := (3 - 7 * nd_k_hi_c nd)%Z in
  let '(ct_ju, ct_jc) :=
    if (nd_s nd =? nd_db_shift nd) && (0 <=? raw_ju)%Z then
      let rju := toNatClip raw_ju in
      (Z.of_N (rju / sh2), fdivNat (raw_jc + Z.of_N (rju mod sh2))%Z sh2)
    else (0%Z, 0%Z) in
  let next_jb := addJBound (nd_jb nd) ct_ju ct_jc in
  let qslo0 := floorMinU1
    (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb))
    (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb)%Z
    (2 * ms) in
  let qs_lo := qslo0 - 2 in
  if qs_hi <? qs_lo then (true, memo)
  else if 4096 <? qs_hi - qs_lo then (false, memo)
  else
    let qs_stop_opt := qsStopOpt nd ms qs_lo qs_hi tyc next_jb in
    let cntQS :=
      match qs_stop_opt with
      | None => qs_hi - qs_lo + 1
      | Some qs_stop =>
        if qs_stop <=? qs_lo then 0
        else N.min (qs_stop - qs_lo) (qs_hi - qs_lo + 1)
      end in
    runRange 13%nat (stepQSBody stepFn nd ms sh4 ct tyc next_jb) qs_lo cntQS memo.

Definition stepCTBody (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms qs_hi : N) (ct : N) (memo : MemoTree) : bool * MemoTree :=
  let sh2 := pow2N (nd_s nd + 1) in
  let sh4 := pow2N (nd_s nd + 2) in
  if (nd_s nd =? nd_db_shift nd) &&
     holdsLinearAllUK 64 (7 - Z.of_N (2 * nd_wj_k nd))%Z
       (Z.of_N (128 * ct + 2 * nd_wj_hi_u nd) - Z.of_N (128 * nd_wRQ nd))%Z
       (2 * nd_wj_hi_c nd)%Z
       (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) then
    (true, memo)
  else if (nd_s nd =? nd_db_shift nd) &&
          holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
            (Z.of_N (128 * ct + sh2 * nd_kj_hi_u nd) - Z.of_N (128 * nd_wRQ nd))%Z
            (Z.of_N sh2 * nd_kj_hi_c nd)%Z
            (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) then
    (true, memo)
  else
    match t0PowNorm wordFuel ct (nd_Y nd) with
    | None => (false, memo)
    | Some yc =>
      match t1Norm wordFuel yc with
      | None => (false, memo)
      | Some tyc => stepCTInner stepFn nd ms qs_hi sh2 sh4 ct tyc memo
      end
    end.

Definition findQStops (nd : SymWaveNode) (ms ms_next q_min q_max : N)
    : option N * option N * option N * option N :=
  match findL0Anchor 7%nat (nd_Y nd) q_min q_max with
  | None => (None, None, None, None)
  | Some (q_anc, wy0, py0) =>
    let nx1 := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd + 1) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms_next (-1)%Z
      (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    let nx2 := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd + 1) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z 0 1%Z
      (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    let nx3 := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd + 1) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms_next (-1)%Z
      (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd + pow2N (nd_db_shift nd + 2))
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    let nx4 := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd + 1) true
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms_next (-1)%Z
      (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    (findChildQStop nx1 ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd) (nd_extra_B nd) q_anc wy0 py0 q_max,
     findChildQStop nx2 ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd) (nd_extra_B nd) q_anc (wy0 + 1) (py0 + 1) q_max,
     findChildQStop nx3 ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd) (nd_extra_B nd) q_anc wy0 py0 q_max,
     findChildQStop nx4 ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd) (nd_extra_B nd) q_anc wy0 py0 q_max)
  end.

Definition verifyWaveI0 (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms ms_next two_d_hi_u : N) (memo : MemoTree) : bool * MemoTree :=
  let q_min := floorMinU1
    (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u (nd_jb nd) + nd_w_lo_u nd))
    (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd)) + jb_inf_c (nd_jb nd) + nd_w_lo_c nd)%Z ms in
  let q_max := floorMaxU1
    (Z.of_N (2 * nd_k_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd + nd_w_hi_u nd))
    (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + nd_scaled_db_c nd)) + nd_w_hi_c nd)%Z ms in
  if q_max <? q_min then (true, memoInsert memo nd)
  else if 4096 <? q_max - q_min then (false, memo)
  else
    let '(st1, st2, st3, st4) := findQStops nd ms ms_next q_min q_max in
    let cnt := q_max - q_min + 1 in
    let '(ok, memo') := runRange 13%nat (stepQBody stepFn nd ms ms_next st1 st2 st3 st4) q_min cnt memo in
    if ok then (true, memoInsert memo' nd) else (false, memo').

Definition computeCntA (nd : SymWaveNode) (ms_next qa_lo qa_hi : N) : N :=
  if qa_hi <? qa_lo then 0
  else match findL0Anchor 7%nat (nd_Y nd) qa_lo qa_hi with
  | None => qa_hi - qa_lo + 1
  | Some (qa0, wya0, pya0) =>
    let nx_hi := mkWaveNode
      (nd_s nd + 1) (nd_db_shift nd) false
      (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
      0 0%Z ms_next (-1)%Z
      (nd_extra_B nd + 1) (nd_scaled_db_u nd + pow2N (nd_db_shift nd) * ms_next) (nd_scaled_db_c nd)
      (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
      (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd) in
    if checkAbstract nx_hi true true (wya0 + (qa_hi - qa0)) (pya0 + (qa_hi - qa0)) then
      qa0 - qa_lo
    else qa_hi - qa_lo + 1
  end.

Definition verifyWaveI1 (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (nd : SymWaveNode) (ms ms_next two_d_hi_u : N) (memo : MemoTree) : bool * MemoTree :=
  if negb (holdsLinearAllUK 64 (-1)%Z (Z.of_N (2 * ms)) (- Z.of_N (nd_extra_B nd + 3))%Z
             (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) then
    (false, memo)
  else
    let qa_lo := floorMinU1
      (Z.of_N (nd_k_lo_u nd) - Z.of_N (ms + ms_next))%Z
      (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 4))%Z ms_next in
    let qa_hi := floorMaxU1
      (Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd))
      (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd)) + nd_w_hi_c nd)%Z
      (2 * ms_next) in
    if (qa_lo <=? qa_hi) && (4096 <? qa_hi - qa_lo) then (false, memo)
    else
      let cntA := computeCntA nd ms_next qa_lo qa_hi in
      let '(okA, memoA) := runRange 13%nat (stepQABody stepFn nd ms_next) qa_lo cntA memo in
      if negb okA then (false, memoA)
      else
        let sh := pow2N (nd_db_shift nd) in
        let psi_p_hi_u := Z.of_N ((two_d_hi_u + 2 * nd_scaled_db_u nd) / sh + 1 + nd_w_hi_u nd) in
        let psi_p_hi_c := (nd_w_hi_c nd + Z.of_N ((2 * nd_scaled_db_c nd) / sh + 1))%Z in
        let ctot_max := floorMaxU1 psi_p_hi_u psi_p_hi_c ms in
        if 4096 <? ctot_max then (false, memoA)
        else
          let d_hi_u := (two_d_hi_u + 1) / 2 in
          let qs_hi_1 := (floorMaxU1
            (Z.of_N (nd_k_hi_u nd + d_hi_u + nd_scaled_db_u nd))
            (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd))%Z ms) - 2 in
          let qs_hi_2 := (floorMaxU1
            (Z.of_N (nd_kj_hi_u nd))
            (nd_kj_hi_c nd + Z.of_N (2 * (nd_extra_B nd + 3)))%Z (2 * ms)) - 2 in
          let qs_hi := N.min qs_hi_1 qs_hi_2 in
          let cntC := ctot_max + 1 in
          let '(okC, memoC) := runRange 13%nat (stepCTBody stepFn nd ms qs_hi) 0 cntC memoA in
          if okC then (true, memoInsert memoC nd) else (false, memoC).

Fixpoint verifyWaveNode (fuel : nat) (nd0 : SymWaveNode) (memo : MemoTree) : bool * MemoTree :=
  match fuel with
  | O => (false, memo)
  | S fuel' =>
    let nd := canonNode nd0 in
    if negb (nd_k_hi_c nd <=? 0)%Z || (nd_extra_B nd =? 0) then
      (false, memo)
    else if nd_has_i1_front nd && (nd_s nd =? nd_db_shift nd) &&
            negb (nd_wj_k nd =? pow2N (nd_s nd)) then
      (false, memo)
    else
      let yL0 := noK1 (nd_Y nd) in
      let yHI := hasI (nd_Y nd) in
      let wy := if yL0 then evalPhi 0 (nd_Y nd) else 0 in
      let py := if yL0 then evalPhi 22 (nd_Y nd) else 0 in
      if yL0 && checkAbstract nd true yHI wy py then (true, memo)
      else if memoContains memo nd then (true, memo)
      else if isEmptyWord (nd_Y nd) || negb (noTrailZero (nd_Y nd)) then (false, memo)
      else if (6 <=? nd_s nd) || (negb (nd_has_i1_front nd) && (5 <=? nd_s nd)) then (false, memo)
      else
        let ms := msOf (nd_s nd) in
        let ms_next := msOf (nd_s nd + 1) in
        let two_d_hi_u := twoDInitHiU nd in
        if negb (nd_has_i1_front nd) then
          verifyWaveI0 (verifyWaveNode fuel') nd ms ms_next two_d_hi_u memo
        else
          verifyWaveI1 (verifyWaveNode fuel') nd ms ms_next two_d_hi_u memo
  end.

Definition checkRoot (r : SymWaveNode) (memo : MemoTree) : bool * MemoTree :=
  verifyWaveNode 13%nat r memo.

Fixpoint checkOneRQSlabs (rem : nat) (rq : list BecTok1) (wrq prq global_klo_u : N)
    (global_klo_c : Z) (memo : MemoTree) : bool * MemoTree :=
  match rem with
  | O => (true, memo)
  | S rem' =>
    let slab := N.of_nat (8 - S rem')%nat in
    let s_lo_u0 := 64 + 8 * slab in
    let s_lo_c0 := if slab =? 0 then (-1)%Z else 1%Z in
    let s_hi_u := 64 + 8 * (slab + 1) in
    let s_hi_c := if slab =? 7 then (-4)%Z else 0%Z in
    if s_hi_u <? global_klo_u then
      checkOneRQSlabs rem' rq wrq prq global_klo_u global_klo_c memo
    else
      let '(s_lo_u, s_lo_c) :=
        if s_lo_u0 <? global_klo_u then (global_klo_u, global_klo_c)
        else if s_lo_u0 =? global_klo_u then (s_lo_u0, Z.max s_lo_c0 global_klo_c)
        else (s_lo_u0, s_lo_c0) in
      if (s_lo_u =? s_hi_u) && negb (s_lo_c <=? s_hi_c)%Z then
        checkOneRQSlabs rem' rq wrq prq global_klo_u global_klo_c memo
      else
        let y1 := norm1 (Tok1 :: rq) in
        let nb := mkWaveNode
          0 0 false
          s_lo_u s_lo_c s_hi_u s_hi_c
          (s_lo_u - 64) (s_lo_c + 3)%Z (s_hi_u - 64) (s_hi_c + 3)%Z
          1 0 0
          (2 * s_hi_u) (2 * s_hi_c)%Z
          0 0 0%Z
          emptyJB y1 wrq prq in
        let '(ok, memo') := checkRoot nb memo in
        if negb ok then (false, memo')
        else checkOneRQSlabs rem' rq wrq prq global_klo_u global_klo_c memo'
  end.

Definition checkOneRQ (rq : list BecTok1) (memo : MemoTree) : bool * MemoTree :=
  let wrq := evalPhi 0 rq in
  let prq := evalPhi 22 rq in
  let psirq := evalPhi 2 rq in
  let '(okA, memoA) :=
    if (44 * 64 * psirq <=? 348 * 128) && (64 * prq <=? 52 * 128) then
      match t1Norm wordFuel rq with
      | None => (false, memo)
      | Some y1 =>
        let na := mkWaveNode
          0 0 false
          128 (-3)%Z 128 (-2)%Z
          0 0%Z 0 1%Z
          1 0 0
          256 (-4)%Z
          0 0 0%Z
          emptyJB y1 wrq prq in
        checkRoot na memo
      end
    else (true, memo) in
  if negb okA then (false, memoA)
  else
    let q_psi_lo := (44 * 64 * psirq) / 348 in
    let q_phi_lo := (64 * prq) / 52 in
    let m_lo := N.max q_psi_lo q_phi_lo in
    let global_klo_u := N.max 64 m_lo in
    let global_klo_c := if 64 <=? m_lo then 1%Z else (-1)%Z in
    checkOneRQSlabs 8%nat rq wrq prq global_klo_u global_klo_c memoA.

Definition checkAllRQ : bool :=
  List.forallb (fun rq => fst (checkOneRQ rq MLeaf)) allRQ.

(* ========================================================================== *)
(* Layer 3b Soundness Part 1: Bounds, Linear Rays, MemoTree & Anchor Walk     *)
(* ========================================================================== *)

Local Lemma t1Norm_sound {fuel : nat} {xs ys : list BecTok1}
    (h : t1Norm fuel xs = Some ys) : RelT M1 xs ys.
Proof.
  unfold t1Norm in h.
  destruct (execT fuel 1%nat 0 xs) as [u |] eqn:Hex; [| discriminate].
  injection h as <-. exact (rt_norm_out (execT_t1_sound Hex)).
Qed.

Local Lemma t1Norm_noTrailZero {fuel : nat} {xs ys : list BecTok1}
    (h : t1Norm fuel xs = Some ys) : noTrailZero ys = true.
Proof.
  unfold t1Norm in h.
  destruct (execT fuel 1%nat 0 xs) as [u |]; [injection h as <-; exact (noTrailZero_norm1 u) | discriminate].
Qed.

Local Lemma t0PowNorm_noTrailZero {fuel : nat} {n : N} {xs ys : list BecTok1}
    (htz : noTrailZero xs = true) (h : t0PowNorm fuel n xs = Some ys) :
  noTrailZero ys = true.
Proof.
  unfold t0PowNorm in h.
  destruct (n =? 0); [injection h as <-; exact htz |].
  destruct (execT0 fuel n xs) as [u |]; [injection h as <-; exact (noTrailZero_norm1 u) | discriminate].
Qed.

#[local] Arguments wordFuel : simpl never.
#[local] Arguments execT : simpl never.
#[local] Arguments execT0 : simpl never.
#[local] Arguments t0PowNorm : simpl never.
#[local] Arguments t1Norm : simpl never.

Local Lemma div_ge_of_mul_le (x d k : N) (hd : 0 < d) (h : d * k <= x) :
  k <= x / d.
Proof.
  destruct (div_mod_spec x d hd) as [q [r [hq [_ [hqr hr]]]]].
  rewrite hq. nia.
Qed.

Local Lemma ceil_div_mul_ge (a d : N) (hd : 0 < d) :
  a <= d * ((a + d - 1) / d).
Proof.
  destruct (div_mod_spec (a + d - 1) d hd) as [q [r [hq [_ [hqr hr]]]]].
  rewrite hq. nia.
Qed.

Local Lemma toNatClip_spec (x : Z) :
  ((0 <= x)%Z -> Z.of_N (toNatClip x) = x) /\
  ((x <= 0)%Z -> toNatClip x = 0) /\
  (x <= Z.of_N (toNatClip x))%Z.
Proof.
  unfold toNatClip.
  destruct x as [| p | p]; repeat split; intros; try reflexivity; lia.
Qed.

Local Lemma toNatClip_le_of_le (x : Z) (b : N) (h : (x <= Z.of_N b)%Z) :
  toNatClip x <= b.
Proof.
  destruct (toNatClip_spec x) as [hpos [hneg _]].
  destruct (Z_le_gt_dec x 0) as [hle | hgt]; [rewrite (hneg hle); lia |].
  pose proof (hpos ltac:(lia)). lia.
Qed.

Local Lemma toNatClip_mono {x y : Z} (h : (x <= y)%Z) :
  toNatClip x <= toNatClip y.
Proof.
  apply toNatClip_le_of_le. pose proof (proj2 (proj2 (toNatClip_spec y))). lia.
Qed.

Local Lemma fdivNat_le (x : Z) (d : N) (hd : 0 < d) :
  (Z.of_N d * fdivNat x d <= x)%Z.
Proof.
  unfold fdivNat.
  assert (hd0 : (d =? 0) = false) by (apply N.eqb_neq; lia).
  rewrite hd0.
  pose proof (Z.div_mod x (Z.of_N d) ltac:(lia)).
  pose proof (Z.mod_pos_bound x (Z.of_N d) ltac:(lia)).
  lia.
Qed.

Local Lemma cdivNat_upper (x : Z) (d : N) (hd : 0 < d) :
  (x <= Z.of_N d * Z.of_N (toNatClip (cdivNat x d + 1)%Z))%Z.
Proof.
  unfold cdivNat.
  assert (hd0 : (d =? 0) = false) by (apply N.eqb_neq; lia).
  rewrite hd0.
  destruct ((0 <=? x)%Z) eqn:Hx.
  - apply Z.leb_le in Hx.
    pose proof (Z.div_pos x (Z.of_N d) Hx ltac:(lia)).
    pose proof (Z.div_mod x (Z.of_N d) ltac:(lia)).
    pose proof (Z.mod_pos_bound x (Z.of_N d) ltac:(lia)).
    rewrite (proj1 (toNatClip_spec (x / Z.of_N d + 1)%Z) ltac:(lia)).
    lia.
  - apply Z.leb_gt in Hx. nia.
Qed.

Local Lemma pow2N_eq (n : N) : pow2N n = 2 ^ n.
Proof.
  unfold pow2N. rewrite N.shiftl_mul_pow2. lia.
Qed.

Local Lemma msOf_mul_pow2 {s : N} (hs : s <= 6) : msOf s * (2 ^ s) = 64.
Proof.
  assert (s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]] by lia; reflexivity.
Qed.

Local Lemma msOf_pos {s : N} (hs : s <= 6) : 0 < msOf s.
Proof.
  assert (s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]] by lia; cbn; lia.
Qed.

Local Lemma msOf_succ {s : N} (hs : s <= 5) : 2 * msOf (s + 1) = msOf s.
Proof.
  assert (s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5)
    as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia; reflexivity.
Qed.

Definition JBoundsValid (jb : JBounds) (u_val j_val : N) : Prop :=
  (u_val = 1 -> jb_at1 jb <= 2 * j_val) /\
  (u_val = 2 -> jb_at2 jb <= 2 * j_val) /\
  (u_val = 3 -> jb_at3 jb <= 2 * j_val) /\
  (u_val = 4 -> jb_at4 jb <= 2 * j_val) /\
  (Z.of_N (jb_u5_u jb) * Z.of_N u_val + jb_u5_c jb <= Z.of_N (2 * j_val))%Z /\
  (Z.of_N (jb_inf_u jb) * Z.of_N u_val + jb_inf_c jb <= Z.of_N (2 * j_val))%Z.

Local Lemma JBoundsValid_empty (u_val j_val : N) : JBoundsValid emptyJB u_val j_val.
Proof.
  unfold JBoundsValid, emptyJB; cbn; repeat split; intros; lia.
Qed.

Local Lemma JBoundsValid_mono_J {jb : JBounds} {u_val j1 j2 : N}
    (h : JBoundsValid jb u_val j1) (hle : j1 <= j2) : JBoundsValid jb u_val j2.
Proof.
  destruct h as [h1 [h2 [h3 [h4 [h5 hi]]]]].
  repeat split; [intros hu; pose proof (h1 hu); lia | intros hu; pose proof (h2 hu); lia
    | intros hu; pose proof (h3 hu); lia | intros hu; pose proof (h4 hu); lia | lia | lia].
Qed.

Local Lemma addJBound_sound {jb : JBounds} {u_val j_val : N} {ju jc : Z}
    (hjb : JBoundsValid jb u_val j_val)
    (hbnd : (ju * Z.of_N u_val + jc <= Z.of_N (2 * j_val))%Z) :
  JBoundsValid (addJBound jb ju jc) u_val j_val.
Proof.
  destruct hjb as [h1 [h2 [h3 [h4 [h5 hi]]]]].
  unfold addJBound.
  assert (ha1 : u_val = 1 -> N.max (jb_at1 jb) (toNatClip (ju + jc)%Z) <= 2 * j_val).
  { intros ->. apply N.max_lub; [exact (h1 eq_refl) | apply toNatClip_le_of_le; lia]. }
  assert (ha2 : u_val = 2 -> N.max (jb_at2 jb) (toNatClip (2 * ju + jc)%Z) <= 2 * j_val).
  { intros ->. apply N.max_lub; [exact (h2 eq_refl) | apply toNatClip_le_of_le; lia]. }
  assert (ha3 : u_val = 3 -> N.max (jb_at3 jb) (toNatClip (3 * ju + jc)%Z) <= 2 * j_val).
  { intros ->. apply N.max_lub; [exact (h3 eq_refl) | apply toNatClip_le_of_le; lia]. }
  assert (ha4 : u_val = 4 -> N.max (jb_at4 jb) (toNatClip (4 * ju + jc)%Z) <= 2 * j_val).
  { intros ->. apply N.max_lub; [exact (h4 eq_refl) | apply toNatClip_le_of_le; lia]. }
  destruct (((0 <? ju)%Z || ((ju =? 0)%Z && (0 <? jc)%Z))) eqn:Hcnd.
  - assert (hju0 : (0 <= ju)%Z).
    { apply Bool.orb_true_iff in Hcnd as [hg | hz]; [apply Z.ltb_lt in hg; lia |].
      apply Bool.andb_true_iff in hz as [hz _]; apply Z.eqb_eq in hz; lia. }
    assert (hjun : Z.of_N (Z.to_N ju) = ju) by exact (proj1 (toNatClip_spec ju) hju0).
    assert (hnew : (Z.of_N (Z.to_N ju) * Z.of_N u_val + jc <= Z.of_N (2 * j_val))%Z)
      by (rewrite hjun; exact hbnd).
    cbn [jb_at1 jb_at2 jb_at3 jb_at4 jb_u5_u jb_u5_c jb_inf_u jb_inf_c].
    repeat split; try assumption.
    + destruct (((Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb <? Z.of_N (5 * Z.to_N ju) + jc)%Z ||
        ((Z.of_N (5 * Z.to_N ju) + jc =? Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb)%Z &&
         (jb_u5_u jb <? Z.to_N ju)))); [exact hnew | exact h5].
    + destruct ((jb_inf_u jb <? Z.to_N ju) || ((Z.to_N ju =? jb_inf_u jb) && (jb_inf_c jb <? jc)%Z));
        [exact hnew | exact hi].
  - exact (conj ha1 (conj ha2 (conj ha3 (conj ha4 (conj h5 hi))))).
Qed.

Definition JBoundsLe (jb1 jb2 : JBounds) : Prop :=
  jb_at1 jb1 <= jb_at1 jb2 /\ jb_at2 jb1 <= jb_at2 jb2 /\
  jb_at3 jb1 <= jb_at3 jb2 /\ jb_at4 jb1 <= jb_at4 jb2 /\
  jb_u5_u jb1 <= jb_u5_u jb2 /\ (jb_u5_c jb1 <= jb_u5_c jb2)%Z /\
  jb_inf_u jb1 <= jb_inf_u jb2 /\ (jb_inf_c jb1 <= jb_inf_c jb2)%Z.

Local Lemma JBoundsLe_refl (jb : JBounds) : JBoundsLe jb jb.
Proof. unfold JBoundsLe; repeat split; lia. Qed.

Local Lemma holdsAtU_sound {K0 jCoeff jv k_lo_u k_hi_u u_val k_val j_val : N}
    {alpha beta0 gamma0 k_lo_c k_hi_c : Z}
    (hK0 : K0 <= k_val)
    (hklo : (Z.of_N (k_lo_u * u_val) + k_lo_c <= Z.of_N k_val)%Z)
    (hkhi : (Z.of_N k_val <= Z.of_N (k_hi_u * u_val) + k_hi_c)%Z)
    (hjv : jv <= 2 * j_val)
    (hok : holdsAtU K0 alpha beta0 gamma0 jCoeff jv k_lo_u k_lo_c k_hi_u k_hi_c u_val = true) :
  (alpha * Z.of_N k_val + beta0 * Z.of_N u_val + gamma0 - Z.of_N (jCoeff * (2 * j_val)) <= 0)%Z.
Proof.
  unfold holdsAtU in hok.
  set (klo := Z.max (Z.of_N K0) (Z.of_N (k_lo_u * u_val) + k_lo_c)%Z) in *.
  set (khi := (Z.of_N (k_hi_u * u_val) + k_hi_c)%Z) in *.
  assert (hklo_v : (klo <= Z.of_N k_val)%Z) by (unfold klo; lia).
  assert (hkhi_v : (Z.of_N k_val <= khi)%Z) by (unfold khi; lia).
  assert (hle : (klo <=? khi)%Z = true) by (apply Z.leb_le; lia).
  rewrite hle in hok.
  apply Bool.andb_true_iff in hok as [hb1 hb2].
  apply Z.leb_le in hb1; apply Z.leb_le in hb2.
  assert (hjmul : (Z.of_N (jCoeff * jv) <= Z.of_N (jCoeff * (2 * j_val)))%Z)
    by (clear - hjv; nia).
  destruct (Z_le_gt_dec 0 alpha) as [ha | ha].
  - assert (hak : (alpha * Z.of_N k_val <= alpha * khi)%Z) by (clear - ha hkhi_v; nia).
    lia.
  - assert (hak : (alpha * Z.of_N k_val <= alpha * klo)%Z) by (clear - ha hklo_v; nia).
    lia.
Qed.

Local Lemma ray5_sound {u_val : N} {A B : Z}
    (hU5 : 5 <= u_val) (hA : (A <= 0)%Z) (h5 : (5 * A + B <= 0)%Z) :
  (A * Z.of_N u_val + B <= 0)%Z.
Proof.
  assert (hmul : (A * Z.of_N u_val <= 5 * A)%Z) by nia.
  lia.
Qed.

Local Lemma holdsLinearAllUK_sound {K0 k_lo_u k_hi_u u_val k_val : N}
    {alpha beta gamma k_lo_c k_hi_c : Z}
    (hU : 1 <= u_val) (hK0 : K0 <= k_val)
    (hklo : (Z.of_N (k_lo_u * u_val) + k_lo_c <= Z.of_N k_val)%Z)
    (hkhi : (Z.of_N k_val <= Z.of_N (k_hi_u * u_val) + k_hi_c)%Z)
    (hok : holdsLinearAllUK K0 alpha beta gamma k_lo_u k_lo_c k_hi_u k_hi_c = true) :
  (alpha * Z.of_N k_val + beta * Z.of_N u_val + gamma <= 0)%Z.
Proof.
  unfold holdsLinearAllUK in hok.
  apply Bool.andb_true_iff in hok as [hok hray].
  cbn zeta in hray.
  apply Bool.andb_true_iff in hray as [hc1 hc5].
  apply Bool.andb_true_iff in hok as [hok hu4].
  apply Bool.andb_true_iff in hok as [hok hu3].
  apply Bool.andb_true_iff in hok as [hu1 hu2].
  assert (u_val = 1 \/ u_val = 2 \/ u_val = 3 \/ u_val = 4 \/ 5 <= u_val)
    as [-> | [-> | [-> | [-> | hU5]]]] by lia.
  - pose proof (@holdsAtU_sound K0 0 0 k_lo_u k_hi_u 1 k_val 0 alpha beta gamma k_lo_c k_hi_c hK0 hklo hkhi ltac:(lia) hu1); lia.
  - pose proof (@holdsAtU_sound K0 0 0 k_lo_u k_hi_u 2 k_val 0 alpha beta gamma k_lo_c k_hi_c hK0 hklo hkhi ltac:(lia) hu2); lia.
  - pose proof (@holdsAtU_sound K0 0 0 k_lo_u k_hi_u 3 k_val 0 alpha beta gamma k_lo_c k_hi_c hK0 hklo hkhi ltac:(lia) hu3); lia.
  - pose proof (@holdsAtU_sound K0 0 0 k_lo_u k_hi_u 4 k_val 0 alpha beta gamma k_lo_c k_hi_c hK0 hklo hkhi ltac:(lia) hu4); lia.
  - apply Z.leb_le in hc1; apply Z.leb_le in hc5.
    rewrite !N2Z.inj_mul in hklo, hkhi.
    destruct ((0 <=? alpha)%Z) eqn:Ha.
    + apply Z.leb_le in Ha.
      pose proof (ray5_sound hU5 hc1 hc5) as hr.
      assert (hak : (alpha * Z.of_N k_val <= alpha * (Z.of_N k_hi_u * Z.of_N u_val + k_hi_c))%Z)
        by (clear - Ha hkhi; nia).
      assert (hid : (alpha * (Z.of_N k_hi_u * Z.of_N u_val + k_hi_c) + beta * Z.of_N u_val + gamma =
                     (Z.of_N k_hi_u * alpha + beta) * Z.of_N u_val + (alpha * k_hi_c + gamma))%Z) by ring.
      lia.
    + apply Z.leb_gt in Ha.
      pose proof (ray5_sound hU5 hc1 hc5) as hr.
      assert (hak : (alpha * Z.of_N k_val <= alpha * (Z.of_N k_lo_u * Z.of_N u_val + k_lo_c))%Z)
        by (clear - Ha hklo; nia).
      assert (hid : (alpha * (Z.of_N k_lo_u * Z.of_N u_val + k_lo_c) + beta * Z.of_N u_val + gamma =
                     (Z.of_N k_lo_u * alpha + beta) * Z.of_N u_val + (alpha * k_lo_c + gamma))%Z) by ring.
      lia.
Qed.

Local Lemma holdsWithJBounds_ray_aux {jCoeff k_lo_u k_hi_u u_val k_val j_val ju_u : N}
    {alpha beta0 gamma0 k_lo_c k_hi_c jc : Z}
    (hU5 : 5 <= u_val)
    (hklo : (Z.of_N (k_lo_u * u_val) + k_lo_c <= Z.of_N k_val)%Z)
    (hkhi : (Z.of_N k_val <= Z.of_N (k_hi_u * u_val) + k_hi_c)%Z)
    (hj : (Z.of_N ju_u * Z.of_N u_val + jc <= Z.of_N (2 * j_val))%Z)
    (hr : (let ku := if (0 <=? alpha)%Z then k_hi_u else k_lo_u in
           let kc := if (0 <=? alpha)%Z then k_hi_c else k_lo_c in
           let c1 := (Z.of_N ku * alpha + beta0 - Z.of_N (jCoeff * ju_u))%Z in
           let cz := (alpha * kc + gamma0 - Z.of_N jCoeff * jc)%Z in
           (c1 <=? 0)%Z && (5 * c1 + cz <=? 0)%Z) = true) :
  (alpha * Z.of_N k_val + beta0 * Z.of_N u_val + gamma0 - Z.of_N (jCoeff * (2 * j_val)) <= 0)%Z.
Proof.
  cbn zeta in hr.
  apply Bool.andb_true_iff in hr as [hc1 hc5].
  apply Z.leb_le in hc1; apply Z.leb_le in hc5.
  rewrite !N2Z.inj_mul in *.
  assert (hjb : (Z.of_N jCoeff * (Z.of_N ju_u * Z.of_N u_val + jc) <=
                 Z.of_N jCoeff * (2 * Z.of_N j_val))%Z) by (clear - hj; nia).
  destruct ((0 <=? alpha)%Z) eqn:Ha.
  - apply Z.leb_le in Ha.
    pose proof (ray5_sound hU5 hc1 hc5) as hray.
    assert (hak : (alpha * Z.of_N k_val <= alpha * (Z.of_N k_hi_u * Z.of_N u_val + k_hi_c))%Z)
      by (clear - Ha hkhi; nia).
    assert (hid : (alpha * (Z.of_N k_hi_u * Z.of_N u_val + k_hi_c) + beta0 * Z.of_N u_val + gamma0 -
                   Z.of_N jCoeff * (Z.of_N ju_u * Z.of_N u_val + jc) =
                   (Z.of_N k_hi_u * alpha + beta0 - Z.of_N jCoeff * Z.of_N ju_u) * Z.of_N u_val +
                   (alpha * k_hi_c + gamma0 - Z.of_N jCoeff * jc))%Z) by ring.
    lia.
  - apply Z.leb_gt in Ha.
    pose proof (ray5_sound hU5 hc1 hc5) as hray.
    assert (hak : (alpha * Z.of_N k_val <= alpha * (Z.of_N k_lo_u * Z.of_N u_val + k_lo_c))%Z)
      by (clear - Ha hklo; nia).
    assert (hid : (alpha * (Z.of_N k_lo_u * Z.of_N u_val + k_lo_c) + beta0 * Z.of_N u_val + gamma0 -
                   Z.of_N jCoeff * (Z.of_N ju_u * Z.of_N u_val + jc) =
                   (Z.of_N k_lo_u * alpha + beta0 - Z.of_N jCoeff * Z.of_N ju_u) * Z.of_N u_val +
                   (alpha * k_lo_c + gamma0 - Z.of_N jCoeff * jc))%Z) by ring.
    lia.
Qed.

Local Lemma holdsWithJBounds_sound {K0 jCoeff k_lo_u k_hi_u u_val k_val j_val : N}
    {alpha beta0 gamma0 k_lo_c k_hi_c : Z} {jb : JBounds}
    (hjb : JBoundsValid jb u_val j_val)
    (hU : 1 <= u_val) (hK0 : K0 <= k_val)
    (hklo : (Z.of_N (k_lo_u * u_val) + k_lo_c <= Z.of_N k_val)%Z)
    (hkhi : (Z.of_N k_val <= Z.of_N (k_hi_u * u_val) + k_hi_c)%Z)
    (hok : holdsWithJBounds K0 alpha beta0 gamma0 jCoeff jb k_lo_u k_lo_c k_hi_u k_hi_c = true) :
  (alpha * Z.of_N k_val + beta0 * Z.of_N u_val + gamma0 - Z.of_N (jCoeff * (2 * j_val)) <= 0)%Z.
Proof.
  destruct hjb as [hj1 [hj2 [hj3 [hj4 [hj5 hji]]]]].
  unfold holdsWithJBounds in hok.
  apply Bool.andb_true_iff in hok as [hok hray].
  cbn zeta in hray.
  apply Bool.andb_true_iff in hok as [hok hu4].
  apply Bool.andb_true_iff in hok as [hok hu3].
  apply Bool.andb_true_iff in hok as [hu1 hu2].
  assert (u_val = 1 \/ u_val = 2 \/ u_val = 3 \/ u_val = 4 \/ 5 <= u_val)
    as [-> | [-> | [-> | [-> | hU5]]]] by lia.
  - exact (holdsAtU_sound hK0 hklo hkhi (hj1 eq_refl) hu1).
  - exact (holdsAtU_sound hK0 hklo hkhi (hj2 eq_refl) hu2).
  - exact (holdsAtU_sound hK0 hklo hkhi (hj3 eq_refl) hu3).
  - exact (holdsAtU_sound hK0 hklo hkhi (hj4 eq_refl) hu4).
  - apply Bool.orb_true_iff in hray as [hr5 | hri].
    + exact (holdsWithJBounds_ray_aux hU5 hklo hkhi hj5 hr5).
    + exact (holdsWithJBounds_ray_aux hU5 hklo hkhi hji hri).
Qed.

Local Lemma holdsAtU_mono {K0 jCoeff jv1 jv2 k_lo_u k_hi_u u : N}
    {alpha b1 b2 g1 g2 k_lo_c k_hi_c : Z}
    (hb : (b2 <= b1)%Z) (hg : (g2 <= g1)%Z) (hj : jv1 <= jv2)
    (hok : holdsAtU K0 alpha b1 g1 jCoeff jv1 k_lo_u k_lo_c k_hi_u k_hi_c u = true) :
  holdsAtU K0 alpha b2 g2 jCoeff jv2 k_lo_u k_lo_c k_hi_u k_hi_c u = true.
Proof.
  unfold holdsAtU in hok |- *.
  destruct ((Z.max (Z.of_N K0) (Z.of_N (k_lo_u * u) + k_lo_c) <=? Z.of_N (k_hi_u * u) + k_hi_c)%Z);
    [| reflexivity].
  apply Bool.andb_true_iff in hok as [h1 h2].
  apply Z.leb_le in h1; apply Z.leb_le in h2.
  assert (hju : (Z.of_N (jCoeff * jv1) <= Z.of_N (jCoeff * jv2))%Z) by (clear - hj; nia).
  assert (hbu : (Z.of_N u * b2 <= Z.of_N u * b1)%Z) by (clear - hb; nia).
  apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
Qed.

Local Lemma holdsWithJBounds_mono {K0 jCoeff k_lo_u k_hi_u : N}
    {alpha b1 b2 g1 g2 k_lo_c k_hi_c : Z} {jb1 jb2 : JBounds}
    (hb : (b2 <= b1)%Z) (hg : (g2 <= g1)%Z) (hjb : JBoundsLe jb1 jb2)
    (hok : holdsWithJBounds K0 alpha b1 g1 jCoeff jb1 k_lo_u k_lo_c k_hi_u k_hi_c = true) :
  holdsWithJBounds K0 alpha b2 g2 jCoeff jb2 k_lo_u k_lo_c k_hi_u k_hi_c = true.
Proof.
  destruct hjb as [hj1 [hj2 [hj3 [hj4 [hu5u [hu5c [hiu hic]]]]]]].
  unfold holdsWithJBounds in hok |- *.
  apply Bool.andb_true_iff in hok as [hok hray].
  cbn zeta in hray |- *.
  apply Bool.andb_true_iff in hok as [hok h4].
  apply Bool.andb_true_iff in hok as [hok h3].
  apply Bool.andb_true_iff in hok as [h1 h2].
  repeat (apply Bool.andb_true_iff; split);
    [exact (holdsAtU_mono hb hg hj1 h1)
    | exact (holdsAtU_mono hb hg hj2 h2)
    | exact (holdsAtU_mono hb hg hj3 h3)
    | exact (holdsAtU_mono hb hg hj4 h4) |].
  apply Bool.orb_true_iff in hray as [hr5 | hri]; apply Bool.orb_true_iff.
  - left; apply Bool.andb_true_iff in hr5 as [v1 v5]; apply Z.leb_le in v1; apply Z.leb_le in v5.
    assert (hm1 : (Z.of_N (jCoeff * jb_u5_u jb1) <= Z.of_N (jCoeff * jb_u5_u jb2))%Z)
      by (clear - hu5u; nia).
    assert (hm2 : (Z.of_N jCoeff * jb_u5_c jb1 <= Z.of_N jCoeff * jb_u5_c jb2)%Z)
      by (clear - hu5c; nia).
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
  - right; apply Bool.andb_true_iff in hri as [v1 v5]; apply Z.leb_le in v1; apply Z.leb_le in v5.
    assert (hm1 : (Z.of_N (jCoeff * jb_inf_u jb1) <= Z.of_N (jCoeff * jb_inf_u jb2))%Z)
      by (clear - hiu; nia).
    assert (hm2 : (Z.of_N jCoeff * jb_inf_c jb1 <= Z.of_N jCoeff * jb_inf_c jb2)%Z)
      by (clear - hic; nia).
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
Qed.

Local Lemma dominantJuMin_shift {K0 jCoeff k_lo_u k_hi_u : N}
    {alpha b1 b2 g1 g2 k_lo_c k_hi_c : Z}
    {jb : JBounds} {jc0 ju_r ju_q jc : Z} {step_ju : N}
    (hdom : (Z.of_N (dominantJuMin jb jc0) <= ju_r)%Z)
    (hstep : ju_q = (ju_r + Z.of_N step_ju)%Z)
    (hjc : jc = jc0)
    (hb : (b2 <= b1 + Z.of_N (jCoeff * step_ju))%Z)
    (hg : (g2 <= g1)%Z)
    (hok : holdsWithJBounds K0 alpha b1 g1 jCoeff (addJBound jb ju_r jc0)
             k_lo_u k_lo_c k_hi_u k_hi_c = true) :
  holdsWithJBounds K0 alpha b2 g2 jCoeff (addJBound jb ju_q jc)
    k_lo_u k_lo_c k_hi_u k_hi_c = true.
Proof.
  assert (hju_nonneg : (0 <= ju_r)%Z) by (clear - hdom; lia).
  assert (hdom_n : dominantJuMin jb jc0 <= Z.to_N ju_r) by (clear - hdom; lia).
  pose proof (proj1 (toNatClip_spec ju_r) hju_nonneg) as hju_toN; unfold toNatClip in hju_toN.
  unfold dominantJuMin in hdom_n; cbn zeta in hdom_n.
  repeat rewrite N.max_lub_iff in hdom_n.
  destruct hdom_n as [[h_neg [h_u5 h_inf]] [[h_r1 h_r2] [h_r3 [h_r4 h_r5]]]].
  pose proof (proj2 (proj2 (toNatClip_spec (- jc0)%Z))) as hc_neg.
  pose proof (proj2 (proj2 (toNatClip_spec (Z.of_N (jb_at1 jb) - jc0)%Z))) as hc1.
  pose proof (proj2 (proj2 (toNatClip_spec (Z.of_N (jb_at2 jb) - jc0)%Z))) as hc2.
  pose proof (proj2 (proj2 (toNatClip_spec (Z.of_N (jb_at3 jb) - jc0)%Z))) as hc3.
  pose proof (proj2 (proj2 (toNatClip_spec (Z.of_N (jb_at4 jb) - jc0)%Z))) as hc4.
  pose proof (proj2 (proj2 (toNatClip_spec (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb - jc0)%Z))) as hc5.
  pose proof (ceil_div_mul_ge (toNatClip (Z.of_N (jb_at2 jb) - jc0)%Z) 2 ltac:(lia)) as hd2.
  pose proof (ceil_div_mul_ge (toNatClip (Z.of_N (jb_at3 jb) - jc0)%Z) 3 ltac:(lia)) as hd3.
  pose proof (ceil_div_mul_ge (toNatClip (Z.of_N (jb_at4 jb) - jc0)%Z) 4 ltac:(lia)) as hd4.
  pose proof (ceil_div_mul_ge (toNatClip (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb - jc0)%Z) 5 ltac:(lia)) as hd5.
  replace (toNatClip (Z.of_N (jb_at2 jb) - jc0)%Z + 2 - 1)
    with (toNatClip (Z.of_N (jb_at2 jb) - jc0)%Z + 1) in hd2 by lia.
  replace (toNatClip (Z.of_N (jb_at3 jb) - jc0)%Z + 3 - 1)
    with (toNatClip (Z.of_N (jb_at3 jb) - jc0)%Z + 2) in hd3 by lia.
  replace (toNatClip (Z.of_N (jb_at4 jb) - jc0)%Z + 4 - 1)
    with (toNatClip (Z.of_N (jb_at4 jb) - jc0)%Z + 3) in hd4 by lia.
  replace (toNatClip (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb - jc0)%Z + 5 - 1)
    with (toNatClip (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb - jc0)%Z + 4) in hd5 by lia.
  assert (hu5_lt : (Z.of_N (jb_u5_u jb + 1) <= ju_r)%Z) by (clear - h_u5 hju_toN; lia).
  assert (hinf_lt : (Z.of_N (jb_inf_u jb + 1) <= ju_r)%Z) by (clear - h_inf hju_toN; lia).
  assert (hjc0_ge : (0 <= ju_r + jc0)%Z) by (clear - h_neg hc_neg hju_toN; lia).
  assert (hat1_dom : (Z.of_N (jb_at1 jb) <= ju_r + jc0)%Z) by (clear - h_r1 hc1 hju_toN; lia).
  assert (hat2_dom : (Z.of_N (jb_at2 jb) <= 2 * ju_r + jc0)%Z) by (clear - h_r2 hc2 hd2 hju_toN; lia).
  assert (hat3_dom : (Z.of_N (jb_at3 jb) <= 3 * ju_r + jc0)%Z) by (clear - h_r3 hc3 hd3 hju_toN; lia).
  assert (hat4_dom : (Z.of_N (jb_at4 jb) <= 4 * ju_r + jc0)%Z) by (clear - h_r4 hc4 hd4 hju_toN; lia).
  assert (h5_dom : (Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb <= 5 * ju_r + jc0)%Z)
    by (clear - h_r5 hc5 hd5 hju_toN; lia).
  clear hju_nonneg hju_toN h_neg h_u5 h_inf h_r1 h_r2 h_r3 h_r4 h_r5
        hc_neg hc1 hc2 hc3 hc4 hc5 hd2 hd3 hd4 hd5.
  assert (heval_jb : forall (ju_x jc_x : Z),
      (ju_r <= ju_x)%Z -> jc_x = jc0 ->
      Z.of_N (jb_at1 (addJBound jb ju_x jc_x)) = (ju_x + jc0)%Z /\
      Z.of_N (jb_at2 (addJBound jb ju_x jc_x)) = (2 * ju_x + jc0)%Z /\
      Z.of_N (jb_at3 (addJBound jb ju_x jc_x)) = (3 * ju_x + jc0)%Z /\
      Z.of_N (jb_at4 (addJBound jb ju_x jc_x)) = (4 * ju_x + jc0)%Z /\
      Z.of_N (jb_u5_u (addJBound jb ju_x jc_x)) = ju_x /\
      jb_u5_c (addJBound jb ju_x jc_x) = jc0 /\
      Z.of_N (jb_inf_u (addJBound jb ju_x jc_x)) = ju_x /\
      jb_inf_c (addJBound jb ju_x jc_x) = jc0).
  { intros ju_x jc_x hjux ->.
    unfold addJBound.
    assert (hpos : (0 <? ju_x)%Z = true) by (apply Z.ltb_lt; lia).
    rewrite hpos; cbn [orb].
    assert (hjux_n : Z.of_N (Z.to_N ju_x) = ju_x)
      by exact (proj1 (toNatClip_spec ju_x) ltac:(clear - hu5_lt hjux; lia)).
    assert (hu5_ltb : (jb_u5_u jb <? Z.to_N ju_x) = true)
      by (apply N.ltb_lt; clear - hu5_lt hjux hjux_n; lia).
    assert (hinf_ltb : (jb_inf_u jb <? Z.to_N ju_x) = true)
      by (apply N.ltb_lt; clear - hinf_lt hjux hjux_n; lia).
    assert (hupd5 : (((Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb <? Z.of_N (5 * Z.to_N ju_x) + jc0)%Z ||
      ((Z.of_N (5 * Z.to_N ju_x) + jc0 =? Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb)%Z &&
       (jb_u5_u jb <? Z.to_N ju_x)))) = true).
    { destruct ((Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb <? Z.of_N (5 * Z.to_N ju_x) + jc0)%Z) eqn:Hlt5;
        [reflexivity |].
      apply Z.ltb_ge in Hlt5.
      assert (Heq5 : (Z.of_N (5 * Z.to_N ju_x) + jc0 =? Z.of_N (5 * jb_u5_u jb) + jb_u5_c jb)%Z = true)
        by (apply Z.eqb_eq; clear - h5_dom hjux hjux_n Hlt5; lia).
      rewrite Heq5, hu5_ltb; reflexivity. }
    rewrite hupd5, hinf_ltb; cbn [orb jb_at1 jb_at2 jb_at3 jb_at4 jb_u5_u jb_u5_c jb_inf_u jb_inf_c].
    pose proof (proj1 (toNatClip_spec (ju_x + jc0)%Z) ltac:(clear - hjc0_ge hjux; lia)) as ha1.
    pose proof (proj1 (toNatClip_spec (2 * ju_x + jc0)%Z) ltac:(clear - hjc0_ge hu5_lt hjux; lia)) as ha2.
    pose proof (proj1 (toNatClip_spec (3 * ju_x + jc0)%Z) ltac:(clear - hjc0_ge hu5_lt hjux; lia)) as ha3.
    pose proof (proj1 (toNatClip_spec (4 * ju_x + jc0)%Z) ltac:(clear - hjc0_ge hu5_lt hjux; lia)) as ha4.
    refine (conj _ (conj _ (conj _ (conj _ (conj hjux_n (conj eq_refl (conj hjux_n eq_refl))))))).
    - clear - hat1_dom hjux ha1; lia.
    - clear - hat2_dom hjux ha2; lia.
    - clear - hat3_dom hjux ha3; lia.
    - clear - hat4_dom hjux ha4; lia. }
  destruct (heval_jb ju_r jc0 ltac:(lia) eq_refl)
    as [hr1 [hr2 [hr3 [hr4 [hru5u [hru5c [hriu hric]]]]]]].
  destruct (heval_jb ju_q jc ltac:(lia) hjc)
    as [hq1 [hq2 [hq3 [hq4 [hqu5u [hqu5c [hqiu hqic]]]]]]].
  clear hu5_lt hinf_lt hjc0_ge hat1_dom hat2_dom hat3_dom hat4_dom h5_dom heval_jb.
  set (jbr := addJBound jb ju_r jc0) in *.
  set (jbq := addJBound jb ju_q jc) in *.
  assert (hat_shift : forall (u jvr jvq : N),
      Z.of_N jvq = (Z.of_N jvr + Z.of_N (u * step_ju))%Z ->
      holdsAtU K0 alpha b1 g1 jCoeff jvr k_lo_u k_lo_c k_hi_u k_hi_c u = true ->
      holdsAtU K0 alpha b2 g2 jCoeff jvq k_lo_u k_lo_c k_hi_u k_hi_c u = true).
  { clear - hb hg.
    intros u jvr jvq hjv hu_ok.
    unfold holdsAtU in hu_ok |- *.
    destruct ((Z.max (Z.of_N K0) (Z.of_N (k_lo_u * u) + k_lo_c) <=? Z.of_N (k_hi_u * u) + k_hi_c)%Z);
      [| reflexivity].
    apply Bool.andb_true_iff in hu_ok as [v1 v2].
    apply Z.leb_le in v1; apply Z.leb_le in v2.
    assert (hbu : (Z.of_N u * b2 <= Z.of_N u * b1 + Z.of_N u * Z.of_N (jCoeff * step_ju))%Z)
      by (clear - hb; nia).
    assert (hjvq : Z.of_N (jCoeff * jvq) =
                   (Z.of_N (jCoeff * jvr) + Z.of_N u * Z.of_N (jCoeff * step_ju))%Z)
      by (rewrite !N2Z.inj_mul in *; rewrite hjv; ring).
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia. }
  unfold holdsWithJBounds in hok |- *.
  apply Bool.andb_true_iff in hok as [hok hray].
  cbn zeta in hray |- *.
  apply Bool.andb_true_iff in hok as [hok hu4].
  apply Bool.andb_true_iff in hok as [hok hu3].
  apply Bool.andb_true_iff in hok as [hu1 hu2].
  repeat (apply Bool.andb_true_iff; split);
    [exact (hat_shift 1 (jb_at1 jbr) (jb_at1 jbq) ltac:(lia) hu1)
    | exact (hat_shift 2 (jb_at2 jbr) (jb_at2 jbq) ltac:(lia) hu2)
    | exact (hat_shift 3 (jb_at3 jbr) (jb_at3 jbq) ltac:(lia) hu3)
    | exact (hat_shift 4 (jb_at4 jbr) (jb_at4 jbq) ltac:(lia) hu4) |].
  apply Bool.orb_true_iff in hray as [hr5 | hri]; apply Bool.orb_true_iff.
  - left; apply Bool.andb_true_iff in hr5 as [v1 v5]; apply Z.leb_le in v1; apply Z.leb_le in v5.
    assert (hjq5 : Z.of_N (jCoeff * jb_u5_u jbq) =
                   (Z.of_N (jCoeff * jb_u5_u jbr) + Z.of_N (jCoeff * step_ju))%Z)
      by (clear - hru5u hqu5u hstep; rewrite !N2Z.inj_mul, hru5u, hqu5u, hstep; ring).
    rewrite hqu5c, <- hru5c.
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
  - right; apply Bool.andb_true_iff in hri as [v1 v5]; apply Z.leb_le in v1; apply Z.leb_le in v5.
    assert (hjqi : Z.of_N (jCoeff * jb_inf_u jbq) =
                   (Z.of_N (jCoeff * jb_inf_u jbr) + Z.of_N (jCoeff * step_ju))%Z)
      by (clear - hriu hqiu hstep; rewrite !N2Z.inj_mul, hriu, hqiu, hstep; ring).
    rewrite hqic, <- hric.
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
Qed.

Local Lemma floorMinU1_le (num_u num_c : Z) (den_u u_val q : N)
    (hU : 1 <= u_val) (hden : 0 < den_u)
    (h : (num_u * Z.of_N u_val + num_c < Z.of_N (den_u * u_val * (q + 1)))%Z) :
  floorMinU1 num_u num_c den_u <= q.
Proof.
  unfold floorMinU1.
  rewrite !N2Z.inj_mul, !N2Z.inj_add in h.
  destruct ((num_c <? 0)%Z) eqn:Hltc.
  - apply Z.ltb_lt in Hltc.
    destruct ((0 <=? num_u + num_c)%Z) eqn:Hgev; [| lia].
    apply Z.leb_le in Hgev.
    pose proof (proj1 (toNatClip_spec (num_u + num_c)%Z) Hgev) as hclip.
    destruct (div_mod_spec (toNatClip (num_u + num_c)%Z) den_u hden)
      as [qv [rv [hqv [_ [hqr hrv]]]]].
    rewrite hqv. clear - hU hden h Hltc hclip hqr hrv; nia.
  - apply Z.ltb_ge in Hltc.
    destruct ((0 <=? num_u)%Z) eqn:Hgeu; [| lia].
    apply Z.leb_le in Hgeu.
    pose proof (proj1 (toNatClip_spec num_u) Hgeu) as hclip.
    destruct (div_mod_spec (toNatClip num_u) den_u hden)
      as [qv [rv [hqv [_ [hqr hrv]]]]].
    rewrite hqv. clear - hU hden h Hltc hclip hqr hrv; nia.
Qed.

Local Lemma floorMaxU1_ge (num_u num_c : Z) (den_u u_val q : N)
    (hU : 1 <= u_val) (hden : 0 < den_u)
    (h : (Z.of_N (den_u * u_val * q) <= num_u * Z.of_N u_val + num_c)%Z) :
  q <= floorMaxU1 num_u num_c den_u.
Proof.
  destruct (N.eq_dec q 0) as [-> | hq0]; [lia |].
  unfold floorMaxU1.
  rewrite !N2Z.inj_mul in h.
  destruct ((num_c <=? 0)%Z) eqn:Hlec.
  - apply Z.leb_le in Hlec.
    assert (hu_ge : (Z.of_N (den_u * q) <= num_u)%Z) by (rewrite N2Z.inj_mul; clear - hU h Hlec; nia).
    assert (hgeu : (0 <=? num_u)%Z = true) by (apply Z.leb_le; lia).
    rewrite hgeu. apply (div_ge_of_mul_le _ den_u q hden).
    pose proof (proj1 (toNatClip_spec num_u) ltac:(lia)). lia.
  - apply Z.leb_gt in Hlec.
    assert (hv_ge : (Z.of_N (den_u * q) <= num_u + num_c)%Z) by (rewrite N2Z.inj_mul; clear - hU h Hlec; nia).
    assert (hgev : (0 <=? num_u + num_c)%Z = true) by (apply Z.leb_le; lia).
    rewrite hgev. apply (div_ge_of_mul_le _ den_u q hden).
    pose proof (proj1 (toNatClip_spec (num_u + num_c)%Z) ltac:(lia)). lia.
Qed.

Local Lemma twoDInitHiU_sound (nd : SymWaveNode) (u_val k0_val d0_val : N)
    (hU : 1 <= u_val)
    (hkhi : (Z.of_N k0_val <= Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)%Z)
    (hkhic : (nd_k_hi_c nd <= 0)%Z)
    (hd1 : 2 * d0_val <= 64 * nd_wRQ nd * u_val)
    (hd2 : 20 * d0_val + 64 * nd_pRQ nd * u_val + 1 <= 52 * k0_val) :
  2 * d0_val <= twoDInitHiU nd * u_val.
Proof.
  unfold twoDInitHiU.
  set (diff := (Z.of_N (52 * nd_k_hi_u nd) - Z.of_N (64 * nd_pRQ nd))%Z).
  set (u2 := toNatClip (cdivNat diff 10 + 1)%Z).
  destruct (N.min_spec (64 * nd_wRQ nd) u2) as [[_ ->] | [_ ->]]; [exact hd1 |].
  pose proof (cdivNat_upper diff 10 ltac:(lia)) as hc.
  fold u2 in hc. unfold diff in hc.
  rewrite !N2Z.inj_mul in hc, hkhi.
  clear - hU hkhi hkhic hd2 hc; nia.
Qed.

Fixpoint MemoValid (P : SymWaveNode -> Prop) (m : MemoTree) : Prop :=
  match m with
  | MLeaf => True
  | MNode _ l _ vs r => MemoValid P l /\ (forall x, In x vs -> P x) /\ MemoValid P r
  end.

Local Lemma eqJB_sound {a b : JBounds} (h : eqJB a b = true) : a = b.
Proof.
  destruct a, b; unfold eqJB in h; cbn in h.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [H ?]
  | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
  | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
  end; subst; reflexivity.
Qed.

Local Lemma eqTok1_sound {a b : BecTok1} (h : eqTok1 a b = true) : a = b.
Proof.
  destruct a, b; try reflexivity; discriminate h.
Qed.

Local Lemma eqWord1_sound : forall {a b : list BecTok1}, eqWord1 a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] h;
    [reflexivity | discriminate h | discriminate h |].
  cbn [eqWord1] in h. apply Bool.andb_true_iff in h as [h1 h2].
  rewrite (eqTok1_sound h1), (IH _ h2). reflexivity.
Qed.

Local Lemma eqWaveNode_sound {a b : SymWaveNode} (h : eqWaveNode a b = true) : a = b.
Proof.
  destruct a, b; unfold eqWaveNode in h; cbn [
    nd_Y nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
    nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
    nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_wRQ nd_pRQ] in h.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [H ?]
  | H : eqWord1 _ _ = true |- _ => apply eqWord1_sound in H
  | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
  | H : eqJB _ _ = true |- _ => apply eqJB_sound in H
  | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
  | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
  end; subst; reflexivity.
Qed.

Local Lemma listHasNode_sound {P : SymWaveNode -> Prop} {nd : SymWaveNode} {vs : list SymWaveNode}
    (hvs : forall x, In x vs -> P x) (h : listHasNode nd vs = true) : P nd.
Proof.
  induction vs as [| x xs IH]; [discriminate h |].
  cbn [listHasNode] in h.
  destruct (eqWaveNode nd x) eqn:Heq.
  - rewrite (eqWaveNode_sound Heq). exact (hvs x (or_introl eq_refl)).
  - exact (IH (fun y hy => hvs y (or_intror hy)) h).
Qed.

Local Lemma memoContainsAux_sound {P : SymWaveNode -> Prop} {hk : N} {nd : SymWaveNode} {m : MemoTree}
    (hm : MemoValid P m) (h : memoContainsAux hk nd m = true) : P nd.
Proof.
  induction m as [| c l IHl k vs r IHr]; [discriminate h |].
  destruct hm as [hml [hvs hmr]].
  cbn [memoContainsAux] in h.
  destruct (hk <? k); [exact (IHl hml h) |].
  destruct (k <? hk); [exact (IHr hmr h) |].
  exact (listHasNode_sound hvs h).
Qed.

Local Lemma memoContains_sound {P : SymWaveNode -> Prop} {m : MemoTree} {nd : SymWaveNode}
    (hm : MemoValid P m) (h : memoContains m nd = true) : P nd.
Proof.
  exact (memoContainsAux_sound hm h).
Qed.

Local Lemma balance_valid {P : SymWaveNode -> Prop} (c : MemoColor) (l : MemoTree) (k : N)
    (vs : list SymWaveNode) (r : MemoTree)
    (hl : MemoValid P l) (hvs : forall x, In x vs -> P x) (hr : MemoValid P r) :
  MemoValid P (balance c l k vs r).
Proof.
  destruct c; [exact (conj hl (conj hvs hr)) |].
  unfold balance.
  destruct l as [| cl ll lk lvs lr].
  - destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |].
    destruct cr; [| exact (conj hl (conj hvs hr))].
    destruct rl as [| crl rll rlk rlvs rlr].
    + destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |].
      destruct crr; [| exact (conj hl (conj hvs hr))].
      destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))).
    + destruct crl.
      * destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))).
      * destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |].
        destruct crr; [| exact (conj hl (conj hvs hr))].
        destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))).
  - destruct cl; [| destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |];
      destruct cr; [| exact (conj hl (conj hvs hr))];
      destruct rl as [| crl rll rlk rlvs rlr];
      [destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
       destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]
      | destruct crl;
        [destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd))))
        | destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
          destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]]]].
    destruct ll as [| cll lll llk llvs llr].
    + destruct lr as [| clr lrl lrk lrvs lrr].
      * destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |].
        destruct cr; [| exact (conj hl (conj hvs hr))].
        destruct rl as [| crl rll rlk rlvs rlr];
        [destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
         destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]
        | destruct crl;
          [destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd))))
          | destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
            destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]]].
      * destruct clr.
        -- destruct hl as [ha [hxv [hb [hyv hc]]]]; exact (conj (conj ha (conj hxv hb)) (conj hyv (conj hc (conj hvs hr)))).
        -- destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |].
           destruct cr; [| exact (conj hl (conj hvs hr))].
           destruct rl as [| crl rll rlk rlvs rlr];
           [destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
            destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]
           | destruct crl;
             [destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd))))
             | destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
               destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]]].
    + destruct cll.
      * destruct hl as [[ha [hxv hb]] [hyv hc]]; exact (conj (conj ha (conj hxv hb)) (conj hyv (conj hc (conj hvs hr)))).
      * destruct lr as [| clr lrl lrk lrvs lrr].
        -- destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |].
           destruct cr; [| exact (conj hl (conj hvs hr))].
           destruct rl as [| crl rll rlk rlvs rlr];
           [destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
            destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]
           | destruct crl;
             [destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd))))
             | destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
               destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]]].
        -- destruct clr.
           ++ destruct hl as [ha [hxv [hb [hyv hc]]]]; exact (conj (conj ha (conj hxv hb)) (conj hyv (conj hc (conj hvs hr)))).
           ++ destruct r as [| cr rl rk rvs rr]; [exact (conj hl (conj hvs hr)) |].
              destruct cr; [| exact (conj hl (conj hvs hr))].
              destruct rl as [| crl rll rlk rlvs rlr];
              [destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
               destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]
              | destruct crl;
                [destruct hr as [[hb [hyv hc]] [hzv hd]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd))))
                | destruct rr as [| crr rrl rrk rrvs rrr]; [exact (conj hl (conj hvs hr)) |];
                  destruct crr; [destruct hr as [hb [hyv [hc [hzv hd]]]]; exact (conj (conj hl (conj hvs hb)) (conj hyv (conj hc (conj hzv hd)))) | exact (conj hl (conj hvs hr))]]].
Qed.

Local Lemma insAux_valid {P : SymWaveNode -> Prop} (hk : N) {nd : SymWaveNode} (hnd : P nd)
    (m : MemoTree) (hm : MemoValid P m) : MemoValid P (insAux hk nd m).
Proof.
  induction m as [| c l IHl k vs r IHr].
  - cbn [insAux MemoValid]. split; [exact I | split; [intros x [<- | []]; exact hnd | exact I]].
  - destruct hm as [hml [hvs hmr]].
    cbn [insAux].
    destruct (hk <? k); [exact (balance_valid c _ k vs r (IHl hml) hvs hmr) |].
    destruct (k <? hk); [exact (balance_valid c l k vs _ hml hvs (IHr hmr)) |].
    destruct (listHasNode nd vs); [exact (conj hml (conj hvs hmr)) |].
    refine (conj hml (conj _ hmr)).
    intros x [<- | hx]; [exact hnd | exact (hvs x hx)].
Qed.

Local Lemma memoInsert_sound {P : SymWaveNode -> Prop} {m : MemoTree} {nd : SymWaveNode}
    (hm : MemoValid P m) (hnd : P nd) : MemoValid P (memoInsert m nd).
Proof.
  unfold memoInsert.
  pose proof (insAux_valid (hashNode nd) hnd m hm) as hins.
  destruct (insAux (hashNode nd) nd m); exact hins.
Qed.

#[local] Arguments hashNode : simpl never.
#[local] Arguments memoContains : simpl never.
#[local] Arguments memoInsert : simpl never.

Local Lemma findL0AnchorWalk_sound :
  forall (fuel : nat) (y_cur : list BecTok1) (q_cur q_max q0 wy0 py0 : N),
    noTrailZero y_cur = true ->
    findL0AnchorWalk fuel y_cur q_cur q_max = Some (q0, wy0, py0) ->
    exists d : N, q0 = q_cur + d /\ q0 <= q_max /\
      exists y0 : list BecTok1,
        RelT0Pow d y_cur y0 /\ noK1 y0 = true /\ noTrailZero y0 = true /\ hasI y0 = true /\
        wy0 = evalPhi 0 y0 /\ py0 = evalPhi 22 y0.
Proof.
  induction fuel as [| fuel IH]; intros y_cur q_cur q_max q0 wy0 py0 htz h;
    [discriminate h |].
  cbn [findL0AnchorWalk] in h.
  destruct (q_max <? q_cur) eqn:Hqm; [discriminate h |].
  apply N.ltb_ge in Hqm.
  destruct (noK1 y_cur && hasI y_cur) eqn:Hchk.
  - injection h as <- <- <-.
    apply Bool.andb_true_iff in Hchk as [hnk hhi].
    exists 0; split; [lia | split; [exact Hqm |]].
    exists y_cur.
    exact (conj (rt0_zero y_cur) (conj hnk (conj htz (conj hhi (conj eq_refl eq_refl))))).
  - destruct (Nat.eqb fuel 0%nat || (q_max <? q_cur + 1)); [discriminate h |].
    destruct (t0PowNorm wordFuel 1 y_cur) as [y_next |] eqn:Ht1; [| discriminate h].
    destruct (IH y_next (q_cur + 1) q_max q0 wy0 py0 (t0PowNorm_noTrailZero htz Ht1) h)
      as [d [-> [h2 [y0 [hrel [hnk [htz0 [hhi [hwy hpy]]]]]]]]].
    exists (1 + d); split; [lia | split; [exact h2 |]].
    exists y0.
    exact (conj (RelT0Pow_trans (t0PowNorm_sound Ht1) hrel)
      (conj hnk (conj htz0 (conj hhi (conj hwy hpy))))).
Qed.

Local Lemma findL0Anchor_sound :
  forall (fuel : nat) (w_y : list BecTok1) (q_cur q_max q0 wy0 py0 : N),
    noTrailZero w_y = true ->
    findL0Anchor fuel w_y q_cur q_max = Some (q0, wy0, py0) ->
    q_cur <= q0 /\ q0 <= q_max /\
    exists y0 : list BecTok1,
      RelT0Pow q0 w_y y0 /\ noK1 y0 = true /\ noTrailZero y0 = true /\ hasI y0 = true /\
      wy0 = evalPhi 0 y0 /\ py0 = evalPhi 22 y0.
Proof.
  intros fuel w_y q_cur q_max q0 wy0 py0 htz h.
  unfold findL0Anchor in h.
  destruct (q_max <? q_cur); [discriminate h |].
  destruct (t0PowNorm wordFuel q_cur w_y) as [y_cur |] eqn:Ht0; [| discriminate h].
  destruct (findL0AnchorWalk_sound fuel y_cur q_cur q_max q0 wy0 py0
              (t0PowNorm_noTrailZero htz Ht0) h)
    as [d [-> [h2 [y0 [hrel [hnk [htz0 [hhi [hwy hpy]]]]]]]]].
  split; [lia | split; [exact h2 |]].
  exists y0.
  exact (conj (RelT0Pow_trans (t0PowNorm_sound Ht0) hrel)
    (conj hnk (conj htz0 (conj hhi (conj hwy hpy))))).
Qed.

#[local] Arguments findL0AnchorWalk : simpl never.
#[local] Arguments findL0Anchor : simpl never.


(* ========================================================================== *)
(* Layer 3b Soundness Part 2: NodeState, checkAbstract, Stops & Wave Dichotomy *)
(* ========================================================================== *)

Local Lemma RelT0Pow_split2 :
  forall (m : N) {x z : list BecTok1},
    RelT0Pow (m + 2) x z ->
    exists q u1 : list BecTok1, RelT0Pow m x q /\ RelT M0 q u1 /\ RelT M0 u1 z.
Proof.
  intros m; induction m as [| m IH] using N_ind_add1; intros x z h.
  - replace (0 + 2) with 2 in h by lia.
    destruct (RelT0Pow_2_inv h) as [u1 [hs1 hs2]].
    exists x, u1; exact (conj (rt0_zero x) (conj hs1 hs2)).
  - replace (m + 1 + 2) with ((m + 2) + 1) in h by lia.
    destruct (RelT0Pow_succ_inv h) as [w1 [hs hrem]].
    destruct (IH _ _ hrem) as [q [u1 [hpow [hs1 hs2]]]].
    exists q, u1; exact (conj (rt0_succ hs hpow) (conj hs1 hs2)).
Qed.

Local Lemma RelT0Pow_split_add :
  forall (a b : N) {x z : list BecTok1},
    RelT0Pow (a + b) x z ->
    exists y : list BecTok1, RelT0Pow a x y /\ RelT0Pow b y z.
Proof.
  intros a b; induction a as [| a IH] using N_ind_add1; intros x z h.
  - replace (0 + b) with b in h by lia.
    exists x; exact (conj (rt0_zero x) h).
  - replace (a + 1 + b) with ((a + b) + 1) in h by lia.
    destruct (RelT0Pow_succ_inv h) as [w1 [hs hrem]].
    destruct (IH _ _ hrem) as [y [ha hb]].
    exists y; exact (conj (rt0_succ hs ha) hb).
Qed.

Local Lemma collar_step_inC1_pow {k_col : N} {M W u2 : list BecTok1}
    (hK : 1 <= k_col) (ht1 : RelT M1 M W) (hpow : RelT0Pow (k_col + 1) W u2) :
  cfgCollar k_col (TokI :: Tok1 :: M) -->+
    cfgCollar (k_col + 1 + leadB (norm1 u2)) (dropB (norm1 u2)).
Proof.
  replace (k_col + 1) with ((k_col - 1) + 2) in hpow by lia.
  destruct (RelT0Pow_split2 (k_col - 1) hpow) as [Qw [u1 [hp [hs1 hs2]]]].
  exact (collar_step_inC1 hK ht1 hp hs1 hs2).
Qed.

Local Lemma cfgCollar_append_norm1 (k_col : N) (P v : list BecTok1) :
  cfgCollar k_col (P ++ norm1 v) = cfgCollar k_col (P ++ v).
Proof.
  unfold cfgCollar, evalBecCfg.
  replace ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ P ++ norm1 v)
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ P) ++ norm1 v)
    by (rewrite <- !app_assoc; reflexivity).
  replace ([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ P ++ v)
    with (([TokB; TokB; Tok0; Tok1] ++ repB k_col ++ P) ++ v)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite !decode1_append, (becLeft_append_eq (becLeft_decode1_norm1 v)).
  reflexivity.
Qed.

Definition withY (nd : SymWaveNode) (y' : list BecTok1) : SymWaveNode :=
  mkWaveNode (nd_s nd) (nd_db_shift nd) (nd_has_i1_front nd)
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    (nd_w_lo_u nd) (nd_w_lo_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
    (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (nd_jb nd) y' (nd_wRQ nd) (nd_pRQ nd).

Definition nodeCfg (nd : SymWaveNode) (k0 j_val : N) (P : list BecTok1) : Q * tape :=
  cfgCollar (k0 + nd_extra_B nd + j_val)
    (if nd_has_i1_front nd then TokI :: Tok1 :: (P ++ nd_Y nd) else P ++ nd_Y nd).

Record NodeState (nd : SymWaveNode) (u_val k0 d0 j_val : N) (P : list BecTok1) : Prop := mkNodeState {
  nst_U : 1 <= u_val;
  nst_K64 : 64 <= k0;
  nst_s6 : nd_s nd <= 6;
  nst_dbs : nd_db_shift nd <= nd_s nd;
  nst_noP : noK1 P = true;
  nst_powP : 2 ^ countBin P = msOf (nd_s nd) * u_val;
  nst_leadP : nd_has_i1_front nd = false -> leadB P = 0;
  nst_nhP : nd_has_i1_front nd = true -> notHeadI (P ++ nd_Y nd) = true;
  nst_tzY : noTrailZero (nd_Y nd) = true;
  nst_klo : (Z.of_N (nd_k_lo_u nd * u_val) + nd_k_lo_c nd <= Z.of_N k0)%Z;
  nst_khi : (Z.of_N k0 <= Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)%Z;
  nst_wlo : (Z.of_N (nd_w_lo_u nd * u_val) + nd_w_lo_c nd <= Z.of_N (evalPhi 0 P))%Z;
  nst_whi : (Z.of_N (evalPhi 0 P) <= Z.of_N (nd_w_hi_u nd * u_val) + nd_w_hi_c nd)%Z;
  nst_jb : JBoundsValid (nd_jb nd) u_val j_val;
  nst_db : pow2N (nd_db_shift nd) * deltaB P + j_val <= d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd;
  nst_d1 : 2 * d0 <= 64 * nd_wRQ nd * u_val;
  nst_d2 : 20 * d0 + 64 * nd_pRQ nd * u_val + 1 <= 52 * k0;
  nst_wM_lo : 128 * nd_wRQ nd * u_val + 1 <= 7 * k0 + 4 * d0;
  nst_D_lo : nd_s nd = nd_db_shift nd -> d0 <= pow2N (nd_s nd) * (deltaB P + j_val);
  nst_kj : nd_has_i1_front nd = true ->
    (Z.of_N (2 * (k0 + j_val)) <= Z.of_N (nd_kj_hi_u nd * u_val) + nd_kj_hi_c nd)%Z;
  nst_hwj : nd_has_i1_front nd = true -> nd_s nd = nd_db_shift nd ->
    (Z.of_N (4 * d0) + Z.of_N (2 * nd_wj_k nd * k0) <=
      Z.of_N (pow2N (nd_s nd + 1) * evalPhi 0 P) +
      Z.of_N (pow2N (nd_s nd + 2) * deltaB P) +
      Z.of_N (2 * nd_wj_hi_u nd * u_val) + 2 * nd_wj_hi_c nd)%Z
}.

Definition NodeClosed (nd : SymWaveNode) : Prop :=
  forall u_val k0 d0 j_val P, NodeState nd u_val k0 d0 j_val P ->
    exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
      (InC0 k' tail' \/ InC1 k' tail').

Local Lemma canonNode_cfg (nd : SymWaveNode) (k0 j_val : N) (P : list BecTok1) :
  nodeCfg (canonNode nd) k0 j_val P = nodeCfg nd k0 j_val P.
Proof.
  unfold canonNode, nodeCfg; destruct (nd_has_i1_front nd); reflexivity.
Qed.

Local Lemma canonNode_state {nd : SymWaveNode} {u_val k0 d0 j_val : N} {P : list BecTok1}
    (hst : NodeState nd u_val k0 d0 j_val P) : NodeState (canonNode nd) u_val k0 d0 j_val P.
Proof.
  destruct hst as [hU hK64 hs6 hdbs hnoP hpowP hleadP hnhP htzY hklo hkhi hwlo hwhi hjb hdb hd1 hd2 hwM_lo hD_lo hkj hwj].
  unfold canonNode.
  destruct (nd_has_i1_front nd) eqn:Hfr; cbn [
    negb nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
    nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
    nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ].
  - constructor; cbn [
      negb nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
      nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
      nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
      try assumption; lia.
  - constructor; cbn [
      negb nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
      nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
      nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
      try assumption; intros h; discriminate h.
Qed.

Local Lemma hasI_append (xs ys : list BecTok1) :
  hasI (xs ++ ys) = (hasI xs || hasI ys).
Proof.
  induction xs as [| t xs IH]; [reflexivity |].
  destruct t; cbn [app hasI]; [exact IH | reflexivity | exact IH | exact IH].
Qed.

Local Lemma checkAbstract_mono (nd1 nd2 : SymWaveNode) (isHI1 isHI2 : bool)
    (wy1 wy2 py1 py2 : N)
    (hs : nd_s nd2 = nd_s nd1) (hdbs : nd_db_shift nd2 = nd_db_shift nd1)
    (hfr : nd_has_i1_front nd2 = nd_has_i1_front nd1)
    (hklu : nd_k_lo_u nd2 = nd_k_lo_u nd1) (hklc : nd_k_lo_c nd2 = nd_k_lo_c nd1)
    (hkhu : nd_k_hi_u nd2 = nd_k_hi_u nd1) (hkhc : nd_k_hi_c nd2 = nd_k_hi_c nd1)
    (hwhu : nd_w_hi_u nd2 = nd_w_hi_u nd1) (hwhc : nd_w_hi_c nd2 = nd_w_hi_c nd1)
    (heb : nd_extra_B nd2 = nd_extra_B nd1)
    (hsdu : nd_scaled_db_u nd2 = nd_scaled_db_u nd1) (hsdc : nd_scaled_db_c nd2 = nd_scaled_db_c nd1)
    (hprq : nd_pRQ nd2 = nd_pRQ nd1)
    (hHI : isHI1 = true -> isHI2 = true)
    (hwy : wy2 <= wy1) (hpy : py2 <= py1)
    (hjb : JBoundsLe (nd_jb nd1) (nd_jb nd2))
    (hok : checkAbstract nd1 true isHI1 wy1 py1 = true) :
  checkAbstract nd2 true isHI2 wy2 py2 = true.
Proof.
  unfold checkAbstract in hok |- *.
  rewrite hs, hdbs, hfr, hklu, hklc, hkhu, hkhc, hwhu, hwhc, heb, hsdu, hsdc, hprq.
  cbn [negb] in hok |- *.
  destruct (nd_has_i1_front nd1 && negb isHI1) eqn:H1; [discriminate hok |].
  assert (H2 : (nd_has_i1_front nd1 && negb isHI2) = false).
  { destruct (nd_has_i1_front nd1); [| reflexivity].
    cbn [andb] in H1 |- *. destruct isHI1; [| discriminate H1].
    rewrite (hHI eq_refl); reflexivity. }
  rewrite H2; cbn zeta in hok |- *.
  set (ms := msOf (nd_s nd1)) in *.
  set (denom := 20 * pow2N (nd_db_shift nd1)) in *.
  set (gw := if nd_has_i1_front nd1 then 7 else 10) in *.
  set (ap := if nd_has_i1_front nd1 then 52 else 101) in *.
  destruct (holdsWithJBounds 64 (- Z.of_N (2 * gw))%Z
              (Z.of_N (4 * (nd_w_hi_u nd1 + ms * wy1)))
              (4 * nd_w_hi_c nd1 + 2 - Z.of_N (2 * gw * nd_extra_B nd1))%Z
              gw (nd_jb nd1) (nd_k_lo_u nd1) (nd_k_lo_c nd1) (nd_k_hi_u nd1) (nd_k_hi_c nd1))
    eqn:Hw1; [cbn [negb] in hok | discriminate hok].
  assert (hms_wy : ms * wy2 <= ms * wy1) by exact (N.mul_le_mono_l _ _ ms hwy).
  assert (Hw2 : holdsWithJBounds 64 (- Z.of_N (2 * gw))%Z
              (Z.of_N (4 * (nd_w_hi_u nd1 + ms * wy2)))
              (4 * nd_w_hi_c nd1 + 2 - Z.of_N (2 * gw * nd_extra_B nd1))%Z
              gw (nd_jb nd2) (nd_k_lo_u nd1) (nd_k_lo_c nd1) (nd_k_hi_u nd1) (nd_k_hi_c nd1) = true).
  { refine (holdsWithJBounds_mono _ (Z.le_refl _) hjb Hw1). clear - hms_wy; clearbody ms; lia. }
  rewrite Hw2; cbn [negb].
  assert (hms_py : denom * (nd_w_hi_u nd1 + ms * py2) <= denom * (nd_w_hi_u nd1 + ms * py1))
    by (apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_l; exact hpy).
  refine (holdsWithJBounds_mono _ (Z.le_refl _) hjb hok).
  clear - hms_py; clearbody denom ms; lia.
Qed.

Local Lemma checkAbstract_shift (ndTpl : SymWaveNode) (jb : JBounds)
    (jc0 ju_r ju_q jc : Z) (delta step_mul : N) (wy_r wy_q py_r py_q : N)
    (hdom : (Z.of_N (dominantJuMin jb jc0) <= ju_r)%Z)
    (hstep : ju_q = (ju_r + Z.of_N (delta * step_mul))%Z)
    (hjc : jc = jc0)
    (hmul : 2 * msOf (nd_s ndTpl) <= step_mul)
    (hwy : wy_q <= wy_r + delta) (hpy : py_q <= py_r + delta)
    (hok : checkAbstract (withJB ndTpl (addJBound jb ju_r jc0)) true true wy_r py_r = true) :
  checkAbstract (withJB ndTpl (addJBound jb ju_q jc)) true true wy_q py_q = true.
Proof.
  unfold checkAbstract, withJB in hok |- *.
  cbn [negb nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
       nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c nd_pRQ nd_jb] in hok |- *.
  rewrite Bool.andb_false_r in hok |- *.
  cbn zeta in hok |- *.
  set (ms := msOf (nd_s ndTpl)) in *.
  set (denom := 20 * pow2N (nd_db_shift ndTpl)) in *.
  set (gw := if nd_has_i1_front ndTpl then 7 else 10) in *.
  set (ap := if nd_has_i1_front ndTpl then 52 else 101) in *.
  assert (hgw_ge : 7 <= gw) by (unfold gw; destruct (nd_has_i1_front ndTpl); lia).
  assert (hap_ge : 52 <= ap) by (unfold ap; destruct (nd_has_i1_front ndTpl); lia).
  destruct (holdsWithJBounds 64 (- Z.of_N (2 * gw))%Z
              (Z.of_N (4 * (nd_w_hi_u ndTpl + ms * wy_r)))
              (4 * nd_w_hi_c ndTpl + 2 - Z.of_N (2 * gw * nd_extra_B ndTpl))%Z
              gw (addJBound jb ju_r jc0)
              (nd_k_lo_u ndTpl) (nd_k_lo_c ndTpl) (nd_k_hi_u ndTpl) (nd_k_hi_c ndTpl))
    eqn:Hw1; [cbn [negb] in hok | discriminate hok].
  assert (hw1 : ms * wy_q <= ms * wy_r + ms * delta)
    by (rewrite <- N.mul_add_distr_l; exact (N.mul_le_mono_l _ _ ms hwy)).
  assert (hw2 : 2 * (ms * delta) <= delta * step_mul)
    by (replace (2 * (ms * delta)) with (delta * (2 * ms)) by ring;
        exact (N.mul_le_mono_l _ _ delta hmul)).
  assert (hw3 : 7 * (delta * step_mul) <= gw * (delta * step_mul))
    by exact (N.mul_le_mono_r _ _ (delta * step_mul) hgw_ge).
  assert (hb_w : 4 * (nd_w_hi_u ndTpl + ms * wy_q) <=
                 4 * (nd_w_hi_u ndTpl + ms * wy_r) + gw * (delta * step_mul))
    by (clear - hw1 hw2 hw3; clearbody ms gw; lia).
  assert (Hw2 : holdsWithJBounds 64 (- Z.of_N (2 * gw))%Z
              (Z.of_N (4 * (nd_w_hi_u ndTpl + ms * wy_q)))
              (4 * nd_w_hi_c ndTpl + 2 - Z.of_N (2 * gw * nd_extra_B ndTpl))%Z
              gw (addJBound jb ju_q jc)
              (nd_k_lo_u ndTpl) (nd_k_lo_c ndTpl) (nd_k_hi_u ndTpl) (nd_k_hi_c ndTpl) = true).
  { refine (dominantJuMin_shift hdom hstep hjc _ (Z.le_refl _) Hw1).
    clear - hb_w; clearbody ms gw; lia. }
  rewrite Hw2; cbn [negb].
  assert (hp1 : ms * py_q <= ms * py_r + ms * delta)
    by (rewrite <- N.mul_add_distr_l; exact (N.mul_le_mono_l _ _ ms hpy)).
  assert (hp2 : denom * (nd_w_hi_u ndTpl + ms * py_q) <=
                denom * (nd_w_hi_u ndTpl + ms * py_r) + denom * (delta * step_mul))
    by (rewrite <- N.mul_add_distr_l; apply N.mul_le_mono_l; clear - hp1 hw2; clearbody ms; lia).
  assert (hp3 : 2 * (denom * (delta * step_mul)) <= (440 + denom * ap) * (delta * step_mul)).
  { replace (2 * (denom * (delta * step_mul))) with ((2 * denom) * (delta * step_mul)) by ring.
    apply N.mul_le_mono_r; clear - hap_ge; clearbody denom ap; nia. }
  assert (hb_p : 2 * (denom * (nd_w_hi_u ndTpl + ms * py_q) + 440 * nd_scaled_db_u ndTpl) <=
                 2 * (denom * (nd_w_hi_u ndTpl + ms * py_r) + 440 * nd_scaled_db_u ndTpl) +
                 (440 + denom * ap) * (delta * step_mul))
    by (clear - hp2 hp3; clearbody ms denom ap; lia).
  refine (dominantJuMin_shift hdom hstep hjc _ (Z.le_refl _) hok).
  clear - hb_p; clearbody ms denom ap; lia.
Qed.

Local Lemma checkAbstract_sound {nd : SymWaveNode} {u_val k0 d0 j_val : N} {P : list BecTok1}
    {isHI : bool} {wy py_hi : N}
    (hst : NodeState nd u_val k0 d0 j_val P)
    (hyL0 : noK1 (nd_Y nd) = true)
    (hHI : isHI = true -> hasI (nd_Y nd) = true)
    (hwy : evalPhi 0 (nd_Y nd) <= wy)
    (hpy : evalPhi 22 (nd_Y nd) <= py_hi)
    (hok : checkAbstract nd true isHI wy py_hi = true) :
  exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
    (InC0 k' tail' \/ InC1 k' tail').
Proof.
  destruct hst as [hU hK64 _ _ hnoP hpowP _ hnhP _ hklo hkhi _ hwhi hjb hdb _ hd2 _ _ _ _].
  unfold checkAbstract in hok; cbn [negb] in hok.
  destruct (nd_has_i1_front nd && negb isHI) eqn:Hfr_hi; [discriminate hok |].
  cbn zeta in hok.
  set (ms := msOf (nd_s nd)) in *.
  set (denom := 20 * pow2N (nd_db_shift nd)) in *.
  set (gw := if nd_has_i1_front nd then 7 else 10) in *.
  set (ap := if nd_has_i1_front nd then 52 else 101) in *.
  assert (hdenom_pos : 0 < denom)
    by (unfold denom; rewrite pow2N_eq; pose proof (pow2_pos (nd_db_shift nd)); lia).
  destruct (holdsWithJBounds 64 (- Z.of_N (2 * gw))%Z
              (Z.of_N (4 * (nd_w_hi_u nd + ms * wy)))
              (4 * nd_w_hi_c nd + 2 - Z.of_N (2 * gw * nd_extra_B nd))%Z
              gw (nd_jb nd) (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd))
    eqn:Hw_ok; [cbn [negb] in hok | discriminate hok].
  pose proof (holdsWithJBounds_sound hjb hU hK64 hklo hkhi Hw_ok) as hw_ineq.
  pose proof (holdsWithJBounds_sound hjb hU hK64 hklo hkhi hok) as hp_ineq.
  set (K_cur := k0 + nd_extra_B nd + j_val).
  set (M := P ++ nd_Y nd).
  assert (hnoM : noK1 M = true) by (unfold M; rewrite noK1_append, hnoP, hyL0; reflexivity).
  assert (hwM_eq : evalPhi 0 M = evalPhi 0 P + (ms * u_val) * evalPhi 0 (nd_Y nd))
    by (unfold M; rewrite (evalPhi_append 0), hpowP; reflexivity).
  assert (hpM_eq : evalPhi 22 M = evalPhi 0 P + 22 * deltaB P + (ms * u_val) * evalPhi 22 (nd_Y nd))
    by (unfold M; rewrite (evalPhi_append 22), (evalPhi_eq_zero_add_deltaB 22 P), hpowP; reflexivity).
  assert (hwM_bound : 2 * evalPhi 0 M < gw * K_cur).
  { assert (h1 : (ms * u_val) * evalPhi 0 (nd_Y nd) <= (ms * wy) * u_val)
      by (replace ((ms * u_val) * evalPhi 0 (nd_Y nd)) with ((ms * evalPhi 0 (nd_Y nd)) * u_val) by ring;
          apply N.mul_le_mono_r, N.mul_le_mono_l; exact hwy).
    assert (h2 : (Z.of_N (evalPhi 0 M) <=
                  Z.of_N (nd_w_hi_u nd * u_val) + Z.of_N ((ms * wy) * u_val) + nd_w_hi_c nd)%Z)
      by (clear - hwM_eq h1 hwhi; clearbody ms M; lia).
    assert (hring_w :
      ((- Z.of_N (2 * gw)) * Z.of_N k0 +
       Z.of_N (4 * (nd_w_hi_u nd + ms * wy)) * Z.of_N u_val +
       (4 * nd_w_hi_c nd + 2 - Z.of_N (2 * gw * nd_extra_B nd)) -
       Z.of_N (gw * (2 * j_val)) =
       4 * (Z.of_N (nd_w_hi_u nd * u_val) + Z.of_N ((ms * wy) * u_val) + nd_w_hi_c nd) + 2 -
       2 * Z.of_N (gw * K_cur))%Z)
      by (unfold K_cur; repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
    clear - hw_ineq h2 hring_w; clearbody ms gw K_cur M; lia. }
  assert (hpM_bound : evalPhi 22 M < ap * K_cur).
  { assert (hpy_u : (ms * u_val) * evalPhi 22 (nd_Y nd) <= (ms * py_hi) * u_val)
      by (replace ((ms * u_val) * evalPhi 22 (nd_Y nd)) with ((ms * evalPhi 22 (nd_Y nd)) * u_val) by ring;
          apply N.mul_le_mono_r, N.mul_le_mono_l; exact hpy).
    assert (hsum : (Z.of_N (evalPhi 0 P + (ms * u_val) * evalPhi 22 (nd_Y nd)) <=
                    Z.of_N (nd_w_hi_u nd * u_val) + Z.of_N ((ms * py_hi) * u_val) + nd_w_hi_c nd)%Z)
      by (clear - hpy_u hwhi; clearbody ms; lia).
    pose proof (Z.mul_le_mono_nonneg_l _ _ (Z.of_N (2 * denom)) ltac:(lia) hsum) as hsum_s.
    assert (hgoal_z : (Z.of_N (2 * denom) * Z.of_N (evalPhi 22 M + 1) <=
                       Z.of_N (2 * denom) * Z.of_N (ap * K_cur))%Z).
    { assert (hring_p :
        (Z.of_N (2 * denom) * Z.of_N (evalPhi 22 M + 1) -
         Z.of_N (2 * denom) * Z.of_N (ap * K_cur) =
         (Z.of_N (2 * denom) * Z.of_N (evalPhi 0 P + (ms * u_val) * evalPhi 22 (nd_Y nd)) -
          Z.of_N (2 * denom) * (Z.of_N (nd_w_hi_u nd * u_val) + Z.of_N ((ms * py_hi) * u_val) + nd_w_hi_c nd)) +
         880 * (Z.of_N (pow2N (nd_db_shift nd) * deltaB P + j_val) -
                Z.of_N (d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd)) +
         44 * (Z.of_N (20 * d0 + 64 * nd_pRQ nd * u_val + 1) - Z.of_N (52 * k0)) +
         ((Z.of_N (2 * 22 * 52) - Z.of_N (2 * denom * ap)) * Z.of_N k0 +
          (Z.of_N (2 * (denom * (nd_w_hi_u nd + ms * py_hi) + 440 * nd_scaled_db_u nd)) -
           Z.of_N (2 * 64 * 22 * nd_pRQ nd)) * Z.of_N u_val +
          (Z.of_N (2 * denom) * (nd_w_hi_c nd + 1 - Z.of_N (ap * nd_extra_B nd)) +
           (Z.of_N (2 * 22 * 20 * nd_scaled_db_c nd) - Z.of_N (2 * 22))) -
          Z.of_N ((440 + denom * ap) * (2 * j_val))))%Z)
        by (rewrite hpM_eq; unfold K_cur, denom; repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      clear - hp_ineq hsum_s hdb hd2 hring_p; clearbody denom ms ap K_cur M; lia. }
    rewrite <- !N2Z.inj_mul, <- N2Z.inj_le in hgoal_z.
    apply N.mul_le_mono_pos_l in hgoal_z; clear - hdenom_pos hgoal_z; clearbody denom ap K_cur M; lia. }
  unfold nodeCfg; fold K_cur M.
  unfold gw, ap in hwM_bound, hpM_bound.
  destruct (nd_has_i1_front nd) eqn:Hfr; cbv iota in hwM_bound, hpM_bound.
  - (* has_i1_front = true -> InC1 *)
    assert (hisHI : isHI = true)
      by (destruct isHI; [reflexivity | discriminate Hfr_hi]).
    pose proof (hHI hisHI) as hIY.
    assert (hIM : hasI M = true) by (unfold M; rewrite hasI_append, hIY, Bool.orb_true_r; reflexivity).
    pose proof (hnhP eq_refl) as hnhM; fold M in hnhM.
    assert (hnorm_i1 : norm1 (TokI :: Tok1 :: M) = TokI :: Tok1 :: trimZero M).
    { assert (hcons1 : consNorm Tok1 M = Tok1 :: M).
      { destruct M as [| u us]; [reflexivity |].
        destruct u; [reflexivity | discriminate hnhM | reflexivity | reflexivity]. }
      unfold norm1; cbn [coalesce].
      rewrite (coalesce_eq_of_noK1 hnoM), hcons1.
      exact (trimZero_i1_of_hasI hIM). }
    rewrite <- (cfgCollar_eq_norm1 K_cur (TokI :: Tok1 :: M)), hnorm_i1.
    exists K_cur, (TokI :: Tok1 :: trimZero M).
    split; [apply evstep_refl | right].
    pose proof (evalPhi_trimZero 0 M) as hw_tr.
    pose proof (evalPhi_trimZero 22 M) as hp_tr.
    assert (hIM_tr : hasI (trimZero M) = true) by (rewrite hasI_trimZero; exact hIM).
    unfold InC1; split; [unfold K_cur; lia |].
    exists (trimZero M).
    refine (conj eq_refl (conj (noK1_trimZero hnoM) (conj (noTrailZero_trimZero M)
      (conj (notHeadI_trimZero hnhM hIM) (conj hIM_tr _))))); lia.
  - (* has_i1_front = false -> InC0 *)
    rewrite <- (cfgCollar_norm1 K_cur M).
    exists (K_cur + leadB (norm1 M)), (dropB (norm1 M)).
    split; [apply evstep_refl | left].
    pose proof (evalPhi_norm1_of_noK1 0 hnoM) as hw_n.
    pose proof (evalPhi_norm1_of_noK1 22 hnoM) as hp_n.
    pose proof (evalPhi_leadB_dropB 0 (norm1 M)) as hw_d.
    pose proof (evalPhi_leadB_dropB 22 (norm1 M)) as hp_d.
    unfold InC0.
    refine (conj _ (conj (noK1_dropB (noK1_norm1 hnoM)) (conj (noTrailZero_dropB (noTrailZero_norm1 M)) _)));
      unfold K_cur in *; lia.
Qed.

Local Lemma findChildQStop_sound (nxTpl : SymWaveNode)
    (ms k_hi_u : N) (k_hi_c : Z) (w_hi_u : N) (w_hi_c : Z) (extra_B_parent : N)
    (q0 wy_b py_b q_max q_stop q : N) (y_q : list BecTok1) (jc : Z)
    (hms_pos : 0 < ms)
    (hms_le : 2 * msOf (nd_s nxTpl) <= ms)
    (hjc : jc = (- (2 * k_hi_c + w_hi_c + Z.of_N (2 * extra_B_parent)))%Z)
    (hstop : findChildQStop nxTpl ms k_hi_u k_hi_c w_hi_u w_hi_c extra_B_parent
               q0 wy_b py_b q_max = Some q_stop)
    (hge_stop : q_stop <= q) (hle_max : q <= q_max)
    (hpy_q : evalPhi 22 y_q <= py_b + (q - q0)) :
  q0 <= q /\
  (checkAbstract (withY nxTpl y_q) true true (wy_b + (q - q0)) (evalPhi 22 y_q) = true \/
   checkAbstract (withJB (withY nxTpl y_q)
     (addJBound (nd_jb nxTpl) (Z.of_N (q * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z jc))
     true true (wy_b + (q - q0)) (evalPhi 22 y_q) = true).
Proof.
  unfold findChildQStop in hstop.
  destruct (q_max <? q0) eqn:Hb0.
  - apply N.ltb_lt in Hb0; injection hstop as <-; lia.
  - apply N.ltb_ge in Hb0.
    destruct (checkAbstract nxTpl true true (wy_b + (q_max - q0)) (py_b + (q_max - q0))) eqn:Ha_max.
    + injection hstop as <-.
      split; [exact hge_stop | left].
      refine (checkAbstract_mono nxTpl (withY nxTpl y_q) true true _ _ _ _
        eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        (fun h => h) _ _ (JBoundsLe_refl _) Ha_max); lia.
    + cbn zeta in hstop.
      set (jc0 := (- (2 * k_hi_c + w_hi_c + Z.of_N (2 * extra_B_parent)))%Z) in *.
      set (min_ju := dominantJuMin (nd_jb nxTpl) jc0) in *.
      set (need := 2 * k_hi_u + w_hi_u + min_ju) in *.
      set (q_right := N.max q0 ((need + ms - 1) / ms)) in *.
      assert (hq0_le_qr : q0 <= q_right) by exact (N.le_max_l _ _).
      assert (hqr_ge : (need + ms - 1) / ms <= q_right) by exact (N.le_max_r _ _).
      pose proof (ceil_div_mul_ge need ms hms_pos) as hceil.
      assert (hdom_r : (Z.of_N min_ju <= Z.of_N (q_right * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z).
      { assert (hmul : need <= q_right * ms) by (clear - hqr_ge hceil; clearbody q_right need min_ju jc0; nia).
        unfold need in hmul; clear - hmul; clearbody q_right min_ju jc0; lia. }
      destruct (q_right <=? q_max) eqn:Hbr; [| discriminate hstop].
      set (ju_r := (Z.of_N (q_right * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z) in *.
      set (nx_r := withJB nxTpl (addJBound (nd_jb nxTpl) ju_r jc0)) in *.
      destruct (checkAbstract nx_r true true (wy_b + (q_right - q0)) (py_b + (q_right - q0))) eqn:Ha_r;
        [| discriminate hstop].
      assert (shift_from_qr : q_right <= q ->
        checkAbstract (withJB (withY nxTpl y_q)
          (addJBound (nd_jb nxTpl) (Z.of_N (q * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z jc))
          true true (wy_b + (q - q0)) (evalPhi 22 y_q) = true).
      { intros hqr_q.
        assert (ha_r_Y : checkAbstract (withJB (withY nxTpl y_q) (addJBound (nd_jb nxTpl) ju_r jc0))
                           true true (wy_b + (q_right - q0)) (py_b + (q_right - q0)) = true).
        { exact (checkAbstract_mono nx_r _ true true _ _ _ _
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
            (fun h => h) (N.le_refl _) (N.le_refl _) (JBoundsLe_refl _) Ha_r). }
        refine (checkAbstract_shift (withY nxTpl y_q) (nd_jb nxTpl) jc0 ju_r
          (Z.of_N (q * ms) - Z.of_N (2 * k_hi_u + w_hi_u))%Z jc (q - q_right) ms
          (wy_b + (q_right - q0)) (wy_b + (q - q0))
          (py_b + (q_right - q0)) (evalPhi 22 y_q)
          hdom_r _ hjc hms_le _ _ ha_r_Y).
        - unfold ju_r; assert (hsub : (q - q_right) * ms + q_right * ms = q * ms)
            by (clear - hqr_q; clearbody q_right need min_ju jc0; nia);
          clear - hsub; clearbody q_right need min_ju jc0; lia.
        - clear - hq0_le_qr hqr_q; clearbody q_right need min_ju jc0; lia.
        - clear - hq0_le_qr hqr_q hpy_q; clearbody q_right need min_ju jc0; lia. }
      destruct (q_right <=? q0) eqn:Hbr0.
      * apply N.leb_le in Hbr0; injection hstop as <-.
        assert (hqr_le : q_right <= q) by (clear - Hbr0 hge_stop; clearbody q_right need min_ju jc0; lia).
        exact (conj hge_stop (or_intror (shift_from_qr hqr_le))).
      * apply N.leb_gt in Hbr0.
        destruct (checkAbstract nxTpl true true (wy_b + (q_right - 1 - q0)) (py_b + (q_right - 1 - q0))) eqn:Ha_mid;
          injection hstop as <-.
        -- split; [exact hge_stop |].
           destruct (q <? q_right) eqn:Hlt_qr.
           ++ apply N.ltb_lt in Hlt_qr; left.
              refine (checkAbstract_mono nxTpl (withY nxTpl y_q) true true _ _ _ _
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                (fun h => h) _ _ (JBoundsLe_refl _) Ha_mid).
              ** clear - hge_stop Hlt_qr; clearbody q_right need min_ju jc0; lia.
              ** clear - hge_stop Hlt_qr hpy_q; clearbody q_right need min_ju jc0; lia.
           ++ apply N.ltb_ge in Hlt_qr; exact (or_intror (shift_from_qr Hlt_qr)).
        -- exact (conj (N.le_trans _ _ _ hq0_le_qr hge_stop) (or_intror (shift_from_qr hge_stop))).
Qed.

#[local] Arguments checkAbstract : simpl never.
#[local] Arguments findChildQStop : simpl never.

Local Lemma eq_repB_of_countBin_zero :
  forall {xs : list BecTok1},
    noK1 xs = true -> countBin xs = 0 -> xs = repB (deltaB xs).
Proof.
  induction xs as [| t rest IH]; intros hno hcb; [reflexivity |].
  destruct t; [cbn [countBin] in hcb; lia | cbn [countBin] in hcb; lia | discriminate hno |].
  cbn [noK1 countBin deltaB] in hno, hcb |- *.
  replace (1 + deltaB rest) with (deltaB rest + 1) by lia.
  rewrite repB_succ, <- (IH hno hcb). reflexivity.
Qed.

Local Lemma countBin_repB (k : N) : countBin (repB k) = 0.
Proof.
  induction k as [| k IH] using N_ind_add1; [reflexivity |].
  rewrite repB_succ; cbn [countBin]; exact IH.
Qed.

Local Lemma deltaB_repB_append (k : N) (w : list BecTok1) :
  deltaB (repB k ++ w) = k + deltaB w.
Proof.
  induction k as [| k IH] using N_ind_add1; [cbn; lia |].
  rewrite repB_succ; cbn [app deltaB]; rewrite IH; lia.
Qed.

Local Lemma noK1_repB_append (k : N) (w : list BecTok1) :
  noK1 (repB k ++ w) = noK1 w.
Proof.
  induction k as [| k IH] using N_ind_add1; [reflexivity |].
  rewrite repB_succ; cbn [app noK1]; exact IH.
Qed.

Local Lemma noK1_repB (k : N) : noK1 (repB k) = true.
Proof.
  pose proof (noK1_repB_append k []) as h.
  rewrite app_nil_r in h; exact h.
Qed.

Local Lemma deltaB_repB (k : N) : deltaB (repB k) = k.
Proof.
  pose proof (deltaB_repB_append k []) as h.
  rewrite app_nil_r in h; cbn [deltaB] in h; lia.
Qed.

Local Lemma evalPhi_zero_repB (k : N) : evalPhi 0 (repB k) = 0.
Proof.
  induction k as [| k IH] using N_ind_add1; [reflexivity |].
  rewrite repB_succ; cbn [evalPhi]; lia.
Qed.

Local Lemma evalPhi_two_repB (k : N) : evalPhi 2 (repB k) = 2 * k.
Proof.
  induction k as [| k IH] using N_ind_add1; [cbn; lia |].
  rewrite repB_succ; cbn [evalPhi]; rewrite IH; lia.
Qed.

Local Lemma hasI_t0Pow (n : N) {w : list BecTok1}
    (hno : noK1 w = true) (hI : hasI w = true) :
  hasI (t0Pow n w) = true.
Proof.
  apply (hasI_of_evalPhi_zero_pos (noK1_t0Pow n hno)).
  rewrite (evalPhi_t0Pow 0 n hno).
  pose proof (evalPhi_zero_pos_of_hasI hI); lia.
Qed.

Fixpoint prefixMod (n : N) (w : list BecTok1) : list BecTok1 :=
  match w with
  | [] => []
  | TokB :: xs => TokB :: prefixMod n xs
  | Tok0 :: xs => (if (n mod 2) =? 0 then Tok0 else TokI) :: prefixMod (n / 2) xs
  | TokI :: xs => (if (n mod 2) =? 0 then TokI else Tok0) :: prefixMod ((n + 1) / 2) xs
  | Tok1 :: xs => Tok1 :: xs
  end.

Local Lemma prefixMod_props :
  forall (P : list BecTok1), noK1 P = true ->
    forall (n : N),
      noK1 (prefixMod n P) = true /\
      countBin (prefixMod n P) = countBin P /\
      deltaB (prefixMod n P) = deltaB P /\
      evalPhi 0 (prefixMod n P) = (evalPhi 0 P + n) mod (2 ^ countBin P) /\
      leadB (prefixMod n P) = leadB P /\
      countB (prefixMod n P) = countB P.
Proof.
  induction P as [| t xs IH]; intros hP n.
  - cbn [prefixMod noK1 countBin deltaB evalPhi leadB countB].
    rewrite pow2_0, N.mod_1_r. repeat split; reflexivity.
  - destruct t; try discriminate hP; cbn [noK1] in hP.
    + (* Tok0 *)
      destruct (IH hP (n / 2)) as [hno [hcb [hdb [hw [_ hcntb]]]]].
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as mpow eqn:hM_def.
      assert (hpow : 2 ^ countBin (Tok0 :: xs) = 2 * mpow)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]]]];
      destruct (div_mod_spec (evalPhi 0 xs + (n / 2)) mpow hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) mod (2 * mpow) = 2 * R0).
        { refine (proj2 (@div_mod_unique (evalPhi 0 (Tok0 :: xs) + n) (2 * mpow) Q0 (2 * R0) _ _));
            [cbn [evalPhi]; clear - hnh_eq hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hpow, hdm; cbn [prefixMod]; rewrite Emod; cbn [N.eqb noK1 countBin deltaB evalPhi leadB countB].
        rewrite hw, hR0.
        repeat split; try assumption; try reflexivity; lia.
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) mod (2 * mpow) = 1 + 2 * R0).
        { refine (proj2 (@div_mod_unique (evalPhi 0 (Tok0 :: xs) + n) (2 * mpow) Q0 (1 + 2 * R0) _ _));
            [cbn [evalPhi]; clear - hnh_eq hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hpow, hdm; cbn [prefixMod]; rewrite Emod; cbn [N.eqb noK1 countBin deltaB evalPhi leadB countB].
        rewrite hw, hR0.
        repeat split; try assumption; try reflexivity; lia.
    + (* TokI *)
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as mpow eqn:hM_def.
      assert (hpow : 2 ^ countBin (TokI :: xs) = 2 * mpow)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [hn1 hn_eq]] | [Emod [hn1 hn_eq]]]]].
      * destruct (IH hP nh) as [hno [hcb [hdb [hw [_ hcntb]]]]].
        destruct (div_mod_spec (evalPhi 0 xs + nh) mpow hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) mod (2 * mpow) = 1 + 2 * R0).
        { refine (proj2 (@div_mod_unique (evalPhi 0 (TokI :: xs) + n) (2 * mpow) Q0 (1 + 2 * R0) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hpow, hdm; cbn [prefixMod]; rewrite Emod, hn1; cbn [N.eqb noK1 countBin deltaB evalPhi leadB countB].
        rewrite hw, hR0.
        repeat split; try assumption; try reflexivity; lia.
      * destruct (IH hP (nh + 1)) as [hno [hcb [hdb [hw [_ hcntb]]]]].
        destruct (div_mod_spec (evalPhi 0 xs + (nh + 1)) mpow hM) as [Q1 [R1 [hQ1 [hR1 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) mod (2 * mpow) = 2 * R1).
        { refine (proj2 (@div_mod_unique (evalPhi 0 (TokI :: xs) + n) (2 * mpow) Q1 (2 * R1) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hpow, hdm; cbn [prefixMod]; rewrite Emod, hn1; cbn [N.eqb noK1 countBin deltaB evalPhi leadB countB].
        rewrite hw, hR1.
        repeat split; try assumption; try reflexivity; lia.
    + (* TokB *)
      destruct (IH hP n) as [hno [hcb [hdb [hw [hlb hcntb]]]]].
      cbn [prefixMod noK1 countBin deltaB evalPhi leadB countB].
      rewrite N.add_0_l.
      repeat split; try assumption; lia.
Qed.

Local Lemma prefixMod_rel :
  forall (P : list BecTok1), noK1 P = true ->
    forall (n : N) {Y Y' : list BecTok1},
      RelT0Pow ((evalPhi 0 P + n) / (2 ^ countBin P)) Y Y' ->
      RelT0Pow n (P ++ Y) (prefixMod n P ++ Y').
Proof.
  induction P as [| t xs IH]; intros hP n Y Y' hY.
  - cbn [evalPhi countBin prefixMod app] in hY |- *.
    rewrite pow2_0, N.add_0_l, N.div_1_r in hY. exact hY.
  - destruct t; try discriminate hP; cbn [noK1] in hP.
    + (* Tok0 *)
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as mpow eqn:hM_def.
      assert (hpow : 2 ^ countBin (Tok0 :: xs) = 2 * mpow)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      rewrite hpow in hY.
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]]]];
      destruct (div_mod_spec (evalPhi 0 xs + nh) mpow hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) / (2 * mpow) = Q0).
        { refine (proj1 (@div_mod_unique (evalPhi 0 (Tok0 :: xs) + n) (2 * mpow) Q0 (2 * R0) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hdm, <- hQ0 in hY.
        pose proof (IH hP nh Y Y' hY) as hrel.
        cbn [prefixMod app]; rewrite Emod, hnh_eq; cbn [N.eqb app].
        rewrite hn_eq; exact (proj1 (RelT0Pow_bit hrel)).
      * assert (hdm : (evalPhi 0 (Tok0 :: xs) + n) / (2 * mpow) = Q0).
        { refine (proj1 (@div_mod_unique (evalPhi 0 (Tok0 :: xs) + n) (2 * mpow) Q0 (1 + 2 * R0) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hdm, <- hQ0 in hY.
        pose proof (IH hP nh Y Y' hY) as hrel.
        cbn [prefixMod app]; rewrite Emod, hnh_eq; cbn [N.eqb app].
        rewrite hn_eq; exact (proj1 (proj2 (RelT0Pow_bit hrel))).
    + (* TokI *)
      pose proof (pow2_pos (countBin xs)) as hM.
      remember (2 ^ countBin xs) as mpow eqn:hM_def.
      assert (hpow : 2 ^ countBin (TokI :: xs) = 2 * mpow)
        by (cbn [countBin]; rewrite pow2_succ, <- hM_def; reflexivity).
      rewrite hpow in hY.
      destruct (mod2_dichotomy n) as [nh [hnh_eq [[Emod [hn1 hn_eq]] | [Emod [hn1 hn_eq]]]]].
      * destruct (div_mod_spec (evalPhi 0 xs + nh) mpow hM) as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) / (2 * mpow) = Q0).
        { refine (proj1 (@div_mod_unique (evalPhi 0 (TokI :: xs) + n) (2 * mpow) Q0 (1 + 2 * R0) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hdm, <- hQ0 in hY.
        pose proof (IH hP nh Y Y' hY) as hrel.
        cbn [prefixMod app]; rewrite Emod, hn1; cbn [N.eqb app].
        rewrite hn_eq; exact (proj2 (proj2 (RelT0Pow_bit hrel))).
      * destruct (div_mod_spec (evalPhi 0 xs + (nh + 1)) mpow hM) as [Q1 [R1 [hQ1 [hR1 [hQR hRlt]]]]].
        assert (hdm : (evalPhi 0 (TokI :: xs) + n) / (2 * mpow) = Q1).
        { refine (proj1 (@div_mod_unique (evalPhi 0 (TokI :: xs) + n) (2 * mpow) Q1 (2 * R1) _ _));
            [cbn [evalPhi]; clear - hn_eq hQR; nia | clear - hRlt; lia]. }
        rewrite hdm, <- hQ1 in hY.
        pose proof (IH hP (nh + 1) Y Y' hY) as hrel.
        cbn [prefixMod app]; rewrite Emod, hn1; cbn [N.eqb app].
        rewrite hn_eq; exact (RelT0Pow_kI_odd hrel).
    + (* TokB *)
      cbn [evalPhi countBin] in hY; rewrite N.add_0_l in hY.
      pose proof (RelT0Pow_repB 1 (IH hP n Y Y' hY)) as hrep.
      cbn [repB Pos.iter prefixMod app] in hrep |- *.
      exact hrep.
Qed.

Local Lemma prefix_wave_dichotomy_aux :
  forall (m b : N) (P : list BecTok1) (n : N),
    1 <= m -> countBin P = m -> countB P = b -> noK1 P = true ->
    2 * (2 ^ m) <= n + 2 ->
    (exists (P_next : list BecTok1) (dJ q_abs : N),
      noK1 P_next = true /\
      countBin P_next = m - 1 /\
      deltaB P_next + dJ <= deltaB P + 2 ^ (m - 1) /\
      n + 3 <= 2 ^ (m - 1) * (q_abs + 3) /\
      (2 ^ m) * q_abs <= 2 * n + 2 + evalPhi 2 P /\
      (forall (Y ya : list BecTok1), RelT0Pow q_abs Y ya ->
        exists W : list BecTok1,
          RelT M1 (P ++ Y) W /\
          RelT0Pow n W (repB dJ ++ (P_next ++ ya)))) \/
    (exists (P_s : list BecTok1) (ct : N),
      evalPhi 2 P = ct * (2 ^ m) /\
      noK1 P_s = true /\
      countBin P_s = m /\
      deltaB P_s = deltaB P /\
      evalPhi 0 P_s = (n + 2) mod (2 ^ m) /\
      (forall (Y yc tyc yq : list BecTok1),
        RelT0Pow ct Y yc -> RelT M1 yc tyc ->
        RelT0Pow ((n + 2) / (2 ^ m) - 2) tyc yq ->
        exists W : list BecTok1,
          RelT M1 (P ++ Y) W /\
          RelT0Pow n W (P_s ++ yq))).
Proof.
  intros m; induction m as [| m' ihm] using N_ind_add1.
  - intros b P n hm; lia.
  - assert (hpow_m : 2 ^ (m' + 1) = 2 * (2 ^ m')) by exact (pow2_succ m').
    pose proof (pow2_pos m') as hm'_pos.
    assert (step_kI : forall (xs : list BecTok1) (n : N),
        countBin (TokI :: xs) = m' + 1 -> noK1 (TokI :: xs) = true ->
        exists (P_next : list BecTok1) (dJ q_abs : N),
          noK1 P_next = true /\
          countBin P_next = (m' + 1) - 1 /\
          deltaB P_next + dJ <= deltaB (TokI :: xs) + 2 ^ ((m' + 1) - 1) /\
          n + 3 <= 2 ^ ((m' + 1) - 1) * (q_abs + 3) /\
          (2 ^ (m' + 1)) * q_abs <= 2 * n + 2 + evalPhi 2 (TokI :: xs) /\
          (forall (Y ya : list BecTok1), RelT0Pow q_abs Y ya ->
            exists W : list BecTok1,
              RelT M1 ((TokI :: xs) ++ Y) W /\
              RelT0Pow n W (repB dJ ++ (P_next ++ ya)))).
    { intros xs n hcb hno.
      cbn [noK1] in hno.
      cbn [countBin] in hcb; assert (hcb_xs : countBin xs = m') by lia; clear hcb.
      replace ((m' + 1) - 1) with m' by lia.
      set (q_abs := (evalPhi 0 xs + (n + 1)) / (2 ^ m')).
      set (P_next := prefixMod (n + 1) xs).
      destruct (prefixMod_props xs hno (n + 1)) as [hno' [hcb' [hdb' [_ [_ _]]]]].
      destruct (div_mod_spec (evalPhi 0 xs + (n + 1)) (2 ^ m') hm'_pos)
        as [qv [rv [hqv [_ [hqr hrv]]]]].
      fold q_abs in hqv; subst qv.
      assert (hw_le_2 : evalPhi 0 xs <= evalPhi 2 xs)
        by (rewrite (evalPhi_eq_zero_add_deltaB 2 xs); lia).
      exists P_next, 1, q_abs.
      refine (conj hno' (conj _ (conj _ (conj _ (conj _ _))))).
      - unfold P_next; rewrite hcb', hcb_xs; reflexivity.
      - unfold P_next; cbn [deltaB]; rewrite hdb'; clear - hm'_pos; lia.
      - clear - hqr hrv; clearbody q_abs; nia.
      - cbn [evalPhi]; rewrite hpow_m; clear - hqr hw_le_2; clearbody q_abs; nia.
      - intros Y ya hya.
        assert (hrel1 : RelT0Pow (n + 1) (xs ++ Y) (P_next ++ ya)).
        { apply (prefixMod_rel xs hno (n + 1)). rewrite hcb_xs; exact hya. }
        destruct (RelT0Pow_succ_inv hrel1) as [u [hs hrem]].
        exists (TokB :: u).
        split; [exact (rt_t1_kI hs) |].
        exact (RelT0Pow_repB 1 hrem). }
    assert (step_k0 : forall (xs : list BecTok1) (n : N),
        countBin (Tok0 :: xs) = m' + 1 -> noK1 (Tok0 :: xs) = true ->
        2 * (2 ^ (m' + 1)) <= n + 2 ->
        (exists (P_next : list BecTok1) (dJ q_abs : N),
          noK1 P_next = true /\
          countBin P_next = (m' + 1) - 1 /\
          deltaB P_next + dJ <= deltaB (Tok0 :: xs) + 2 ^ ((m' + 1) - 1) /\
          n + 3 <= 2 ^ ((m' + 1) - 1) * (q_abs + 3) /\
          (2 ^ (m' + 1)) * q_abs <= 2 * n + 2 + evalPhi 2 (Tok0 :: xs) /\
          (forall (Y ya : list BecTok1), RelT0Pow q_abs Y ya ->
            exists W : list BecTok1,
              RelT M1 ((Tok0 :: xs) ++ Y) W /\
              RelT0Pow n W (repB dJ ++ (P_next ++ ya)))) \/
        (exists (P_s : list BecTok1) (ct : N),
          evalPhi 2 (Tok0 :: xs) = ct * (2 ^ (m' + 1)) /\
          noK1 P_s = true /\
          countBin P_s = m' + 1 /\
          deltaB P_s = deltaB (Tok0 :: xs) /\
          evalPhi 0 P_s = (n + 2) mod (2 ^ (m' + 1)) /\
          (forall (Y yc tyc yq : list BecTok1),
            RelT0Pow ct Y yc -> RelT M1 yc tyc ->
            RelT0Pow ((n + 2) / (2 ^ (m' + 1)) - 2) tyc yq ->
            exists W : list BecTok1,
              RelT M1 ((Tok0 :: xs) ++ Y) W /\
              RelT0Pow n W (P_s ++ yq)))).
    { intros xs n hcb hno hn.
      cbn [noK1] in hno.
      cbn [countBin] in hcb; assert (hcb_xs : countBin xs = m') by lia; clear hcb.
      replace ((m' + 1) - 1) with m' by lia.
      set (b0 := if (n mod 2) =? 0 then Tok0 else TokI).
      assert (hb0_cases : b0 = Tok0 \/ b0 = TokI)
        by (unfold b0; destruct ((n mod 2) =? 0); [left; reflexivity | right; reflexivity]).
      destruct (N.eq_dec m' 0) as [-> | hm'0].
      - (* m' = 0 *)
        pose proof (eq_repB_of_countBin_zero hno hcb_xs) as hxs_eq.
        set (k := deltaB xs) in *.
        set (P_s := b0 :: repB k).
        right; exists P_s, (2 * k).
        change (2 ^ (0 + 1)) with 2 in *.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        + cbn [evalPhi]; rewrite hxs_eq, evalPhi_two_repB; fold k; lia.
        + unfold P_s; destruct hb0_cases as [-> | ->]; exact (noK1_repB k).
        + unfold P_s; destruct hb0_cases as [-> | ->]; cbn [countBin]; rewrite countBin_repB; reflexivity.
        + unfold P_s; destruct hb0_cases as [-> | ->]; cbn [deltaB]; rewrite deltaB_repB; reflexivity.
        + unfold P_s, b0.
          pose proof (evalPhi_zero_repB k) as hw0.
          destruct (mod2_dichotomy n) as [nh [_ [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]]]].
          * rewrite Emod; cbn [N.eqb evalPhi]; rewrite hw0.
            assert (hm2 : (n + 2) mod 2 = 0)
              by (refine (proj2 (@div_mod_unique (n + 2) 2 (nh + 1) 0 _ _)); lia).
            lia.
          * rewrite Emod; cbn [N.eqb evalPhi]; rewrite hw0.
            assert (hm2 : (n + 2) mod 2 = 1)
              by (refine (proj2 (@div_mod_unique (n + 2) 2 (nh + 1) 1 _ _)); lia).
            lia.
        + intros Y yc tyc yq hct ht1 hyq.
          destruct (mod2_dichotomy n) as [nh [hnh_eq hmod]].
          assert (hnh_div : 1 <= nh /\ (n + 2) / 2 - 2 = nh - 1).
          { destruct hmod as [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]].
            - split; [clear - hn hn_eq; lia |].
              assert ((n + 2) / 2 = nh + 1)
                by (refine (proj1 (@div_mod_unique (n + 2) 2 (nh + 1) 0 _ _)); clear - hn_eq; lia).
              lia.
            - split; [clear - hn hn_eq; lia |].
              assert ((n + 2) / 2 = nh + 1)
                by (refine (proj1 (@div_mod_unique (n + 2) 2 (nh + 1) 1 _ _)); clear - hn_eq; lia).
              lia. }
          destruct hnh_div as [hnh1 hdiv_eq].
          rewrite hdiv_eq in hyq.
          assert (ht1_rep : RelT M1 (xs ++ Y) (xs ++ tyc))
            by (rewrite hxs_eq; exact (RelT_t1_repB k hct ht1)).
          assert (hpow_rep : RelT0Pow (nh - 1) (xs ++ tyc) (xs ++ yq))
            by (rewrite hxs_eq; exact (RelT0Pow_repB k hyq)).
          assert (hpow_half : RelT0Pow nh (Tok1 :: (xs ++ Y)) (xs ++ yq))
            by (replace nh with ((nh - 1) + 1) by lia; exact (rt0_succ (rt_t0_k1 ht1_rep) hpow_rep)).
          exists (Tok0 :: Tok1 :: (xs ++ Y)); split; [exact (rt_t1_k0 _) |].
          unfold P_s, b0; rewrite <- hxs_eq.
          destruct hmod as [[Emod [_ hn_eq]] | [Emod [_ hn_eq]]];
            rewrite Emod, hn_eq; cbn [N.eqb app];
            [exact (proj1 (RelT0Pow_bit hpow_half)) | exact (proj1 (proj2 (RelT0Pow_bit hpow_half)))].
      - (* 1 <= m' *)
        assert (hm'1 : 1 <= m') by lia.
        assert (hpow_m' : 2 ^ m' = 2 * (2 ^ (m' - 1)))
          by (replace m' with ((m' - 1) + 1) at 1 by lia; exact (pow2_succ (m' - 1))).
        pose proof (pow2_pos (m' - 1)) as hm'm1_pos.
        destruct (mod2_dichotomy n) as [nh [hnh_eq hmod_both]].
        assert (hmod_info : (n mod 2 = 0 /\ n = 2 * nh) \/ (n mod 2 = 1 /\ n = 2 * nh + 1))
          by (destruct hmod_both as [[e [_ hq]] | [e [_ hq]]]; [left | right]; exact (conj e hq));
        clear hmod_both.
        assert (hnh_ge : 2 <= nh /\ 2 * (2 ^ m') <= (nh - 1) + 2)
          by (clear - hpow_m hpow_m' hm'm1_pos hn hmod_info; lia).
        destruct hnh_ge as [hnh2 hn_sub].
        destruct (ihm (countB xs) xs (nh - 1) hm'1 hcb_xs eq_refl hno hn_sub)
          as [[P_sub [dJ_sub [q_abs [hno_sub [hcb_sub [hdb_sub [hlo_sub [hhi_sub hstep_sub]]]]]]]] |
              [P_sub [ct [hpsi_sub [hno_sub [hcb_sub [hdb_sub [hw_sub hstep_sub]]]]]]]].
        + left; set (P_next := b0 :: (repB dJ_sub ++ P_sub)).
          exists P_next, 0, q_abs.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
          * unfold P_next; destruct hb0_cases as [-> | ->]; cbn [noK1]; rewrite noK1_repB_append; exact hno_sub.
          * unfold P_next; destruct hb0_cases as [-> | ->]; cbn [countBin];
              rewrite countBin_append, countBin_repB, hcb_sub; clear - hm'1; lia.
          * unfold P_next; destruct hb0_cases as [-> | ->]; cbn [deltaB];
              rewrite deltaB_repB_append; clear - hpow_m' hdb_sub; lia.
          * rewrite hpow_m'; replace (2 * 2 ^ (m' - 1) * (q_abs + 3)) with (2 * (2 ^ (m' - 1) * (q_abs + 3))) by ring.
            clear - hnh2 hmod_info hlo_sub; lia.
          * cbn [evalPhi]; rewrite hpow_m; replace (2 * 2 ^ m' * q_abs) with (2 * (2 ^ m' * q_abs)) by ring.
            clear - hnh2 hmod_info hhi_sub; lia.
          * intros Y ya hya.
            destruct (hstep_sub Y ya hya) as [W_sub [ht1_sub hpow_sub]].
            assert (hpow_half : RelT0Pow nh (Tok1 :: (xs ++ Y)) (repB dJ_sub ++ (P_sub ++ ya)))
              by (replace nh with ((nh - 1) + 1) by lia; exact (rt0_succ (rt_t0_k1 ht1_sub) hpow_sub)).
            exists (Tok0 :: Tok1 :: (xs ++ Y)); split; [exact (rt_t1_k0 _) |].
            unfold P_next, b0; cbn [repB app]; rewrite <- app_assoc.
            destruct hmod_info as [[Emod hn_eq] | [Emod hn_eq]]; rewrite Emod, hn_eq; cbn [N.eqb];
              [exact (proj1 (RelT0Pow_bit hpow_half)) | exact (proj1 (proj2 (RelT0Pow_bit hpow_half)))].
        + right; set (P_s := b0 :: P_sub).
          pose (mpow := 2 ^ m'); assert (hM_def : mpow = 2 ^ m') by reflexivity; clearbody mpow.
          assert (hdiv_mod_n2 :
            (n + 2) / (2 * mpow) = (nh + 1) / mpow /\
            (n + 2) mod (2 * mpow) = (n mod 2) + 2 * ((nh + 1) mod mpow)).
          { destruct (div_mod_spec (nh + 1) mpow ltac:(rewrite hM_def; exact hm'_pos))
              as [Q0 [R0 [hQ0 [hR0 [hQR hRlt]]]]].
            rewrite hQ0, hR0.
            refine (@div_mod_unique (n + 2) (2 * mpow) Q0 ((n mod 2) + 2 * R0) _ _);
              [clear - hmod_info hQR; nia | clear - hmod_info hRlt; lia]. }
          exists P_s, ct.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
          * cbn [evalPhi]; rewrite hpsi_sub, hpow_m, <- hM_def; ring.
          * unfold P_s; destruct hb0_cases as [-> | ->]; exact hno_sub.
          * unfold P_s; destruct hb0_cases as [-> | ->]; cbn [countBin]; rewrite hcb_sub; reflexivity.
          * unfold P_s; destruct hb0_cases as [-> | ->]; cbn [deltaB]; rewrite hdb_sub; reflexivity.
          * replace ((nh - 1) + 2) with (nh + 1) in hw_sub by lia.
            rewrite <- hM_def in hw_sub.
            rewrite hpow_m, <- hM_def, (proj2 hdiv_mod_n2).
            unfold P_s, b0.
            destruct hmod_info as [[Emod _] | [Emod _]]; rewrite Emod; cbn [N.eqb evalPhi]; rewrite hw_sub; lia.
          * intros Y yc tyc yq hct ht1 hyq.
            assert (hq_eq : (n + 2) / (2 ^ (m' + 1)) - 2 = ((nh - 1) + 2) / (2 ^ m') - 2).
            { replace ((nh - 1) + 2) with (nh + 1) by lia.
              rewrite hpow_m, <- !hM_def, (proj1 hdiv_mod_n2); reflexivity. }
            rewrite hq_eq in hyq.
            destruct (hstep_sub Y yc tyc yq hct ht1 hyq) as [W_sub [ht1_sub hpow_sub]].
            assert (hpow_half : RelT0Pow nh (Tok1 :: (xs ++ Y)) (P_sub ++ yq))
              by (replace nh with ((nh - 1) + 1) by lia; exact (rt0_succ (rt_t0_k1 ht1_sub) hpow_sub)).
            exists (Tok0 :: Tok1 :: (xs ++ Y)); split; [exact (rt_t1_k0 _) |].
            unfold P_s, b0.
            destruct hmod_info as [[Emod hn_eq] | [Emod hn_eq]]; rewrite Emod, hn_eq; cbn [N.eqb app];
              [exact (proj1 (RelT0Pow_bit hpow_half)) | exact (proj1 (proj2 (RelT0Pow_bit hpow_half)))]. }
    intros b; induction b as [| b' ihb] using N_ind_add1; intros P n hm hcb hb hno hn.
    + destruct P as [| t xs]; [cbn in hcb; lia |].
      destruct t; [exact (step_k0 xs n hcb hno hn) | exact (or_introl (step_kI xs n hcb hno))
        | discriminate hno | cbn [countB] in hb; lia].
    + destruct P as [| t xs]; [cbn in hcb; lia |].
      destruct t; [exact (step_k0 xs n hcb hno hn) | exact (or_introl (step_kI xs n hcb hno))
        | discriminate hno |].
      cbn [noK1 countBin countB] in hno, hcb, hb.
      assert (hb_xs : countB xs = b') by lia; clear hb.
      pose (mpow := 2 ^ (m' + 1)); assert (hM_def : mpow = 2 ^ (m' + 1)) by reflexivity; clearbody mpow.
      assert (hM_pos : 0 < mpow) by (rewrite hM_def; exact (pow2_pos (m' + 1))).
      destruct (div_mod_spec (evalPhi 0 xs + 2) mpow hM_pos) as [cq0 [r0_m [hcq0_def [hr0_def [hdiv2 _]]]]].
      set (xs2 := prefixMod 2 xs).
      destruct (prefixMod_props xs hno 2) as [hno2 [hcb2 [hdb2 [hw2 [_ hcntb2]]]]].
      assert (hpsi_eq : evalPhi 2 (TokB :: xs) = cq0 * mpow + evalPhi 2 xs2).
      { pose proof (evalPhi_eq_zero_add_deltaB 2 xs) as e1.
        pose proof (evalPhi_eq_zero_add_deltaB 2 xs2) as e2.
        unfold xs2 in e2 |- *; rewrite hcb, <- hM_def, hr0_def in hw2.
        cbn [evalPhi]; clear - e1 e2 hdb2 hw2 hdiv2; nia. }
      assert (hcb_xs2 : countBin xs2 = m' + 1) by (unfold xs2; rewrite hcb2; exact hcb).
      assert (hb_xs2 : countB xs2 = b') by (unfold xs2; rewrite hcntb2; exact hb_xs).
      destruct (ihb xs2 n hm hcb_xs2 hb_xs2 hno2 hn)
        as [[P_next [dJ0 [qa0 [hno_n [hcb_n [hdb_n [hlo_n [hhi_n hstep_n]]]]]]]] |
            [P_sub [ct0 [hpsi_s [hno_s [hcb_s [hdb_s [hw_s hstep_s]]]]]]]].
      * left; exists P_next, (dJ0 + 1), (cq0 + qa0).
        refine (conj hno_n (conj hcb_n (conj _ (conj _ (conj _ _))))).
        -- unfold xs2 in hdb_n; rewrite hdb2 in hdb_n; cbn [deltaB]; clear - hdb_n; lia.
        -- pose proof (N.mul_le_mono_l (qa0 + 3) (cq0 + qa0 + 3) (2 ^ (m' + 1 - 1)) ltac:(lia)) as hmul_qa.
           clear - hlo_n hmul_qa; lia.
        -- rewrite <- hM_def in hhi_n |- *.
           replace (mpow * (cq0 + qa0)) with (cq0 * mpow + mpow * qa0) by ring.
           clear - hpsi_eq hhi_n; lia.
        -- intros Y ya hya.
           destruct (RelT0Pow_split_add cq0 qa0 hya) as [yc0 [hcq0 hqa0]].
           assert (hrel2 : RelT0Pow 2 (xs ++ Y) (xs2 ++ yc0)).
           { apply (prefixMod_rel xs hno 2). rewrite hcb, <- hM_def, hcq0_def; exact hcq0. }
           destruct (RelT0Pow_2_inv hrel2) as [u1 [hs1 hs2]].
           destruct (hstep_n yc0 ya hqa0) as [W0 [ht1_0 hpow_0]].
           exists (TokB :: W0); split; [exact (rt_t1_kB hs1 hs2 ht1_0) |].
           rewrite repB_succ; cbn [app].
           exact (RelT0Pow_repB 1 hpow_0).
      * right; exists (TokB :: P_sub), (cq0 + ct0).
        refine (conj _ (conj hno_s (conj _ (conj _ (conj _ _))))).
        -- rewrite hpsi_eq, hpsi_s, <- !hM_def; ring.
        -- cbn [countBin]; exact hcb_s.
        -- cbn [deltaB]; rewrite hdb_s; unfold xs2; rewrite hdb2; reflexivity.
        -- cbn [evalPhi]; rewrite N.add_0_l; exact hw_s.
        -- intros Y yc tyc yq hct ht1 hyq.
           destruct (RelT0Pow_split_add cq0 ct0 hct) as [yc0 [hcq0 hct0]].
           assert (hrel2 : RelT0Pow 2 (xs ++ Y) (xs2 ++ yc0)).
           { apply (prefixMod_rel xs hno 2). rewrite hcb, <- hM_def, hcq0_def; exact hcq0. }
           destruct (RelT0Pow_2_inv hrel2) as [u1 [hs1 hs2]].
           destruct (hstep_s yc0 yc tyc yq hct0 ht1 hyq) as [W0 [ht1_0 hpow_0]].
           exists (TokB :: W0); split; [exact (rt_t1_kB hs1 hs2 ht1_0) |].
           exact (RelT0Pow_repB 1 hpow_0).
Qed.

(* ========================================================================== *)
(* Layer 3b Soundness Part 3a: Child Constructors & Wave Step Soundness       *)
(* ========================================================================== *)

Local Lemma runRange_sound {P : N -> Prop} (body : N -> MemoTree -> bool * MemoTree)
    (hbody : forall i m, fst (body i m) = true -> MemoValid NodeClosed m ->
               MemoValid NodeClosed (snd (body i m)) /\ P i) :
  forall (d : nat) (cur rem : N) (memo : MemoTree),
    fst (runRange d body cur rem memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (runRange d body cur rem memo)) /\
    (forall i : N, cur <= i -> i < cur + rem -> P i).
Proof.
  induction d as [| d' IH]; intros cur rem memo hok hm; cbn [runRange] in hok |- *.
  - destruct (rem =? 0) eqn:Hr0.
    + apply N.eqb_eq in Hr0; subst rem.
      split; [exact hm | intros i h1 h2; lia].
    + destruct (rem =? 1) eqn:Hr1; [| discriminate hok].
      apply N.eqb_eq in Hr1; subst rem.
      destruct (hbody cur memo hok hm) as [hm' hp].
      split; [exact hm' | intros i h1 h2; assert (i = cur) by lia; subst i; exact hp].
  - destruct (rem =? 0) eqn:Hr0.
    + apply N.eqb_eq in Hr0; subst rem.
      split; [exact hm | intros i h1 h2; lia].
    + cbn zeta in hok |- *.
      assert (h_le : N.div2 rem <= rem).
      { destruct (div_mod_spec rem 2 ltac:(lia)) as [q2 [r2 [hq2 [_ [hqr2 hr2]]]]].
        rewrite N.div2_div, hq2; lia. }
      remember (N.div2 rem) as h eqn:Hh.
      destruct (runRange d' body cur h memo) as [ok1 m1] eqn:Hr1.
      destruct ok1; [cbn [negb] in hok |- * | discriminate hok].
      destruct (IH cur h memo ltac:(rewrite Hr1; reflexivity) hm) as [hm1 hp1].
      rewrite Hr1 in hm1; cbn [snd] in hm1.
      destruct (IH (cur + h) (rem - h) m1 hok hm1) as [hm2 hp2].
      split; [exact hm2 | intros i hlo hhi].
      destruct (N.lt_ge_cases i (cur + h)) as [hlt | hge];
        [exact (hp1 i hlo hlt) | exact (hp2 i hge ltac:(lia))].
Qed.

#[local] Arguments runRange : simpl never.

Local Lemma pow2N_0 : pow2N 0 = 1.
Proof. reflexivity. Qed.

Local Lemma pow2N_succ (n : N) : pow2N (n + 1) = 2 * pow2N n.
Proof. rewrite !pow2N_eq, pow2_succ; reflexivity. Qed.

Local Lemma pow2N_pos (n : N) : 1 <= pow2N n.
Proof. rewrite pow2N_eq; pose proof (pow2_pos n); lia. Qed.

Local Lemma msOf_0 : msOf 0 = 64.
Proof. reflexivity. Qed.

Local Lemma leadB_dropB (w : list BecTok1) : leadB (dropB w) = 0.
Proof.
  induction w as [| t xs IH]; [reflexivity |].
  destruct t; try reflexivity; exact IH.
Qed.

Local Lemma notHeadI_append_of_nonempty {P : list BecTok1} (Y : list BecTok1)
    (hne : P <> []) (hnh : notHeadI P = true) :
  notHeadI (P ++ Y) = true.
Proof.
  destruct P as [| t xs]; [contradiction |].
  destruct t; [reflexivity | discriminate hnh | reflexivity | reflexivity].
Qed.

Local Lemma collar_step_raw (k_col : N) {tail u v v' : list BecTok1}
    (hpow : RelT0Pow (2 * k_col) tail u) (ht1 : RelT M1 u v) (ht0 : RelT M0 v v') :
  cfgCollar k_col tail -->+ cfgCollar k_col v'.
Proof.
  pose proof (collar_step k_col hpow ht1 ht0) as h.
  rewrite cfgCollar_norm1 in h; exact h.
Qed.

Local Lemma collar_step_inC1_pow_raw {k_col : N} {M W u2 : list BecTok1}
    (hK : 1 <= k_col) (ht1 : RelT M1 M W) (hpow : RelT0Pow (k_col + 1) W u2) :
  cfgCollar k_col (TokI :: Tok1 :: M) -->+ cfgCollar (k_col + 1) u2.
Proof.
  pose proof (collar_step_inC1_pow hK ht1 hpow) as h.
  rewrite cfgCollar_norm1 in h; exact h.
Qed.

Local Lemma NodeState_withJB {nd : SymWaveNode} {jb' : JBounds} {u_val k0 d0 j_val : N} {P : list BecTok1}
    (hst : NodeState nd u_val k0 d0 j_val P) (hjb' : JBoundsValid jb' u_val j_val) :
  NodeState (withJB nd jb') u_val k0 d0 j_val P.
Proof.
  destruct hst; constructor; cbn [
    withJB nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
    nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
    nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
    assumption.
Qed.

Definition childJB (nd : SymWaveNode) (ms q : N) : JBounds :=
  addJBound (nd_jb nd)
    (Z.of_N (q * ms) - Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd))%Z
    (- (2 * nd_k_hi_c nd + nd_w_hi_c nd + Z.of_N (2 * nd_extra_B nd)))%Z.

Definition mkChild1 (nd : SymWaveNode) (ms ms_next q : N) (y : list BecTok1) : SymWaveNode :=
  mkWaveNode
    (nd_s nd + 1) (nd_db_shift nd + 1) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms_next (-1)%Z
    (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (childJB nd ms q) y (nd_wRQ nd) (nd_pRQ nd).

Definition mkChild2 (nd : SymWaveNode) (ms q : N) (y : list BecTok1) : SymWaveNode :=
  mkWaveNode
    (nd_s nd + 1) (nd_db_shift nd + 1) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z 0 1%Z
    (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (childJB nd ms q) y (nd_wRQ nd) (nd_pRQ nd).

Definition mkChild3 (nd : SymWaveNode) (ms ms_next q : N) (y : list BecTok1) : SymWaveNode :=
  mkWaveNode
    (nd_s nd + 1) (nd_db_shift nd + 1) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms_next (-1)%Z
    (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd + pow2N (nd_db_shift nd + 2))
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (childJB nd ms q) y (nd_wRQ nd) (nd_pRQ nd).

Definition mkChild4 (nd : SymWaveNode) (ms ms_next q : N) (y : list BecTok1) : SymWaveNode :=
  let sh1 := pow2N (nd_s nd + 1) in
  mkWaveNode
    (nd_s nd + 1) (nd_db_shift nd + 1) true
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms_next (-1)%Z
    (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    ((q + 1) * ms) (- Z.of_N (2 * nd_extra_B nd + 2))%Z
    sh1 (64 * (q + 1)) (- Z.of_N (sh1 * (nd_extra_B nd + 1)))%Z
    (childJB nd ms q) y (nd_wRQ nd) (nd_pRQ nd).

Definition ChildClosedAt (nd nx : SymWaveNode) : Prop :=
  forall u_val k0 d0 j_c P_c,
    JBoundsValid (nd_jb nd) u_val j_c ->
    NodeState nx u_val k0 d0 j_c P_c ->
    exists k' tail', nodeCfg nx k0 j_c P_c -->* cfgCollar k' tail' /\
      (InC0 k' tail' \/ InC1 k' tail').

Local Lemma childClosedAt_of_nodeClosed (nd : SymWaveNode) {nx : SymWaveNode}
    (h : NodeClosed nx) : ChildClosedAt nd nx.
Proof.
  intros u_val k0 d0 j_c P_c _ hns; exact (h u_val k0 d0 j_c P_c hns).
Qed.

Definition StopInv (mkC : N -> list BecTok1 -> SymWaveNode) (nd : SymWaveNode) (q_max delta : N)
    (st : option N) : Prop :=
  match st with
  | None => True
  | Some q_stop =>
    forall q : N, q_stop <= q -> q <= q_max ->
      exists y_out : list BecTok1,
        RelT0Pow (q + delta) (nd_Y nd) y_out /\
        noTrailZero y_out = true /\
        ChildClosedAt nd (mkC q y_out)
  end.

Local Lemma mk_stopInv (nxTpl : SymWaveNode) (mkC : N -> list BecTok1 -> SymWaveNode)
    (ms q_max q0 wy0 py0 delta : N) (nd : SymWaveNode) (y0 : list BecTok1)
    (hms_pos : 0 < ms)
    (hms_le : 2 * msOf (nd_s nxTpl) <= ms)
    (htpl_jb : nd_jb nxTpl = nd_jb nd)
    (hfields : forall q y,
      nd_s (mkC q y) = nd_s nxTpl /\ nd_db_shift (mkC q y) = nd_db_shift nxTpl /\
      nd_has_i1_front (mkC q y) = nd_has_i1_front nxTpl /\
      nd_k_lo_u (mkC q y) = nd_k_lo_u nxTpl /\ nd_k_lo_c (mkC q y) = nd_k_lo_c nxTpl /\
      nd_k_hi_u (mkC q y) = nd_k_hi_u nxTpl /\ nd_k_hi_c (mkC q y) = nd_k_hi_c nxTpl /\
      nd_w_hi_u (mkC q y) = nd_w_hi_u nxTpl /\ nd_w_hi_c (mkC q y) = nd_w_hi_c nxTpl /\
      nd_extra_B (mkC q y) = nd_extra_B nxTpl /\
      nd_scaled_db_u (mkC q y) = nd_scaled_db_u nxTpl /\ nd_scaled_db_c (mkC q y) = nd_scaled_db_c nxTpl /\
      nd_pRQ (mkC q y) = nd_pRQ nxTpl /\
      nd_Y (mkC q y) = y /\ nd_jb (mkC q y) = childJB nd ms q)
    (hy0_rel : RelT0Pow q0 (nd_Y nd) y0)
    (hy0_no : noK1 y0 = true)
    (hy0_tz : noTrailZero y0 = true)
    (hy0_I : hasI y0 = true)
    (hwy0 : wy0 = evalPhi 0 y0)
    (hpy0 : py0 = evalPhi 22 y0) :
  StopInv mkC nd q_max delta
    (findChildQStop nxTpl ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
      (nd_extra_B nd) q0 (wy0 + delta) (py0 + delta) q_max).
Proof.
  destruct (findChildQStop nxTpl ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
              (nd_extra_B nd) q0 (wy0 + delta) (py0 + delta) q_max) as [q_stop |] eqn:Hst;
    [| exact I].
  cbn [StopInv]; intros q hge_stop hle_max.
  set (y_out := t0Pow ((q - q0) + delta) y0).
  set (jc := (- (2 * nd_k_hi_c nd + nd_w_hi_c nd + Z.of_N (2 * nd_extra_B nd)))%Z).
  assert (hpy_out : evalPhi 22 y_out <= (py0 + delta) + (q - q0))
    by (unfold y_out; rewrite (evalPhi_t0Pow 22 _ hy0_no), hpy0; lia).
  destruct (findChildQStop_sound nxTpl ms (nd_k_hi_u nd) (nd_k_hi_c nd) (nd_w_hi_u nd) (nd_w_hi_c nd)
              (nd_extra_B nd) q0 (wy0 + delta) (py0 + delta) q_max q_stop q y_out jc
              hms_pos hms_le eq_refl Hst hge_stop hle_max hpy_out)
    as [hq0_le hchk_or].
  assert (hrel_out : RelT0Pow (q + delta) (nd_Y nd) y_out).
  { replace (q + delta) with (q0 + ((q - q0) + delta)) by lia.
    exact (RelT0Pow_trans hy0_rel (RelT0Pow_t0Pow _ hy0_no)). }
  pose proof (noK1_t0Pow ((q - q0) + delta) hy0_no) as hno_out; fold y_out in hno_out.
  pose proof (noTrailZero_t0Pow ((q - q0) + delta) hy0_no hy0_tz) as htz_out; fold y_out in htz_out.
  pose proof (hasI_t0Pow ((q - q0) + delta) hy0_no hy0_I) as hI_out; fold y_out in hI_out.
  assert (hwy_out : evalPhi 0 y_out <= (wy0 + delta) + (q - q0))
    by (unfold y_out; rewrite (evalPhi_t0Pow 0 _ hy0_no), hwy0; lia).
  destruct (hfields q y_out)
    as [fs [fd [ffr [fklu [fklc [fkhu [fkhc [fwhu [fwhc [feb [fsdu [fsdc [fprq [fY fjb]]]]]]]]]]]]]].
  exists y_out; split; [exact hrel_out | split; [exact htz_out |]].
  intros u_val k0 d0 j_c P_c hjb_base hns.
  destruct hchk_or as [hchk1 | hchk2].
  - set (nx0 := withJB (mkC q y_out) (nd_jb nd)).
    assert (hchk1' : checkAbstract nx0 true true ((wy0 + delta) + (q - q0)) (evalPhi 22 y_out) = true).
    { refine (checkAbstract_mono (withY nxTpl y_out) nx0 true true _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ (fun h => h) (N.le_refl _) (N.le_refl _) _ hchk1);
        try exact fs; try exact fd; try exact ffr; try exact fklu; try exact fklc;
        try exact fkhu; try exact fkhc; try exact fwhu; try exact fwhc; try exact feb;
        try exact fsdu; try exact fsdc; try exact fprq.
      cbn [withY withJB nd_jb]; rewrite htpl_jb; exact (JBoundsLe_refl _). }
    pose proof (NodeState_withJB hns hjb_base) as hns0; fold nx0 in hns0.
    assert (hno0 : noK1 (nd_Y nx0) = true) by (unfold nx0, withJB; cbn [nd_Y]; rewrite fY; exact hno_out).
    assert (hI0 : hasI (nd_Y nx0) = true) by (unfold nx0, withJB; cbn [nd_Y]; rewrite fY; exact hI_out).
    assert (hwy0' : evalPhi 0 (nd_Y nx0) <= (wy0 + delta) + (q - q0))
      by (unfold nx0, withJB; cbn [nd_Y]; rewrite fY; exact hwy_out).
    assert (hpy0' : evalPhi 22 (nd_Y nx0) <= evalPhi 22 y_out)
      by (unfold nx0, withJB; cbn [nd_Y]; rewrite fY; lia).
    assert (hcfg0 : nodeCfg nx0 k0 j_c P_c = nodeCfg (mkC q y_out) k0 j_c P_c) by reflexivity.
    rewrite <- hcfg0.
    exact (checkAbstract_sound hns0 hno0 (fun _ => hI0) hwy0' hpy0' hchk1').
  - assert (hchk2' : checkAbstract (mkC q y_out) true true ((wy0 + delta) + (q - q0)) (evalPhi 22 y_out) = true).
    { refine (checkAbstract_mono
        (withJB (withY nxTpl y_out)
          (addJBound (nd_jb nxTpl) (Z.of_N (q * ms) - Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd))%Z jc))
        (mkC q y_out) true true _ _ _ _
        fs fd ffr fklu fklc fkhu fkhc fwhu fwhc feb fsdu fsdc fprq
        (fun h => h) (N.le_refl _) (N.le_refl _) _ hchk2).
      cbn [withJB withY nd_jb]; rewrite fjb, htpl_jb; exact (JBoundsLe_refl _). }
    assert (hno2 : noK1 (nd_Y (mkC q y_out)) = true) by (rewrite fY; exact hno_out).
    assert (hI2 : hasI (nd_Y (mkC q y_out)) = true) by (rewrite fY; exact hI_out).
    assert (hwy2 : evalPhi 0 (nd_Y (mkC q y_out)) <= (wy0 + delta) + (q - q0)) by (rewrite fY; exact hwy_out).
    assert (hpy2 : evalPhi 22 (nd_Y (mkC q y_out)) <= evalPhi 22 y_out) by (rewrite fY; lia).
    exact (checkAbstract_sound hns hno2 (fun _ => hI2) hwy2 hpy2 hchk2').
Qed.

Local Lemma runBeforeStop_false_iff {q : N} {st : option N} :
  runBeforeStop q st = false <-> exists q_stop, st = Some q_stop /\ q_stop <= q.
Proof.
  destruct st as [q_stop |]; cbn [runBeforeStop].
  - rewrite N.ltb_ge. split;
      [intros h; exists q_stop; exact (conj eq_refl h) | intros [qs [heq hle]]; injection heq as <-; exact hle].
  - split; [intros h; discriminate h | intros [qs [heq _]]; discriminate heq].
Qed.

Local Lemma loopQ_step_children
    (nd : SymWaveNode) (ms ms_next q : N)
    (hs4 : nd_s nd <= 4) (hfr : nd_has_i1_front nd = false)
    (hms : ms = msOf (nd_s nd)) (hmsn : ms_next = msOf (nd_s nd + 1))
    (hc1 : exists y1, RelT0Pow q (nd_Y nd) y1 /\ noTrailZero y1 = true /\
      ChildClosedAt nd (mkChild1 nd ms ms_next q y1))
    (hc2 : exists y2, RelT0Pow (q + 1) (nd_Y nd) y2 /\ noTrailZero y2 = true /\
      ChildClosedAt nd (mkChild2 nd ms q y2))
    (hc3 : exists y3, RelT0Pow q (nd_Y nd) y3 /\ noTrailZero y3 = true /\
      ChildClosedAt nd (mkChild3 nd ms ms_next q y3))
    (hc4 : exists y4, RelT0Pow q (nd_Y nd) y4 /\ noTrailZero y4 = true /\
      ChildClosedAt nd (mkChild4 nd ms ms_next q y4))
    {u_val k0 d0 j_val : N} {P : list BecTok1}
    (hst : NodeState nd u_val k0 d0 j_val P)
    (hq_eq : (evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val)) / (ms * u_val) = q) :
  exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
    (InC0 k' tail' \/ InC1 k' tail').
Proof.
  destruct hst as [hU hK64 hs6 hdbs hnoP hpowP hleadP hnhP htzY hklo hkhi hwlo hwhi hjb hdb hd1 hd2 hwM_lo hD_lo hkj hwj].
  assert (hms_pos : 0 < ms) by (rewrite hms; apply msOf_pos; lia).
  assert (hmsn_pos : 0 < ms_next) by (rewrite hmsn; apply msOf_pos; lia).
  assert (hms_dbl : 2 * ms_next = ms) by (rewrite hms, hmsn; apply msOf_succ; lia).
  assert (hms_pow : ms * (2 ^ nd_s nd) = 64) by (rewrite hms; (apply msOf_mul_pow2; lia)).
  assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
  set (K_col := k0 + nd_extra_B nd + j_val).
  destruct (div_mod_spec (evalPhi 0 P + 2 * K_col) (ms * u_val) hmsU_pos)
    as [qv [rK [hqv [hrK [hdiv_K hmod_K]]]]].
  unfold K_col in hqv; rewrite hq_eq in hqv; subst qv.
  assert (hjb' : JBoundsValid (childJB nd ms q) u_val j_val).
  { unfold childJB; apply (addJBound_sound hjb).
    assert (hring_jb :
      ((Z.of_N (q * ms) - Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd)) * Z.of_N u_val +
       (- (2 * nd_k_hi_c nd + nd_w_hi_c nd + Z.of_N (2 * nd_extra_B nd))) =
       Z.of_N ((ms * u_val) * q) -
       2 * (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd) -
       (Z.of_N (nd_w_hi_u nd * u_val) + nd_w_hi_c nd) -
       Z.of_N (2 * nd_extra_B nd))%Z)
      by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
    unfold K_col in hdiv_K; clear - hdiv_K hkhi hwhi hring_jb; lia. }
  set (P' := prefixMod (2 * K_col) P).
  destruct (prefixMod_props P hnoP (2 * K_col)) as [hnoP' [hcbP' [hdbP' [hwP' [hlbP' _]]]]].
  fold P' in hnoP', hcbP', hdbP', hwP', hlbP'.
  assert (hpowP_ms : 2 ^ countBin P = ms * u_val) by (rewrite hpowP, hms; reflexivity).
  assert (hm2 : 2 <= ms_next).
  { rewrite hmsn.
    assert (nd_s nd = 0 \/ nd_s nd = 1 \/ nd_s nd = 2 \/ nd_s nd = 3 \/ nd_s nd = 4)
      as [-> | [-> | [-> | [-> | ->]]]] by lia; cbn; lia. }
  assert (hmsnU_ge2 : 2 <= ms_next * u_val) by (clear - hm2 hU; nia).
  assert (hcb_ge2 : 2 <= countBin P').
  { rewrite hcbP'.
    assert (h4 : 4 <= 2 ^ countBin P) by (rewrite hpowP_ms, <- hms_dbl; clear - hmsnU_ge2; lia).
    destruct (N.lt_ge_cases (countBin P) 2) as [hlt2 | hge2]; [| exact hge2].
    assert (countBin P = 0 \/ countBin P = 1) as [hc0 | hc1'] by lia;
      rewrite hc0 in h4 || rewrite hc1' in h4; cbn in h4; lia. }
  assert (hlb0 : leadB P' = 0) by (rewrite hlbP', (hleadP hfr); reflexivity).
  unfold nodeCfg; rewrite hfr; fold K_col.
  destruct P' as [| t0 R_P] eqn:HP'; [cbn in hcb_ge2; lia |].
  destruct t0; [| | discriminate hnoP' | cbn [leadB] in hlb0; lia].
  - (* t0 = Tok0: Child 3 or Child 4 *)
    cbn [noK1] in hnoP'; cbn [countBin] in hcbP', hcb_ge2.
    assert (hpowR : 2 ^ countBin R_P = ms_next * u_val).
    { rewrite <- hcbP', pow2_succ, <- hms_dbl in hpowP_ms; clear - hpowP_ms; lia. }
    assert (hwR_lt : evalPhi 0 R_P < ms_next * u_val)
      by (rewrite <- hpowR; exact (evalPhi_zero_lt_pow_countBin R_P)).
    assert (hRP_ne : R_P <> [])
      by (intros hemp; subst R_P; cbn in hcb_ge2; lia).
    destruct (notHeadI R_P) eqn:HnhR.
    + (* Child 4: notHeadI R_P = true *)
      destruct hc4 as [y4 [hy4_rel [hy4_tz hcl4]]].
      assert (h2k_rel : RelT0Pow (2 * K_col) (P ++ nd_Y nd) ((Tok0 :: R_P) ++ y4)).
      { rewrite <- HP'; apply (prefixMod_rel P hnoP (2 * K_col)).
        unfold K_col; rewrite hpowP_ms, hq_eq; exact hy4_rel. }
      clear HP' P' hq_eq.
      pose proof (collar_step_raw K_col h2k_rel (rt_t1_k0 _) (rt_t0_k0 _)) as hstep1.
      cbn [app] in hstep1.
      change (cfgCollar K_col (TokI :: Tok1 :: R_P ++ y4))
        with (nodeCfg (mkChild4 nd ms ms_next q y4) k0 j_val R_P) in hstep1.
      assert (hns4 : NodeState (mkChild4 nd ms ms_next q y4) u_val k0 d0 j_val R_P).
      { unfold mkChild4; cbn zeta; constructor; cbn [
          nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h); try lia.
        - intros _; exact (notHeadI_append_of_nonempty y4 hRP_ne HnhR).
        - cbn [deltaB] in hdbP'.
          assert (hlin : pow2N (nd_db_shift nd + 1) * deltaB R_P = pow2N (nd_db_shift nd) * deltaB P)
            by (rewrite <- hdbP', pow2N_succ; ring).
          clear - hdb hlin; lia.
        - intros hseq.
          pose proof (hD_lo ltac:(lia)) as hd0.
          cbn [deltaB] in hdbP'.
          assert (hlin : pow2N (nd_s nd + 1) * (deltaB R_P + j_val) =
                         pow2N (nd_s nd) * (deltaB P + j_val) + pow2N (nd_s nd) * j_val)
            by (rewrite <- hdbP', pow2N_succ; ring).
          clear - hd0 hlin; lia.
        - intros _ hseq.
          pose proof (hD_lo ltac:(lia)) as hd0.
          cbn [deltaB] in hdbP'; cbn [evalPhi] in hwP'; rewrite hpowP_ms, hrK in hwP'.
          remember (pow2N (nd_s nd)) as sh0 eqn:Hsh0.
          assert (hp1 : pow2N (nd_s nd + 1) = 2 * sh0) by (rewrite pow2N_succ, <- Hsh0; reflexivity).
          assert (hp2 : pow2N (nd_s nd + 1 + 1) = 4 * sh0) by (rewrite pow2N_succ, hp1; ring).
          assert (hp3 : pow2N (nd_s nd + 1 + 2) = 8 * sh0)
            by (replace (nd_s nd + 1 + 2) with ((nd_s nd + 1 + 1) + 1) by lia; rewrite pow2N_succ, hp2; ring).
          rewrite hp1, hp2, hp3.
          assert (h4d : 4 * d0 <= 8 * sh0 * deltaB R_P + 4 * sh0 * j_val).
          { pose proof (N.mul_le_mono_l _ _ 4 hd0) as hm4.
            rewrite <- hdbP' in hm4; replace (4 * (sh0 * (2 * deltaB R_P + j_val)))
              with (8 * sh0 * deltaB R_P + 4 * sh0 * j_val) in hm4 by ring; exact hm4. }
          assert (h2k : 2 * K_col <= (ms * u_val) * q + 2 * evalPhi 0 R_P)
            by (clear - hdiv_K hwP'; lia).
          assert (hms_sh0 : ms * sh0 = 64) by (rewrite Hsh0, pow2N_eq; exact hms_pow).
          assert (hmul_sh : 4 * sh0 * K_col <= 128 * q * u_val + 4 * sh0 * evalPhi 0 R_P).
          { pose proof (N.mul_le_mono_l _ _ (2 * sh0) h2k) as hm2s.
            replace ((2 * sh0) * (2 * K_col)) with (4 * sh0 * K_col) in hm2s by ring.
            replace ((2 * sh0) * ((ms * u_val) * q + 2 * evalPhi 0 R_P))
              with (2 * (ms * sh0) * q * u_val + 4 * sh0 * evalPhi 0 R_P) in hm2s by ring.
            rewrite hms_sh0 in hm2s; exact hm2s. }
          assert (hsh0_16 : sh0 <= 16).
          { rewrite Hsh0, pow2N_eq.
            assert (nd_s nd = 0 \/ nd_s nd = 1 \/ nd_s nd = 2 \/ nd_s nd = 3 \/ nd_s nd = 4)
              as [e | [e | [e | [e | e]]]] by lia; rewrite e; cbn; lia. }
          assert (h4sh_u : 4 * sh0 <= 128 * u_val) by (clear - hsh0_16 hU; lia).
          assert (hring4 :
            (Z.of_N (8 * sh0 * deltaB R_P) + Z.of_N (2 * (64 * (q + 1)) * u_val) +
             2 * (- Z.of_N ((2 * sh0) * (nd_extra_B nd + 1))) - Z.of_N (2 * (2 * sh0) * k0) =
             (Z.of_N (8 * sh0 * deltaB R_P + 4 * sh0 * j_val)) +
             (Z.of_N (128 * q * u_val) - Z.of_N (4 * sh0 * K_col)) +
             (Z.of_N (128 * u_val) - Z.of_N (4 * sh0)))%Z)
            by (unfold K_col; repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
          clear - h4d hmul_sh h4sh_u hwR_lt hring4; lia. }
      destruct (hcl4 u_val k0 d0 j_val R_P hjb hns4) as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep1) hstar) hinv).
    + (* Child 3: notHeadI R_P = false, so R_P = TokI :: R_tail *)
      destruct R_P as [| rt R_tail]; [contradiction |].
      destruct rt; try discriminate HnhR.
      destruct hc3 as [y3 [hy3_rel [hy3_tz hcl3]]].
      assert (h2k_rel : RelT0Pow (2 * K_col) (P ++ nd_Y nd) ((Tok0 :: TokI :: R_tail) ++ y3)).
      { rewrite <- HP'; apply (prefixMod_rel P hnoP (2 * K_col)).
        unfold K_col; rewrite hpowP_ms, hq_eq; exact hy3_rel. }
      clear HP' P' hq_eq.
      cbn [app] in h2k_rel.
      pose proof (collar_step_raw K_col h2k_rel (rt_t1_k0 _) (rt_t0_k0 _)) as hstep1.
      set (P_c := TokI :: TokB :: R_tail).
      assert (hcfg_eq : cfgCollar K_col (TokI :: Tok1 :: TokI :: R_tail ++ y3) =
                        nodeCfg (mkChild3 nd ms ms_next q y3) k0 j_val P_c).
      { unfold nodeCfg, mkChild3, P_c, cfgCollar, evalBecCfg, K_col.
        cbn [nd_extra_B nd_has_i1_front nd_Y app decode1].
        rewrite !decode1_append; cbn [decode1 app]; reflexivity. }
      rewrite hcfg_eq in hstep1.
      assert (hns3 : NodeState (mkChild3 nd ms ms_next q y3) u_val k0 d0 j_val P_c).
      { constructor; cbn [
          mkChild3 nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
        - unfold P_c; cbn [countBin] in hpowR |- *; rewrite hpowR, hmsn; reflexivity.
        - intros _; reflexivity.
        - unfold P_c; cbn [evalPhi] in hwR_lt |- *; lia.
        - cbn [deltaB] in hdbP'.
          assert (hlin : pow2N (nd_db_shift nd + 1) * deltaB P_c =
                         pow2N (nd_db_shift nd) * deltaB P + pow2N (nd_db_shift nd + 2)).
          { unfold P_c; cbn [deltaB].
            replace (nd_db_shift nd + 2) with ((nd_db_shift nd + 1) + 1) by lia.
            rewrite !pow2N_succ, <- hdbP'; ring. }
          clear - hdb hlin; lia.
        - intros hseq.
          pose proof (hD_lo ltac:(lia)) as hd0.
          cbn [deltaB] in hdbP'.
          assert (hlin : pow2N (nd_s nd + 1) * (deltaB P_c + j_val) =
                         pow2N (nd_s nd) * (deltaB P + j_val) + pow2N (nd_s nd) * (4 + j_val)).
          { unfold P_c; cbn [deltaB]; rewrite pow2N_succ, <- hdbP'; ring. }
          clear - hd0 hlin; lia. }
      destruct (hcl3 u_val k0 d0 j_val P_c hjb hns3) as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep1) hstar) hinv).
  - (* t0 = TokI: Child 1 or Child 2 *)
    cbn [noK1] in hnoP'; cbn [countBin] in hcbP'.
    assert (hpowR : 2 ^ countBin R_P = ms_next * u_val).
    { rewrite <- hcbP', pow2_succ, <- hms_dbl in hpowP_ms; clear - hpowP_ms; lia. }
    assert (hwR_lt : evalPhi 0 R_P < ms_next * u_val)
      by (rewrite <- hpowR; exact (evalPhi_zero_lt_pow_countBin R_P)).
    set (R_P2 := prefixMod 2 R_P).
    destruct (prefixMod_props R_P hnoP' 2) as [hnoR2 [hcbR2 [hdbR2 [hwR2 [_ _]]]]].
    fold R_P2 in hnoR2, hcbR2, hdbR2, hwR2.
    rewrite hpowR in hwR2.
    set (J_c := j_val + leadB R_P2).
    set (P_c := dropB R_P2).
    assert (hdb_R : deltaB P = 2 * (leadB R_P2 + deltaB P_c)).
    { unfold P_c; cbn [deltaB] in hdbP'; pose proof (deltaB_leadB_dropB R_P2); lia. }
    assert (hdb_c : pow2N (nd_db_shift nd + 1) * deltaB P_c + J_c <=
                    d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd).
    { pose proof (N.mul_le_mono_r _ _ (leadB R_P2) (pow2N_pos (nd_db_shift nd))) as hle_lb.
      assert (hlin : pow2N (nd_db_shift nd + 1) * deltaB P_c + 2 * (pow2N (nd_db_shift nd) * leadB R_P2) =
                     pow2N (nd_db_shift nd) * deltaB P)
        by (rewrite pow2N_succ, hdb_R; ring).
      unfold J_c; clear - hdb hle_lb hlin; lia. }
    assert (hDlo_c : nd_s nd + 1 = nd_db_shift nd + 1 ->
                     d0 <= pow2N (nd_s nd + 1) * (deltaB P_c + J_c)).
    { intros hseq.
      pose proof (hD_lo ltac:(lia)) as hd0.
      assert (hlin : pow2N (nd_s nd + 1) * (deltaB P_c + J_c) =
                     pow2N (nd_s nd) * (deltaB P + j_val) + pow2N (nd_s nd) * j_val)
        by (unfold J_c; rewrite pow2N_succ, hdb_R; ring).
      clear - hd0 hlin; lia. }
    destruct (N.lt_ge_cases (evalPhi 0 R_P + 2) (ms_next * u_val)) as [hlt_c | hge_c].
    + (* Child 1 *)
      destruct hc1 as [y1 [hy1_rel [hy1_tz hcl1]]].
      assert (h2k_rel : RelT0Pow (2 * K_col) (P ++ nd_Y nd) ((TokI :: R_P) ++ y1)).
      { rewrite <- HP'; apply (prefixMod_rel P hnoP (2 * K_col)).
        unfold K_col; rewrite hpowP_ms, hq_eq; exact hy1_rel. }
      assert (hc0_div : (evalPhi 0 R_P + 2) / (2 ^ countBin R_P) = 0)
        by (rewrite hpowR; exact (N.div_small _ _ hlt_c)).
      assert (hr2_rel : RelT0Pow 2 (R_P ++ y1) (R_P2 ++ y1)).
      { unfold R_P2; apply (prefixMod_rel R_P hnoP' 2); rewrite hc0_div; exact (rt0_zero y1). }
      clear HP' P' hq_eq; clearbody R_P2.
      destruct (RelT0Pow_2_inv hr2_rel) as [u1 [hs1 hs2]].
      pose proof (collar_step_raw K_col h2k_rel (rt_t1_kI hs1) (rt_t0_kB hs2)) as hstep1.
      assert (hcfg_eq : cfgCollar K_col (TokB :: (R_P2 ++ y1)) =
                        nodeCfg (mkChild1 nd ms ms_next q y1) k0 J_c P_c).
      { unfold nodeCfg, mkChild1; cbn [nd_extra_B nd_has_i1_front nd_Y].
        assert (hrw : TokB :: (R_P2 ++ y1) = repB (leadB R_P2 + 1) ++ (P_c ++ y1))
          by (unfold P_c; rewrite repB_succ; cbn [app]; rewrite app_assoc, rep_leadB_dropB; reflexivity).
        rewrite hrw, cfgCollar_repB; f_equal; unfold K_col, J_c; lia. }
      rewrite hcfg_eq in hstep1.
      assert (hns1 : NodeState (mkChild1 nd ms ms_next q y1) u_val k0 d0 J_c P_c).
      { constructor; cbn [
          mkChild1 nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
        - exact (noK1_dropB hnoR2).
        - unfold P_c; rewrite countBin_dropB, hcbR2, hpowR, hmsn; reflexivity.
        - intros _; exact (leadB_dropB R_P2).
        - pose proof (evalPhi_leadB_dropB 0 R_P2) as hd.
          pose proof (N.mod_lt (evalPhi 0 R_P + 2) (ms_next * u_val) ltac:(lia)) as hm_lt.
          unfold P_c; clear - hd hwR2 hm_lt; lia.
        - exact (@JBoundsValid_mono_J _ _ _ J_c hjb' ltac:(unfold J_c; lia)). }
      destruct (hcl1 u_val k0 d0 J_c P_c (@JBoundsValid_mono_J _ _ _ J_c hjb ltac:(unfold J_c; lia)) hns1)
        as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep1) hstar) hinv).
    + (* Child 2 *)
      destruct hc2 as [y2 [hy2_rel [hy2_tz hcl2]]].
      destruct (RelT0Pow_split_add q 1 hy2_rel) as [yq0 [hyq0 hy1_step]].
      assert (h2k_rel : RelT0Pow (2 * K_col) (P ++ nd_Y nd) ((TokI :: R_P) ++ yq0)).
      { rewrite <- HP'; apply (prefixMod_rel P hnoP (2 * K_col)).
        unfold K_col; rewrite hpowP_ms, hq_eq; exact hyq0. }
      assert (hdm_c : (evalPhi 0 R_P + 2) / (ms_next * u_val) = 1 /\
                      (evalPhi 0 R_P + 2) mod (ms_next * u_val) = evalPhi 0 R_P + 2 - ms_next * u_val).
      { refine (@div_mod_unique (evalPhi 0 R_P + 2) (ms_next * u_val) 1
                  (evalPhi 0 R_P + 2 - ms_next * u_val) _ _);
          clear - hwR_lt hge_c hmsnU_ge2; lia. }
      assert (hr2_rel : RelT0Pow 2 (R_P ++ yq0) (R_P2 ++ y2)).
      { unfold R_P2; apply (prefixMod_rel R_P hnoP' 2); rewrite hpowR, (proj1 hdm_c); exact hy1_step. }
      clear HP' P' hq_eq; clearbody R_P2.
      destruct (RelT0Pow_2_inv hr2_rel) as [u1 [hs1 hs2]].
      pose proof (collar_step_raw K_col h2k_rel (rt_t1_kI hs1) (rt_t0_kB hs2)) as hstep1.
      assert (hcfg_eq : cfgCollar K_col (TokB :: (R_P2 ++ y2)) =
                        nodeCfg (mkChild2 nd ms q y2) k0 J_c P_c).
      { unfold nodeCfg, mkChild2; cbn [nd_extra_B nd_has_i1_front nd_Y].
        assert (hrw : TokB :: (R_P2 ++ y2) = repB (leadB R_P2 + 1) ++ (P_c ++ y2))
          by (unfold P_c; rewrite repB_succ; cbn [app]; rewrite app_assoc, rep_leadB_dropB; reflexivity).
        rewrite hrw, cfgCollar_repB; f_equal; unfold K_col, J_c; lia. }
      rewrite hcfg_eq in hstep1.
      assert (hns2 : NodeState (mkChild2 nd ms q y2) u_val k0 d0 J_c P_c).
      { constructor; cbn [
          mkChild2 nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
        - exact (noK1_dropB hnoR2).
        - unfold P_c; rewrite countBin_dropB, hcbR2, hpowR, hmsn; reflexivity.
        - intros _; exact (leadB_dropB R_P2).
        - pose proof (evalPhi_leadB_dropB 0 R_P2) as hd.
          rewrite (proj2 hdm_c) in hwR2.
          unfold P_c; clear - hd hwR2 hwR_lt hge_c; lia.
        - exact (@JBoundsValid_mono_J _ _ _ J_c hjb' ltac:(unfold J_c; lia)). }
      destruct (hcl2 u_val k0 d0 J_c P_c (@JBoundsValid_mono_J _ _ _ J_c hjb ltac:(unfold J_c; lia)) hns2)
        as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep1) hstar) hinv).
Qed.

Local Lemma stopInv_zero_at {mkC : N -> list BecTok1 -> SymWaveNode} {nd : SymWaveNode}
    {q_max qs q : N} (h : StopInv mkC nd q_max 0 (Some qs)) (hge : qs <= q) (hqm : q <= q_max) :
  exists y_out, RelT0Pow q (nd_Y nd) y_out /\ noTrailZero y_out = true /\ ChildClosedAt nd (mkC q y_out).
Proof.
  destruct (h q hge hqm) as [y_out [hr rest]]; rewrite N.add_0_r in hr; exists y_out; exact (conj hr rest).
Qed.

Local Lemma stepQBody_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms ms_next q_max : N)
    (st1 st2 st3 st4 : option N)
    (hs4 : nd_s nd <= 4) (hfr : nd_has_i1_front nd = false)
    (htz : noTrailZero (nd_Y nd) = true)
    (hms : ms = msOf (nd_s nd)) (hmsn : ms_next = msOf (nd_s nd + 1))
    (hst1 : StopInv (mkChild1 nd ms ms_next) nd q_max 0 st1)
    (hst2 : StopInv (mkChild2 nd ms) nd q_max 1 st2)
    (hst3 : StopInv (mkChild3 nd ms ms_next) nd q_max 0 st3)
    (hst4 : StopInv (mkChild4 nd ms ms_next) nd q_max 0 st4) :
  forall (q : N) (memo : MemoTree),
    fst (stepQBody stepFn nd ms ms_next st1 st2 st3 st4 q memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (stepQBody stepFn nd ms ms_next st1 st2 st3 st4 q memo)) /\
    (q <= q_max ->
      forall u_val k0 d0 j_val P, NodeState nd u_val k0 d0 j_val P ->
        (evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val)) / (ms * u_val) = q ->
        exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
          (InC0 k' tail' \/ InC1 k' tail')).
Proof.
  intros q memo hok hm.
  unfold stepQBody in hok |- *.
  set (b1 := runBeforeStop q st1) in *.
  set (b2 := runBeforeStop q st2) in *.
  set (b3 := runBeforeStop q st3) in *.
  set (b4 := runBeforeStop q st4) in *.
  destruct (negb (b1 || b2 || b3 || b4)) eqn:Hall.
  - cbn [snd]; split; [exact hm | intros hqm u_val k0 d0 j_val P hst hq_eq].
    apply Bool.negb_true_iff in Hall.
    repeat rewrite Bool.orb_false_iff in Hall.
    destruct Hall as [[[hb1 hb2] hb3] hb4].
    destruct (proj1 runBeforeStop_false_iff hb1) as [qs1 [heq1 hge1]]; rewrite heq1 in hst1.
    destruct (proj1 runBeforeStop_false_iff hb2) as [qs2 [heq2 hge2]]; rewrite heq2 in hst2.
    destruct (proj1 runBeforeStop_false_iff hb3) as [qs3 [heq3 hge3]]; rewrite heq3 in hst3.
    destruct (proj1 runBeforeStop_false_iff hb4) as [qs4 [heq4 hge4]]; rewrite heq4 in hst4.
    exact (loopQ_step_children nd ms ms_next q hs4 hfr hms hmsn
      (stopInv_zero_at hst1 hge1 hqm) (hst2 q hge2 hqm)
      (stopInv_zero_at hst3 hge3 hqm) (stopInv_zero_at hst4 hge4 hqm) hst hq_eq).
  - destruct (holdsWithJBounds 64 (-2)%Z (Z.of_N ((q + 1) * ms) - Z.of_N (nd_w_lo_u nd))%Z
                (- Z.of_N (2 * nd_extra_B nd) - nd_w_lo_c nd)%Z 1 (nd_jb nd)
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) eqn:Hpr.
    + cbn [snd]; split; [exact hm | intros _ u_val k0 d0 j_val P hst hq_eq].
      pose proof (holdsWithJBounds_sound (nst_jb _ _ _ _ _ _ hst) (nst_U _ _ _ _ _ _ hst)
                    (nst_K64 _ _ _ _ _ _ hst) (nst_klo _ _ _ _ _ _ hst) (nst_khi _ _ _ _ _ _ hst) Hpr) as hp.
      pose proof (nst_wlo _ _ _ _ _ _ hst) as hwlo.
      assert (hms_pos : 0 < ms) by (rewrite hms; apply msOf_pos; lia).
      pose proof (nst_U _ _ _ _ _ _ hst) as hU.
      assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
      destruct (div_mod_spec (evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val)) (ms * u_val) hmsU_pos)
        as [qv [rv [hqv [_ [hdiv hmod]]]]].
      rewrite hq_eq in hqv; subst qv.
      assert (hlt_q : evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val) + 1 <= ((q + 1) * ms) * u_val)
        by (replace (((q + 1) * ms) * u_val) with ((ms * u_val) * q + ms * u_val) by ring; clear - hdiv hmod; lia).
      assert (hring_pr :
        ((-2) * Z.of_N k0 + (Z.of_N ((q + 1) * ms) - Z.of_N (nd_w_lo_u nd)) * Z.of_N u_val +
         (- Z.of_N (2 * nd_extra_B nd) - nd_w_lo_c nd) - Z.of_N (1 * (2 * j_val)) =
         Z.of_N (((q + 1) * ms) * u_val) -
         (Z.of_N (nd_w_lo_u nd * u_val) + nd_w_lo_c nd) -
         Z.of_N (2 * (k0 + nd_extra_B nd + j_val)))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      exfalso; clear - hp hwlo hlt_q hring_pr; lia.
    + destruct (t0PowNorm wordFuel q (nd_Y nd)) as [yp |] eqn:Hyp; [| discriminate hok].
      cbn zeta in hok |- *.
      pose proof (t0PowNorm_sound Hyp) as hyp_rel.
      pose proof (t0PowNorm_noTrailZero htz Hyp) as hyp_tz.
      (* Child 1 *)
      fold (childJB nd ms q) in hok |- *.
      fold (mkChild1 nd ms ms_next q yp) in hok |- *.
      set (p1 := if b1 then stepFn (mkChild1 nd ms ms_next q yp) memo else (true, memo)) in *.
      assert (hp1_spec : fst p1 = true ->
        MemoValid NodeClosed (snd p1) /\
        (q <= q_max -> exists y1, RelT0Pow q (nd_Y nd) y1 /\ noTrailZero y1 = true /\
          ChildClosedAt nd (mkChild1 nd ms ms_next q y1))).
      { intros hp1_ok; unfold p1 in hp1_ok |- *.
        destruct b1 eqn:Hb1.
        - destruct (hstep _ memo hp1_ok hm) as [hcl1 hm1].
          exact (conj hm1 (fun _ => ex_intro _ yp (conj hyp_rel (conj hyp_tz (childClosedAt_of_nodeClosed nd hcl1))))).
        - destruct (proj1 runBeforeStop_false_iff Hb1) as [qs1 [heq1 hge1]]; rewrite heq1 in hst1.
          exact (conj hm (fun hqm => stopInv_zero_at hst1 hge1 hqm)). }
      destruct p1 as [ok1 m1]; destruct ok1; [cbn [negb] in hok |- * | discriminate hok].
      destruct (hp1_spec eq_refl) as [hm1 hc1]; cbn [snd] in hm1.
      (* Child 2 *)
      change (match t0PowNorm wordFuel 1 yp with
              | Some yp1 =>
                stepFn (mkWaveNode
                  (nd_s nd + 1) (nd_db_shift nd + 1) false
                  (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
                  0 0%Z 0 1%Z
                  (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
                  (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
                  (childJB nd ms q) yp1 (nd_wRQ nd) (nd_pRQ nd)) m1
              | None => (false, m1)
              end)
        with (match t0PowNorm wordFuel 1 yp with
              | Some yp1 => stepFn (mkChild2 nd ms q yp1) m1
              | None => (false, m1)
              end) in hok |- *.
      set (p2 := if b2 then
                   match t0PowNorm wordFuel 1 yp with
                   | None => (false, m1)
                   | Some yp1 => stepFn (mkChild2 nd ms q yp1) m1
                   end
                 else (true, m1)) in *.
      assert (hp2_spec : fst p2 = true ->
        MemoValid NodeClosed (snd p2) /\
        (q <= q_max -> exists y2, RelT0Pow (q + 1) (nd_Y nd) y2 /\ noTrailZero y2 = true /\
          ChildClosedAt nd (mkChild2 nd ms q y2))).
      { intros hp2_ok; unfold p2 in hp2_ok |- *.
        destruct b2 eqn:Hb2.
        - destruct (t0PowNorm wordFuel 1 yp) as [yp1 |] eqn:Hyp1; [| discriminate hp2_ok].
          destruct (hstep _ m1 hp2_ok hm1) as [hcl2 hm2].
          exact (conj hm2 (fun _ => ex_intro _ yp1
            (conj (RelT0Pow_trans hyp_rel (t0PowNorm_sound Hyp1))
              (conj (t0PowNorm_noTrailZero hyp_tz Hyp1) (childClosedAt_of_nodeClosed nd hcl2))))).
        - destruct (proj1 runBeforeStop_false_iff Hb2) as [qs2 [heq2 hge2]]; rewrite heq2 in hst2.
          exact (conj hm1 (fun hqm => hst2 q hge2 hqm)). }
      destruct p2 as [ok2 m2]; destruct ok2; [cbn [negb] in hok |- * | discriminate hok].
      destruct (hp2_spec eq_refl) as [hm2 hc2]; cbn [snd] in hm2.
      (* Child 3 *)
      fold (mkChild3 nd ms ms_next q yp) in hok |- *.
      set (p3 := if b3 then stepFn (mkChild3 nd ms ms_next q yp) m2 else (true, m2)) in *.
      assert (hp3_spec : fst p3 = true ->
        MemoValid NodeClosed (snd p3) /\
        (q <= q_max -> exists y3, RelT0Pow q (nd_Y nd) y3 /\ noTrailZero y3 = true /\
          ChildClosedAt nd (mkChild3 nd ms ms_next q y3))).
      { intros hp3_ok; unfold p3 in hp3_ok |- *.
        destruct b3 eqn:Hb3.
        - destruct (hstep _ m2 hp3_ok hm2) as [hcl3 hm3].
          exact (conj hm3 (fun _ => ex_intro _ yp (conj hyp_rel (conj hyp_tz (childClosedAt_of_nodeClosed nd hcl3))))).
        - destruct (proj1 runBeforeStop_false_iff Hb3) as [qs3 [heq3 hge3]]; rewrite heq3 in hst3.
          exact (conj hm2 (fun hqm => stopInv_zero_at hst3 hge3 hqm)). }
      destruct p3 as [ok3 m3]; destruct ok3; [cbn [negb] in hok |- * | discriminate hok].
      destruct (hp3_spec eq_refl) as [hm3 hc3]; cbn [snd] in hm3.
      (* Child 4 *)
      change (mkWaveNode
                (nd_s nd + 1) (nd_db_shift nd + 1) true
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
                0 0%Z ms_next (-1)%Z
                (nd_extra_B nd) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
                ((q + 1) * ms) (- Z.of_N (2 * nd_extra_B nd + 2))%Z
                (pow2N (nd_s nd + 1)) (64 * (q + 1)) (- Z.of_N (pow2N (nd_s nd + 1) * (nd_extra_B nd + 1)))%Z
                (childJB nd ms q) yp (nd_wRQ nd) (nd_pRQ nd))
        with (mkChild4 nd ms ms_next q yp) in hok |- *.
      assert (hp4_spec :
        MemoValid NodeClosed (snd (if b4 then stepFn (mkChild4 nd ms ms_next q yp) m3 else (true, m3))) /\
        (q <= q_max -> exists y4, RelT0Pow q (nd_Y nd) y4 /\ noTrailZero y4 = true /\
          ChildClosedAt nd (mkChild4 nd ms ms_next q y4))).
      { destruct b4 eqn:Hb4.
        - destruct (hstep _ m3 hok hm3) as [hcl4 hm4].
          exact (conj hm4 (fun _ => ex_intro _ yp (conj hyp_rel (conj hyp_tz (childClosedAt_of_nodeClosed nd hcl4))))).
        - destruct (proj1 runBeforeStop_false_iff Hb4) as [qs4 [heq4 hge4]]; rewrite heq4 in hst4.
          exact (conj hm3 (fun hqm => stopInv_zero_at hst4 hge4 hqm)). }
      destruct hp4_spec as [hm4 hc4].
      split; [exact hm4 | intros hqm u_val k0 d0 j_val P hst hq_eq].
      exact (loopQ_step_children nd ms ms_next q hs4 hfr hms hmsn
        (hc1 hqm) (hc2 hqm) (hc3 hqm) (hc4 hqm) hst hq_eq).
Qed.

#[local] Arguments stepQBody : simpl never.

Local Lemma verifyWaveI0_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms ms_next two_d_hi_u : N) (memo : MemoTree)
    (hkhic : (nd_k_hi_c nd <= 0)%Z) (htz : noTrailZero (nd_Y nd) = true)
    (hs4 : nd_s nd <= 4) (hfr : nd_has_i1_front nd = false)
    (hms_eq : ms = msOf (nd_s nd)) (hmsn_eq : ms_next = msOf (nd_s nd + 1))
    (h2d_eq : two_d_hi_u = twoDInitHiU nd)
    (hok : fst (verifyWaveI0 stepFn nd ms ms_next two_d_hi_u memo) = true)
    (hm : MemoValid NodeClosed memo) :
  NodeClosed nd /\ MemoValid NodeClosed (snd (verifyWaveI0 stepFn nd ms ms_next two_d_hi_u memo)).
Proof.
  assert (hms_pos : 0 < ms) by (rewrite hms_eq; apply msOf_pos; lia).
  assert (hms_dbl : 2 * ms_next = ms) by (rewrite hms_eq, hmsn_eq; apply msOf_succ; lia).
  unfold verifyWaveI0 in hok |- *; cbn zeta in hok |- *.
  remember (floorMinU1
    (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u (nd_jb nd) + nd_w_lo_u nd))
    (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd)) + jb_inf_c (nd_jb nd) + nd_w_lo_c nd)%Z ms)
    as q_min eqn:Hqmin.
  remember (floorMaxU1
    (Z.of_N (2 * nd_k_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd + nd_w_hi_u nd))
    (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + nd_scaled_db_c nd)) + nd_w_hi_c nd)%Z ms)
    as q_max eqn:Hqmax.
  assert (hq_range : forall (u_val k0 d0 j_val : N) (P : list BecTok1),
      NodeState nd u_val k0 d0 j_val P ->
      let q := (evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val)) / (ms * u_val) in
      q_min <= q /\ q <= q_max).
  { intros u_val k0 d0 j_val P hst.
    destruct hst as [hU _ _ _ _ _ _ _ _ hklo hkhi hwlo hwhi hjb hdb hd1 hd2 _ _ _ _].
    assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
    destruct (div_mod_spec (evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val)) (ms * u_val) hmsU_pos)
      as [q [rq [hq [_ [hdiv hmod]]]]].
    cbn zeta; rewrite hq.
    pose proof (twoDInitHiU_sound nd u_val k0 d0 hU hkhi hkhic hd1 hd2) as h2d;
      rewrite <- h2d_eq in h2d.
    destruct hjb as [_ [_ [_ [_ [_ hinf]]]]].
    assert (hJ_le : j_val <= d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd).
    { pose proof (N.mul_le_mono_r _ _ (deltaB P) (pow2N_pos (nd_db_shift nd))) as hsh.
      clear - hdb hsh; lia. }
    split.
    - rewrite Hqmin; apply (floorMinU1_le _ _ ms u_val q hU hms_pos).
      assert (hlt_q : evalPhi 0 P + 2 * (k0 + nd_extra_B nd + j_val) + 1 <= ms * u_val * (q + 1))
        by (replace (ms * u_val * (q + 1)) with ((ms * u_val) * q + ms * u_val) by ring;
            clear - hdiv hmod; lia).
      assert (hring_min :
        (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u (nd_jb nd) + nd_w_lo_u nd) * Z.of_N u_val +
         (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd)) + jb_inf_c (nd_jb nd) + nd_w_lo_c nd) =
         2 * (Z.of_N (nd_k_lo_u nd * u_val) + nd_k_lo_c nd) +
         (Z.of_N (jb_inf_u (nd_jb nd)) * Z.of_N u_val + jb_inf_c (nd_jb nd)) +
         (Z.of_N (nd_w_lo_u nd * u_val) + nd_w_lo_c nd) +
         Z.of_N (2 * nd_extra_B nd))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      clear - hklo hwlo hinf hlt_q hring_min; lia.
    - rewrite Hqmax; apply (floorMaxU1_ge _ _ ms u_val q hU hms_pos).
      assert (hring_max :
        (Z.of_N (2 * nd_k_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd + nd_w_hi_u nd) * Z.of_N u_val +
         (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + nd_scaled_db_c nd)) + nd_w_hi_c nd) =
         2 * (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd) +
         Z.of_N (two_d_hi_u * u_val) +
         2 * Z.of_N (nd_scaled_db_u nd * u_val + nd_scaled_db_c nd) +
         (Z.of_N (nd_w_hi_u nd * u_val) + nd_w_hi_c nd) +
         Z.of_N (2 * nd_extra_B nd))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      clear - hdiv h2d hJ_le hkhi hwhi hring_max; lia. }
  destruct (q_max <? q_min) eqn:Hqm_lt.
  - apply N.ltb_lt in Hqm_lt.
    assert (hcl_nd : NodeClosed nd).
    { intros u_val k0 d0 j_val P hst.
      destruct (hq_range u_val k0 d0 j_val P hst); lia. }
    exact (conj hcl_nd (memoInsert_sound hm hcl_nd)).
  - destruct (4096 <? q_max - q_min); [discriminate hok |].
    assert (hst_all :
      let '(st1, st2, st3, st4) := findQStops nd ms ms_next q_min q_max in
      StopInv (mkChild1 nd ms ms_next) nd q_max 0 st1 /\
      StopInv (mkChild2 nd ms) nd q_max 1 st2 /\
      StopInv (mkChild3 nd ms ms_next) nd q_max 0 st3 /\
      StopInv (mkChild4 nd ms ms_next) nd q_max 0 st4).
    { unfold findQStops.
      destruct (findL0Anchor 7%nat (nd_Y nd) q_min q_max) as [[[q0 wy0] py0] |] eqn:Hanc;
        [| exact (conj I (conj I (conj I I)))].
      destruct (findL0Anchor_sound 7%nat (nd_Y nd) q_min q_max q0 wy0 py0 htz Hanc)
        as [_ [_ [y0 [hy0_rel [hy0_no [hy0_tz [hy0_I [hwy0 hpy0]]]]]]]].
      assert (hms_le : 2 * msOf (nd_s nd + 1) <= ms) by (rewrite <- hmsn_eq; lia).
      repeat split;
        [ rewrite <- (N.add_0_r wy0), <- (N.add_0_r py0)
        |
        | rewrite <- (N.add_0_r wy0), <- (N.add_0_r py0)
        | rewrite <- (N.add_0_r wy0), <- (N.add_0_r py0) ];
        (eapply (mk_stopInv _ _ ms q_max q0 wy0 py0 _ nd y0);
         [ exact hms_pos
         | exact hms_le
         | reflexivity
         | intros q y; repeat split; reflexivity
         | exact hy0_rel
         | exact hy0_no
         | exact hy0_tz
         | exact hy0_I
         | exact hwy0
         | exact hpy0 ]). }
    destruct (findQStops nd ms ms_next q_min q_max) as [[[st1 st2] st3] st4].
    destruct hst_all as [hst1 [hst2 [hst3 hst4]]].
    destruct (runRange 13%nat (stepQBody stepFn nd ms ms_next st1 st2 st3 st4)
                q_min (q_max - q_min + 1) memo) as [ok memo'] eqn:Hrun.
    destruct ok; [| discriminate hok].
    destruct (runRange_sound (stepQBody stepFn nd ms ms_next st1 st2 st3 st4)
                (stepQBody_sound stepFn hstep nd ms ms_next q_max st1 st2 st3 st4
                   hs4 hfr htz hms_eq hmsn_eq hst1 hst2 hst3 hst4)
                13%nat q_min (q_max - q_min + 1) memo
                ltac:(rewrite Hrun; reflexivity) hm) as [hmemo' hloop].
    rewrite Hrun in hmemo'; cbn [snd] in hmemo' |- *.
    assert (hcl_nd : NodeClosed nd).
    { intros u_val k0 d0 j_val P hst.
      destruct (hq_range u_val k0 d0 j_val P hst) as [hq_lo hq_hi].
      exact (hloop _ hq_lo ltac:(lia) hq_hi u_val k0 d0 j_val P hst eq_refl). }
    exact (conj hcl_nd (memoInsert_sound hmemo' hcl_nd)).
Qed.

Definition mkChildQA (nd : SymWaveNode) (ms_next : N) (ya : list BecTok1) : SymWaveNode :=
  mkWaveNode
    (nd_s nd + 1) (nd_db_shift nd) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms_next (-1)%Z
    (nd_extra_B nd + 1) (nd_scaled_db_u nd + pow2N (nd_db_shift nd) * ms_next) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (nd_jb nd) ya (nd_wRQ nd) (nd_pRQ nd).

Local Lemma stepQABody_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms_next : N) (htz : noTrailZero (nd_Y nd) = true) :
  forall (qa : N) (memo : MemoTree),
    fst (stepQABody stepFn nd ms_next qa memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (stepQABody stepFn nd ms_next qa memo)) /\
    (exists ya : list BecTok1,
      RelT0Pow qa (nd_Y nd) ya /\ noTrailZero ya = true /\
      NodeClosed (mkChildQA nd ms_next ya)).
Proof.
  intros qa memo hok hm.
  unfold stepQABody in hok |- *.
  destruct (t0PowNorm wordFuel qa (nd_Y nd)) as [ya |] eqn:Hya; [| discriminate hok].
  change (fst (stepFn (mkChildQA nd ms_next ya) memo) = true) in hok.
  destruct (hstep (mkChildQA nd ms_next ya) memo hok hm) as [hcl hm1].
  exact (conj hm1 (ex_intro _ ya (conj (t0PowNorm_sound Hya) (conj (t0PowNorm_noTrailZero htz Hya) hcl)))).
Qed.

#[local] Arguments stepQABody : simpl never.

Definition mkChildQS (nd : SymWaveNode) (ms qs : N) (next_jb : JBounds) (yq : list BecTok1) : SymWaveNode :=
  let ju := (Z.of_N (2 * (qs + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z in
  let jc := (- (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3))))%Z in
  mkWaveNode
    (nd_s nd) (nd_db_shift nd) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms (-1)%Z
    (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    (addJBound next_jb ju jc) yq (nd_wRQ nd) (nd_pRQ nd).

Local Lemma stepQSBody_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms sh4 ct : N) (tyc : list BecTok1) (next_jb : JBounds)
    (htz_tyc : noTrailZero tyc = true) :
  forall (qs : N) (memo : MemoTree),
    fst (stepQSBody stepFn nd ms sh4 ct tyc next_jb qs memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (stepQSBody stepFn nd ms sh4 ct tyc next_jb qs memo)) /\
    (holdsWithJBounds 64 (-2)%Z (Z.of_N (2 * (qs + 3) * ms))
       (- Z.of_N (2 * (nd_extra_B nd + 3)))%Z 1 next_jb
       (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) = true \/
     (nd_s nd = nd_db_shift nd /\
       holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
         (Z.of_N (128 * ct + 256 * (qs + 3)) - Z.of_N (128 * nd_wRQ nd))%Z
         (- Z.of_N (sh4 * (nd_extra_B nd + 3)))%Z
         (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) = true) \/
     (exists yq : list BecTok1,
       RelT0Pow qs tyc yq /\ noTrailZero yq = true /\
       ChildClosedAt (withJB nd next_jb) (mkChildQS nd ms qs next_jb yq))).
Proof.
  intros qs memo hok hm.
  unfold stepQSBody in hok |- *.
  destruct (holdsWithJBounds 64 (-2)%Z (Z.of_N (2 * (qs + 3) * ms))
              (- Z.of_N (2 * (nd_extra_B nd + 3)))%Z 1 next_jb
              (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) eqn:Hpr1.
  - exact (conj hm (or_introl eq_refl)).
  - destruct ((nd_s nd =? nd_db_shift nd) &&
              holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
                (Z.of_N (128 * ct + 256 * (qs + 3)) - Z.of_N (128 * nd_wRQ nd))%Z
                (- Z.of_N (sh4 * (nd_extra_B nd + 3)))%Z
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) eqn:Hpr2.
    + apply Bool.andb_true_iff in Hpr2 as [hseq hlin]; apply N.eqb_eq in hseq.
      exact (conj hm (or_intror (or_introl (conj hseq hlin)))).
    + destruct (t0PowNorm wordFuel qs tyc) as [yq |] eqn:Hyq; [| discriminate hok].
      change (fst (stepFn (mkChildQS nd ms qs next_jb yq) memo) = true) in hok.
      destruct (hstep (mkChildQS nd ms qs next_jb yq) memo hok hm) as [hcl hm1].
      refine (conj hm1 (or_intror (or_intror (ex_intro _ yq _)))).
      exact (conj (t0PowNorm_sound Hyq)
        (conj (t0PowNorm_noTrailZero htz_tyc Hyq) (childClosedAt_of_nodeClosed (withJB nd next_jb) hcl))).
Qed.

#[local] Arguments stepQSBody : simpl never.

Local Lemma qsStopOpt_sound (nd : SymWaveNode) (ms qs_lo qs_hi : N)
    (tyc : list BecTok1) (next_jb : JBounds)
    (hms_pos : 0 < ms) (hms : ms = msOf (nd_s nd)) (htz_tyc : noTrailZero tyc = true) :
  match qsStopOpt nd ms qs_lo qs_hi tyc next_jb with
  | None => True
  | Some qs_stop =>
    forall qs : N, qs_stop <= qs -> qs <= qs_hi ->
      exists yq : list BecTok1,
        RelT0Pow qs tyc yq /\ noTrailZero yq = true /\
        ChildClosedAt (withJB nd next_jb) (mkChildQS nd ms qs next_jb yq)
  end.
Proof.
  unfold qsStopOpt.
  destruct (findL0Anchor 7%nat tyc qs_lo qs_hi) as [[[qs0 wys0] pys0] |] eqn:Hanc; [| exact I].
  destruct (findL0Anchor_sound 7%nat tyc qs_lo qs_hi qs0 wys0 pys0 htz_tyc Hanc)
    as [_ [_ [y0 [hy0_rel [hy0_no [hy0_tz [hy0_I [hwy0 hpy0]]]]]]]].
  set (nxTpl := mkWaveNode
    (nd_s nd) (nd_db_shift nd) false
    (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
    0 0%Z ms (-1)%Z
    (nd_extra_B nd + 1) (nd_scaled_db_u nd) (nd_scaled_db_c nd)
    (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
    next_jb (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd)).
  assert (close_tpl : forall (qs bnd : N), qs0 <= qs -> qs <= bnd ->
      checkAbstract nxTpl true true (wys0 + (bnd - qs0)) (pys0 + (bnd - qs0)) = true ->
      exists yq : list BecTok1,
        RelT0Pow qs tyc yq /\ noTrailZero yq = true /\
        ChildClosedAt (withJB nd next_jb) (mkChildQS nd ms qs next_jb yq)).
  { intros qs bnd hq0 hqB hchk.
    set (yq := t0Pow (qs - qs0) y0).
    assert (hrel : RelT0Pow qs tyc yq)
      by (replace qs with (qs0 + (qs - qs0)) by lia;
          exact (RelT0Pow_trans hy0_rel (RelT0Pow_t0Pow _ hy0_no))).
    pose proof (noK1_t0Pow (qs - qs0) hy0_no) as hno; fold yq in hno.
    pose proof (noTrailZero_t0Pow (qs - qs0) hy0_no hy0_tz) as htz; fold yq in htz.
    pose proof (hasI_t0Pow (qs - qs0) hy0_no hy0_I) as hI; fold yq in hI.
    assert (hwy : evalPhi 0 yq <= wys0 + (bnd - qs0))
      by (unfold yq; rewrite (evalPhi_t0Pow 0 _ hy0_no), hwy0; lia).
    assert (hpy : evalPhi 22 yq <= pys0 + (bnd - qs0))
      by (unfold yq; rewrite (evalPhi_t0Pow 22 _ hy0_no), hpy0; lia).
    exists yq; split; [exact hrel | split; [exact htz |]].
    intros u_val k0 d0 j_c P_c hjb_base hns.
    cbn [withJB nd_jb] in hjb_base.
    set (nx0 := withJB (mkChildQS nd ms qs next_jb yq) next_jb).
    assert (hchk0 : checkAbstract nx0 true true (wys0 + (bnd - qs0)) (pys0 + (bnd - qs0)) = true).
    { exact (checkAbstract_mono nxTpl nx0 true true _ _ _ _
        eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        (fun h => h) (N.le_refl _) (N.le_refl _) (JBoundsLe_refl _) hchk). }
    pose proof (NodeState_withJB hns hjb_base) as hns0; fold nx0 in hns0.
    assert (hcfg0 : nodeCfg nx0 k0 j_c P_c = nodeCfg (mkChildQS nd ms qs next_jb yq) k0 j_c P_c)
      by reflexivity.
    rewrite <- hcfg0.
    exact (checkAbstract_sound hns0 hno (fun _ => hI) hwy hpy hchk0). }
  destruct (checkAbstract nxTpl true true (wys0 + (qs_hi - qs0)) (pys0 + (qs_hi - qs0))) eqn:Ha_hi.
  - intros qs hge hle; exact (close_tpl qs qs_hi hge hle Ha_hi).
  - set (jc_qs := (- (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3))))%Z).
    remember (dominantJuMin next_jb jc_qs) as min_ju eqn:Hmin_ju.
    set (need_qs := nd_k_hi_u nd + (min_ju + 1) / 2).
    set (req_qsr2 := (need_qs + ms - 1) / ms).
    set (qs_r := N.max qs0 (req_qsr2 - 2)).
    assert (hq0_le_qr : qs0 <= qs_r) by exact (N.le_max_l _ _).
    assert (hqr_ge : req_qsr2 - 2 <= qs_r) by exact (N.le_max_r _ _).
    destruct (qs_r <=? qs_hi) eqn:Hbr; [| exact I].
    set (ju_r := (Z.of_N (2 * (qs_r + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z).
    set (nx_r := withJB nxTpl (addJBound next_jb ju_r jc_qs)).
    destruct (checkAbstract nx_r true true (wys0 + (qs_r - qs0)) (pys0 + (qs_r - qs0))) eqn:Ha_r;
      [| exact I].
    assert (hdom_r : (Z.of_N (dominantJuMin next_jb jc_qs) <= ju_r)%Z).
    { rewrite <- Hmin_ju.
      pose proof (ceil_div_mul_ge min_ju 2 ltac:(lia)) as hd2.
      replace (min_ju + 2 - 1) with (min_ju + 1) in hd2 by lia.
      assert (h2need : min_ju + 2 * nd_k_hi_u nd <= 2 * need_qs)
        by (unfold need_qs; clear - hd2; lia).
      pose proof (ceil_div_mul_ge need_qs ms hms_pos) as hceil; fold req_qsr2 in hceil.
      assert (hmul_le : ms * req_qsr2 <= ms * (qs_r + 2))
        by (apply N.mul_le_mono_l; clear - hqr_ge; clearbody qs_r req_qsr2 need_qs; lia).
      assert (h2mul : 2 * need_qs <= 2 * (qs_r + 2) * ms).
      { replace (2 * (qs_r + 2) * ms) with (2 * (ms * (qs_r + 2))) by ring.
        clear - hceil hmul_le; clearbody qs_r req_qsr2 need_qs; lia. }
      unfold ju_r; clear - h2need h2mul; clearbody qs_r req_qsr2 need_qs; lia. }
    assert (close_shift : forall qs : N, qs_r <= qs ->
      exists yq : list BecTok1,
        RelT0Pow qs tyc yq /\ noTrailZero yq = true /\
        ChildClosedAt (withJB nd next_jb) (mkChildQS nd ms qs next_jb yq)).
    { intros qs hqr_q.
      assert (hq0_q : qs0 <= qs) by exact (N.le_trans _ _ _ hq0_le_qr hqr_q).
      set (yq := t0Pow (qs - qs0) y0).
      assert (hrel : RelT0Pow qs tyc yq)
        by (replace qs with (qs0 + (qs - qs0)) by lia;
            exact (RelT0Pow_trans hy0_rel (RelT0Pow_t0Pow _ hy0_no))).
      pose proof (noK1_t0Pow (qs - qs0) hy0_no) as hno; fold yq in hno.
      pose proof (noTrailZero_t0Pow (qs - qs0) hy0_no hy0_tz) as htz; fold yq in htz.
      pose proof (hasI_t0Pow (qs - qs0) hy0_no hy0_I) as hI; fold yq in hI.
      assert (hwy : evalPhi 0 yq <= wys0 + (qs - qs0))
        by (unfold yq; rewrite (evalPhi_t0Pow 0 _ hy0_no), hwy0; lia).
      assert (hpy : evalPhi 22 yq <= pys0 + (qs - qs0))
        by (unfold yq; rewrite (evalPhi_t0Pow 22 _ hy0_no), hpy0; lia).
      assert (ha_r_Y : checkAbstract (withJB (withY nxTpl yq) (addJBound next_jb ju_r jc_qs))
                         true true (wys0 + (qs_r - qs0)) (pys0 + (qs_r - qs0)) = true).
      { exact (checkAbstract_mono nx_r _ true true _ _ _ _
          eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
          (fun h => h) (N.le_refl _) (N.le_refl _) (JBoundsLe_refl _) Ha_r). }
      assert (hsh : checkAbstract (mkChildQS nd ms qs next_jb yq) true true
                      (wys0 + (qs - qs0)) (evalPhi 22 yq) = true).
      { change (mkChildQS nd ms qs next_jb yq)
          with (withJB (withY nxTpl yq)
                 (addJBound next_jb (Z.of_N (2 * (qs + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z jc_qs)).
        refine (checkAbstract_shift (withY nxTpl yq) next_jb jc_qs ju_r
          (Z.of_N (2 * (qs + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd))%Z jc_qs (qs - qs_r) (2 * ms)
          (wys0 + (qs_r - qs0)) (wys0 + (qs - qs0))
          (pys0 + (qs_r - qs0)) (evalPhi 22 yq)
          hdom_r _ eq_refl _ _ _ ha_r_Y).
        - unfold ju_r.
          assert (hsub : 2 * (qs + 2) * ms = 2 * (qs_r + 2) * ms + (qs - qs_r) * (2 * ms)).
          { replace (2 * (qs + 2)) with (2 * (qs_r + 2) + 2 * (qs - qs_r))
              by (clear - hqr_q; clearbody qs_r req_qsr2 need_qs; lia).
            ring. }
          clear - hsub; clearbody qs_r req_qsr2 need_qs; lia.
        - unfold nxTpl; cbn [withY nd_s]; rewrite hms; lia.
        - clear - hq0_le_qr hqr_q; clearbody qs_r req_qsr2 need_qs; lia.
        - clear - hq0_le_qr hqr_q hpy; clearbody qs_r req_qsr2 need_qs yq; lia. }
      exists yq; split; [exact hrel | split; [exact htz |]].
      intros u_val k0 d0 j_c P_c _ hns.
      exact (checkAbstract_sound hns hno (fun _ => hI) hwy (N.le_refl _) hsh). }
    destruct (qs_r <=? qs0) eqn:Hbr0.
    + apply N.leb_le in Hbr0; intros qs hge _.
      exact (close_shift qs ltac:(clear - Hbr0 hge; clearbody qs_r req_qsr2 need_qs; lia)).
    + apply N.leb_gt in Hbr0.
      destruct (checkAbstract nxTpl true true (wys0 + (qs_r - 1 - qs0)) (pys0 + (qs_r - 1 - qs0))) eqn:Ha_mid.
      * intros qs hge _.
        destruct (N.lt_ge_cases qs qs_r) as [hlt | hge_r];
          [exact (close_tpl qs (qs_r - 1) hge ltac:(clear - hlt; clearbody qs_r req_qsr2 need_qs; lia) Ha_mid)
          | exact (close_shift qs hge_r)].
      * intros qs hge _; exact (close_shift qs hge).
Qed.

(* ========================================================================== *)
(* Layer 3b Soundness Part 3b: CT Sweep, Wave Node, Slab & Root Closure       *)
(* ========================================================================== *)

Local Lemma z_le_of_pos_mul_le {d : N} {a b : Z}
    (hd : 0 < d) (h : (Z.of_N d * a <= Z.of_N d * b)%Z) : (a <= b)%Z.
Proof.
  destruct (Z_le_gt_dec a b) as [hle | hgt]; [exact hle |].
  pose proof (Z.mul_le_mono_nonneg_l (b + 1)%Z a (Z.of_N d) ltac:(lia) ltac:(lia)) as hm.
  replace (Z.of_N d * (b + 1))%Z with (Z.of_N d * b + Z.of_N d)%Z in hm by ring.
  lia.
Qed.

Local Lemma n_le_of_pos_mul_lt {d a b : N}
    (h : d * a < d * b) : a < b.
Proof.
  destruct (N.lt_ge_cases a b) as [hlt | hge]; [exact hlt |].
  pose proof (N.mul_le_mono_l b a d hge) as hm; lia.
Qed.

Local Lemma ct_sh_ident (nd : SymWaveNode) (ms ct u_val : N) (P : list BecTok1)
    (hs5 : nd_s nd <= 5) (hms : ms = msOf (nd_s nd))
    (hpsi : evalPhi 2 P = ct * (ms * u_val)) :
  pow2N (nd_s nd + 1) * evalPhi 0 P + pow2N (nd_s nd + 2) * deltaB P = 128 * ct * u_val.
Proof.
  pose proof (evalPhi_eq_zero_add_deltaB 2 P) as he2.
  assert (hms64 : msOf (nd_s nd) * (2 ^ nd_s nd) = 64) by (apply msOf_mul_pow2; lia).
  assert (hp1 : pow2N (nd_s nd + 1) = 2 * (2 ^ nd_s nd))
    by (rewrite pow2N_succ, pow2N_eq; reflexivity).
  assert (hp2 : pow2N (nd_s nd + 2) = 4 * (2 ^ nd_s nd))
    by (replace (nd_s nd + 2) with ((nd_s nd + 1) + 1) by lia;
        rewrite pow2N_succ, hp1; ring).
  rewrite hpsi, hms in he2.
  rewrite hp1, hp2.
  transitivity (2 * (2 ^ nd_s nd) * (evalPhi 0 P + 2 * deltaB P)); [ring |].
  rewrite <- he2.
  transitivity (2 * (msOf (nd_s nd) * (2 ^ nd_s nd)) * ct * u_val); [ring |].
  rewrite hms64; ring.
Qed.

Local Lemma ct_4d_bound (nd : SymWaveNode) (ms ct u_val k0 d0 j_val : N) (P : list BecTok1)
    (hs5 : nd_s nd <= 5) (hms : ms = msOf (nd_s nd))
    (hst : NodeState nd u_val k0 d0 j_val P) (hseq : nd_s nd = nd_db_shift nd)
    (hpsi : evalPhi 2 P = ct * (ms * u_val)) :
  128 * nd_wRQ nd * u_val + 1 <= 7 * k0 + 128 * ct * u_val + pow2N (nd_s nd + 2) * j_val.
Proof.
  pose proof (ct_sh_ident nd ms ct u_val P hs5 hms hpsi) as hident.
  pose proof (nst_D_lo _ _ _ _ _ _ hst hseq) as hd0.
  pose proof (nst_wM_lo _ _ _ _ _ _ hst) as hwM.
  remember (pow2N (nd_s nd)) as sh0 eqn:Hsh0.
  remember (pow2N (nd_s nd + 1)) as sh2 eqn:Hsh2.
  assert (hp2 : pow2N (nd_s nd + 2) = 4 * sh0)
    by (replace (nd_s nd + 2) with ((nd_s nd + 1) + 1) by lia;
        rewrite !pow2N_succ, <- Hsh0; ring).
  remember (pow2N (nd_s nd + 2)) as sh4 eqn:Hsh4.
  pose proof (N.mul_le_mono_l _ _ 4 hd0) as hmul4.
  assert (h4_rhs : 4 * (sh0 * (deltaB P + j_val)) = sh4 * deltaB P + sh4 * j_val)
    by (rewrite hp2; ring).
  clear - hident hwM hmul4 h4_rhs; lia.
Qed.

Local Lemma stepCT_next_jb_qslo (nd : SymWaveNode) (ms sh2 ct_cur : N)
    (hs5 : nd_s nd <= 5) (hms : ms = msOf (nd_s nd)) (hsh2 : sh2 = pow2N (nd_s nd + 1))
    (ct_ju ct_jc : Z) (next_jb : JBounds) (qs_lo : N)
    (hcp : (let raw_ju := (Z.of_N (128 * nd_wRQ nd) - Z.of_N (7 * nd_k_hi_u nd + 128 * (ct_cur + 1)))%Z in
            let raw_jc := (3 - 7 * nd_k_hi_c nd)%Z in
            if (nd_s nd =? nd_db_shift nd) && (0 <=? raw_ju)%Z then
              let rju := toNatClip raw_ju in
              (Z.of_N (rju / sh2), fdivNat (raw_jc + Z.of_N (rju mod sh2))%Z sh2)
            else (0%Z, 0%Z)) = (ct_ju, ct_jc))
    (hnjb_eq : addJBound (nd_jb nd) ct_ju ct_jc = next_jb)
    (hqslo_eq : floorMinU1
                  (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb))
                  (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb)%Z
                  (2 * ms) - 2 = qs_lo)
    (u_val k0 d0 j_val : N) (P : list BecTok1)
    (hst : NodeState nd u_val k0 d0 j_val P)
    (hpsi : evalPhi 2 P = ct_cur * (ms * u_val)) :
  JBoundsValid next_jb u_val j_val /\
  (2 * (ms * u_val) <= k0 + nd_extra_B nd + j_val + 3 ->
    qs_lo <= (k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2).
Proof.
  assert (hms_pos : 0 < ms) by (rewrite hms; apply msOf_pos; lia).
  assert (hnjb : JBoundsValid next_jb u_val j_val).
  { rewrite <- hnjb_eq; cbn zeta in hcp.
    set (raw_ju := (Z.of_N (128 * nd_wRQ nd) - Z.of_N (7 * nd_k_hi_u nd + 128 * (ct_cur + 1)))%Z) in hcp.
    set (raw_jc := (3 - 7 * nd_k_hi_c nd)%Z) in hcp.
    destruct ((nd_s nd =? nd_db_shift nd) && (0 <=? raw_ju)%Z) eqn:Hcond.
    - injection hcp as <- <-.
      apply Bool.andb_true_iff in Hcond as [hseq hrge].
      apply N.eqb_eq in hseq; apply Z.leb_le in hrge.
      apply (addJBound_sound (nst_jb _ _ _ _ _ _ hst)).
      pose proof (nst_khi _ _ _ _ _ _ hst) as hkhi.
      pose proof (nst_U _ _ _ _ _ _ hst) as hU.
      assert (hsh2_pos : 0 < sh2) by (rewrite hsh2; pose proof (pow2N_pos (nd_s nd + 1)); lia).
      assert (hsh4_eq : pow2N (nd_s nd + 2) = 2 * sh2)
        by (replace (nd_s nd + 2) with ((nd_s nd + 1) + 1) by lia;
            rewrite pow2N_succ, <- hsh2; reflexivity).
      pose proof (ct_4d_bound nd ms ct_cur u_val k0 d0 j_val P hs5 hms hst hseq hpsi) as hwM2.
      rewrite hsh4_eq in hwM2.
      remember (toNatClip raw_ju) as rju eqn:Hrju.
      assert (hrju_v : Z.of_N rju = raw_ju)
        by (rewrite Hrju; exact (proj1 (toNatClip_spec raw_ju) hrge)).
      assert (hraw_le : (Z.of_N rju * Z.of_N u_val + raw_jc <= Z.of_N (sh2 * (2 * j_val)))%Z).
      { assert (hring_raw :
          (Z.of_N rju * Z.of_N u_val + raw_jc - Z.of_N (sh2 * (2 * j_val)) =
           (Z.of_N (128 * nd_wRQ nd * u_val + 1) -
            Z.of_N (7 * k0 + 128 * ct_cur * u_val + (2 * sh2) * j_val)) +
           7 * (Z.of_N k0 - (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)) +
           (2 - 128 * Z.of_N u_val))%Z)
          by (rewrite hrju_v; unfold raw_ju, raw_jc;
              repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
        clear - hwM2 hkhi hU hring_raw; lia. }
      destruct (div_mod_spec rju sh2 hsh2_pos) as [q_rju [m_rju [hq_d [hm_d [hdiv_rju _]]]]].
      rewrite hq_d, hm_d.
      pose proof (fdivNat_le (raw_jc + Z.of_N m_rju)%Z sh2 hsh2_pos) as hfdiv.
      remember (fdivNat (raw_jc + Z.of_N m_rju)%Z sh2) as fd eqn:Hfd.
      pose proof (N.mul_le_mono_l 1 u_val m_rju hU) as hm_le_u.
      assert (hdiv_u : sh2 * q_rju * u_val + m_rju <= rju * u_val).
      { assert (h1 : (sh2 * q_rju + m_rju) * u_val = rju * u_val) by (rewrite hdiv_rju; reflexivity).
        replace ((sh2 * q_rju + m_rju) * u_val) with (sh2 * q_rju * u_val + m_rju * u_val) in h1 by ring.
        clear - h1 hm_le_u; lia. }
      apply (z_le_of_pos_mul_le hsh2_pos).
      assert (hring_fd :
        (Z.of_N sh2 * (Z.of_N q_rju * Z.of_N u_val + fd) - Z.of_N sh2 * Z.of_N (2 * j_val) =
         (Z.of_N (sh2 * q_rju * u_val + m_rju) - Z.of_N (rju * u_val)) +
         (Z.of_N sh2 * fd - (raw_jc + Z.of_N m_rju)) +
         (Z.of_N rju * Z.of_N u_val + raw_jc - Z.of_N (sh2 * (2 * j_val))))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      clear - hdiv_u hfdiv hraw_le hring_fd; clearbody raw_jc; lia.
    - injection hcp as <- <-.
      apply (addJBound_sound (nst_jb _ _ _ _ _ _ hst)); lia. }
  split; [exact hnjb | intros h2ms].
  rewrite <- hqslo_eq.
  destruct hnjb as [_ [_ [_ [_ [_ hinf]]]]].
  pose proof (nst_klo _ _ _ _ _ _ hst) as hklo.
  pose proof (nst_U _ _ _ _ _ _ hst) as hU.
  assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
  destruct (div_mod_spec (k0 + nd_extra_B nd + j_val + 3) (ms * u_val) hmsU_pos)
    as [d_qs [rem_qs [hd_qs [_ [hdiv hmod]]]]].
  rewrite hd_qs.
  assert (hge2 : 2 <= d_qs).
  { destruct (N.lt_ge_cases d_qs 2) as [hlt2 | hge2]; [| exact hge2].
    assert (d_qs = 0 \/ d_qs = 1) as [-> | ->] by lia;
      clear - h2ms hdiv hmod; lia. }
  set (qs := d_qs - 2).
  assert (hd_qs_eq : d_qs = qs + 2) by (unfold qs; lia).
  rewrite hd_qs_eq in hdiv; fold qs.
  assert (hqslo0 :
    floorMinU1
      (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb))
      (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb)%Z
      (2 * ms) <= qs + 2).
  { apply (floorMinU1_le _ _ (2 * ms) u_val (qs + 2) hU ltac:(lia)).
    assert (h2lt : 2 * (k0 + nd_extra_B nd + j_val + 3) + 2 <= (2 * ms) * u_val * (qs + 2 + 1))
      by (replace ((2 * ms) * u_val * (qs + 2 + 1))
            with (2 * ((ms * u_val) * (qs + 2) + ms * u_val)) by ring;
          clear - hdiv hmod; lia).
    assert (hring_qslo :
      (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb) * Z.of_N u_val +
       (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb) =
       2 * (Z.of_N (nd_k_lo_u nd * u_val) + nd_k_lo_c nd) +
       (Z.of_N (jb_inf_u next_jb) * Z.of_N u_val + jb_inf_c next_jb) +
       Z.of_N (2 * (nd_extra_B nd + 3)))%Z)
      by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
    clear - hklo hinf h2lt hring_qslo; clearbody qs; lia. }
  remember (floorMinU1
    (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb))
    (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb)%Z
    (2 * ms)) as qv.
  clear - hqslo0; clearbody qs; lia.
Qed.

Local Lemma stepCTInner_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms qs_hi sh2 sh4 ct_cur : N)
    (hs5 : nd_s nd <= 5) (hfr : nd_has_i1_front nd = true)
    (hms : ms = msOf (nd_s nd))
    (hsh2 : sh2 = pow2N (nd_s nd + 1)) (hsh4 : sh4 = pow2N (nd_s nd + 2))
    (yc tyc : list BecTok1)
    (hyc_rel : RelT0Pow ct_cur (nd_Y nd) yc) (htyc_rel : RelT M1 yc tyc)
    (htz_tyc : noTrailZero tyc = true)
    (memo : MemoTree)
    (hok : fst (stepCTInner stepFn nd ms qs_hi sh2 sh4 ct_cur tyc memo) = true)
    (hm : MemoValid NodeClosed memo) :
  MemoValid NodeClosed (snd (stepCTInner stepFn nd ms qs_hi sh2 sh4 ct_cur tyc memo)) /\
  (forall u_val k0 d0 j_val (P P_s : list BecTok1),
    NodeState nd u_val k0 d0 j_val P ->
    evalPhi 2 P = ct_cur * (ms * u_val) ->
    noK1 P_s = true ->
    countBin P_s = countBin P ->
    deltaB P_s = deltaB P ->
    evalPhi 0 P_s = (k0 + nd_extra_B nd + j_val + 3) mod (ms * u_val) ->
    2 * (ms * u_val) <= k0 + nd_extra_B nd + j_val + 3 ->
    (k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2 <= qs_hi ->
    (forall yc' tyc' yq : list BecTok1,
      RelT0Pow ct_cur (nd_Y nd) yc' -> RelT M1 yc' tyc' ->
      RelT0Pow ((k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2) tyc' yq ->
      exists W : list BecTok1,
        RelT M1 (P ++ nd_Y nd) W /\
        RelT0Pow (k0 + nd_extra_B nd + j_val + 1) W (P_s ++ yq)) ->
    exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
      (InC0 k' tail' \/ InC1 k' tail')).
Proof.
  assert (hms_pos : 0 < ms) by (rewrite hms; apply msOf_pos; lia).
  unfold stepCTInner in hok |- *.
  remember (let raw_ju := (Z.of_N (128 * nd_wRQ nd) - Z.of_N (7 * nd_k_hi_u nd + 128 * (ct_cur + 1)))%Z in
            let raw_jc := (3 - 7 * nd_k_hi_c nd)%Z in
            if (nd_s nd =? nd_db_shift nd) && (0 <=? raw_ju)%Z then
              let rju := toNatClip raw_ju in
              (Z.of_N (rju / sh2), fdivNat (raw_jc + Z.of_N (rju mod sh2))%Z sh2)
            else (0%Z, 0%Z)) as cp eqn:Hcp_sym.
  destruct cp as [ct_ju ct_jc]; symmetry in Hcp_sym.
  cbn zeta in hok |- *.
  remember (addJBound (nd_jb nd) ct_ju ct_jc) as next_jb eqn:Hnjb; symmetry in Hnjb.
  remember (floorMinU1
              (Z.of_N (2 * nd_k_lo_u nd + jb_inf_u next_jb))
              (2 * (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 3)) + jb_inf_c next_jb)%Z
              (2 * ms) - 2) as qs_lo eqn:Hqslo; symmetry in Hqslo.
  destruct (qs_hi <? qs_lo) eqn:Hb_qslo.
  - apply N.ltb_lt in Hb_qslo.
    cbn [snd]; split; [exact hm |].
    intros u_val k0 d0 j_val P P_s hst hpsi _ _ _ _ h2ms hqs_hi _.
    destruct (stepCT_next_jb_qslo nd ms sh2 ct_cur hs5 hms hsh2 ct_ju ct_jc next_jb qs_lo
                Hcp_sym Hnjb Hqslo u_val k0 d0 j_val P hst hpsi) as [_ hqs_lo_fn].
    pose proof (hqs_lo_fn h2ms) as hqs_lo.
    remember ((k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2) as qsv.
    clear - Hb_qslo hqs_lo hqs_hi; lia.
  - apply N.ltb_ge in Hb_qslo.
    destruct (4096 <? qs_hi - qs_lo); [discriminate hok |].
    cbn zeta in hok |- *.
    pose proof (qsStopOpt_sound nd ms qs_lo qs_hi tyc next_jb hms_pos hms htz_tyc) as hstop_spec.
    remember (qsStopOpt nd ms qs_lo qs_hi tyc next_jb) as qs_stop_opt eqn:Hqstop.
    remember (match qs_stop_opt with
              | None => qs_hi - qs_lo + 1
              | Some qs_stop =>
                if qs_stop <=? qs_lo then 0
                else N.min (qs_stop - qs_lo) (qs_hi - qs_lo + 1)
              end) as cntQS eqn:Hcnt.
    destruct (runRange_sound (stepQSBody stepFn nd ms sh4 ct_cur tyc next_jb)
                (stepQSBody_sound stepFn hstep nd ms sh4 ct_cur tyc next_jb htz_tyc)
                13%nat qs_lo cntQS memo hok hm) as [hm1 hqs_loop].
    split; [exact hm1 |].
    intros u_val k0 d0 j_val P P_s hst hpsi hno_s hcb_s hdb_s hw_s h2ms hqs_hi hstep_s.
    destruct (stepCT_next_jb_qslo nd ms sh2 ct_cur hs5 hms hsh2 ct_ju ct_jc next_jb qs_lo
                Hcp_sym Hnjb Hqslo u_val k0 d0 j_val P hst hpsi) as [hnjb hqs_lo_fn].
    pose proof (hqs_lo_fn h2ms) as hqs_lo.
    pose proof (nst_U _ _ _ _ _ _ hst) as hU.
    assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
    destruct (div_mod_spec (k0 + nd_extra_B nd + j_val + 3) (ms * u_val) hmsU_pos)
      as [d_qs [rem_qs [hd_qs [hrem_qs [hdiv hmod]]]]].
    rewrite hd_qs in hqs_lo, hqs_hi, hstep_s.
    rewrite hrem_qs in hw_s.
    assert (hge2 : 2 <= d_qs).
    { destruct (N.lt_ge_cases d_qs 2) as [hlt2 | hge2]; [| exact hge2].
      assert (d_qs = 0 \/ d_qs = 1) as [-> | ->] by lia;
        clear - h2ms hdiv hmod; lia. }
    remember (d_qs - 2) as qs eqn:Hqs_def.
    assert (hqs2 : d_qs = qs + 2) by lia.
    rewrite hqs2 in hdiv.
    assert (hlt_qs3 : k0 + nd_extra_B nd + j_val + 3 < (ms * u_val) * (qs + 3))
      by (replace ((ms * u_val) * (qs + 3)) with ((ms * u_val) * (qs + 2) + ms * u_val) by ring;
          clear - hdiv hmod; lia).
    assert (hqs_cases :
      holdsWithJBounds 64 (-2)%Z (Z.of_N (2 * (qs + 3) * ms))
        (- Z.of_N (2 * (nd_extra_B nd + 3)))%Z 1 next_jb
        (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) = true \/
      (nd_s nd = nd_db_shift nd /\
        holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
          (Z.of_N (128 * ct_cur + 256 * (qs + 3)) - Z.of_N (128 * nd_wRQ nd))%Z
          (- Z.of_N (sh4 * (nd_extra_B nd + 3)))%Z
          (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd) = true) \/
      (exists yq : list BecTok1,
        RelT0Pow qs tyc yq /\ noTrailZero yq = true /\
        ChildClosedAt (withJB nd next_jb) (mkChildQS nd ms qs next_jb yq))).
    { destruct qs_stop_opt as [qs_stop |].
      - destruct (N.lt_ge_cases qs qs_stop) as [hlt_st | hge_st].
        + assert (hble_f : (qs_stop <=? qs_lo) = false) by (apply N.leb_gt; clear - hqs_lo hlt_st; lia).
          rewrite hble_f in Hcnt.
          exact (hqs_loop qs hqs_lo ltac:(rewrite Hcnt; clear - hqs_lo hqs_hi hlt_st; lia)).
        + exact (or_intror (or_intror (hstop_spec qs hge_st hqs_hi))).
      - exact (hqs_loop qs hqs_lo ltac:(rewrite Hcnt; clear - hqs_lo hqs_hi; lia)). }
    destruct hqs_cases as [hpr_q1 | [[hseq hpr_q2] | [yq [hyq_rel [hyq_tz hcl_q]]]]].
    + pose proof (holdsWithJBounds_sound hnjb hU (nst_K64 _ _ _ _ _ _ hst)
                    (nst_klo _ _ _ _ _ _ hst) (nst_khi _ _ _ _ _ _ hst) hpr_q1) as hp.
      assert (h2lt : 2 * (k0 + nd_extra_B nd + j_val + 3) + 2 <= (2 * (qs + 3) * ms) * u_val)
        by (replace ((2 * (qs + 3) * ms) * u_val) with (2 * ((ms * u_val) * (qs + 3))) by ring;
            clear - hlt_qs3; lia).
      assert (hring_q1 :
        ((-2) * Z.of_N k0 + Z.of_N (2 * (qs + 3) * ms) * Z.of_N u_val +
         (- Z.of_N (2 * (nd_extra_B nd + 3))) - Z.of_N (1 * (2 * j_val)) =
         Z.of_N ((2 * (qs + 3) * ms) * u_val) -
         Z.of_N (2 * (k0 + nd_extra_B nd + j_val + 3)))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      exfalso; clear - hp h2lt hring_q1; lia.
    + pose proof (holdsLinearAllUK_sound hU (nst_K64 _ _ _ _ _ _ hst)
                    (nst_klo _ _ _ _ _ _ hst) (nst_khi _ _ _ _ _ _ hst) hpr_q2) as hp.
      pose proof (ct_4d_bound nd ms ct_cur u_val k0 d0 j_val P hs5 hms hst hseq hpsi) as hwM2.
      rewrite <- hsh4 in hwM2.
      assert (hsh4_ms : sh4 * ms = 256).
      { assert (hms64 : msOf (nd_s nd) * (2 ^ nd_s nd) = 64) by (apply msOf_mul_pow2; lia).
        assert (hp2 : sh4 = 4 * (2 ^ nd_s nd))
          by (rewrite hsh4; replace (nd_s nd + 2) with ((nd_s nd + 1) + 1) by lia;
              rewrite !pow2N_succ, pow2N_eq; ring).
        rewrite hp2, hms.
        transitivity (4 * (msOf (nd_s nd) * (2 ^ nd_s nd))); [ring | rewrite hms64; reflexivity]. }
      assert (hmul_qs : sh4 * (k0 + nd_extra_B nd + j_val + 3) <= 256 * (qs + 3) * u_val).
      { assert (hle_qs3 : k0 + nd_extra_B nd + j_val + 3 <= (ms * u_val) * (qs + 3))
          by (clear - hlt_qs3; lia).
        pose proof (N.mul_le_mono_l _ _ sh4 hle_qs3) as h1.
        replace (sh4 * ((ms * u_val) * (qs + 3))) with ((sh4 * ms) * (qs + 3) * u_val) in h1 by ring.
        rewrite hsh4_ms in h1; exact h1. }
      assert (hring_q2 :
        ((7 - Z.of_N sh4) * Z.of_N k0 +
         (Z.of_N (128 * ct_cur + 256 * (qs + 3)) - Z.of_N (128 * nd_wRQ nd)) * Z.of_N u_val +
         (- Z.of_N (sh4 * (nd_extra_B nd + 3))) =
         (Z.of_N (7 * k0 + 128 * ct_cur * u_val + sh4 * j_val) -
          Z.of_N (128 * nd_wRQ nd * u_val)) +
         (Z.of_N (256 * (qs + 3) * u_val) -
          Z.of_N (sh4 * (k0 + nd_extra_B nd + j_val + 3))))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      exfalso; clear - hp hwM2 hmul_qs hring_q2; lia.
    + destruct (hstep_s yc tyc yq hyc_rel htyc_rel hyq_rel) as [W [ht1_W hpow_W]].
      pose proof (nst_K64 _ _ _ _ _ _ hst) as hK64.
      pose proof (@collar_step_inC1_pow_raw (k0 + nd_extra_B nd + j_val)
                    (P ++ nd_Y nd) W (P_s ++ yq) ltac:(lia) ht1_W hpow_W) as hstep_tm.
      set (J_c := j_val + leadB P_s).
      set (P_c := dropB P_s).
      assert (hcfg_in : nodeCfg nd k0 j_val P =
                        cfgCollar (k0 + nd_extra_B nd + j_val) (TokI :: Tok1 :: (P ++ nd_Y nd)))
        by (unfold nodeCfg; rewrite hfr; reflexivity).
      assert (hcfg_out : cfgCollar (k0 + nd_extra_B nd + j_val + 1) (P_s ++ yq) =
                         nodeCfg (mkChildQS nd ms qs next_jb yq) k0 J_c P_c).
      { unfold nodeCfg, mkChildQS; cbn zeta; cbn [nd_extra_B nd_has_i1_front nd_Y].
        assert (hrw : P_s ++ yq = repB (leadB P_s) ++ (P_c ++ yq))
          by (unfold P_c; rewrite app_assoc, rep_leadB_dropB; reflexivity).
        rewrite hrw, cfgCollar_repB; f_equal; unfold J_c; lia. }
      rewrite <- hcfg_in, hcfg_out in hstep_tm.
      assert (hjb0 : JBoundsValid (nd_jb (mkChildQS nd ms qs next_jb yq)) u_val j_val).
      { unfold mkChildQS; cbn zeta; cbn [nd_jb]; apply (addJBound_sound hnjb).
        pose proof (nst_khi _ _ _ _ _ _ hst) as hkhi.
        assert (hring_jbq :
          ((Z.of_N (2 * (qs + 2) * ms) - Z.of_N (2 * nd_k_hi_u nd)) * Z.of_N u_val +
           (- (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3)))) - Z.of_N (2 * j_val) =
           2 * (Z.of_N ((ms * u_val) * (qs + 2)) - Z.of_N (k0 + nd_extra_B nd + j_val + 3)) +
           2 * (Z.of_N k0 - (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)))%Z)
          by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
        clear - hdiv hkhi hring_jbq; lia. }
      pose proof (@JBoundsValid_mono_J _ _ _ J_c hjb0 ltac:(unfold J_c; lia)) as hjb_q.
      pose proof (deltaB_leadB_dropB P_s) as hdb_split.
      assert (hns_q : NodeState (mkChildQS nd ms qs next_jb yq) u_val k0 d0 J_c P_c).
      { destruct hst as [_ _ hs6 hdbs _ hpowP _ _ _ hklo hkhi _ _ _ hdb hd1 hd2 hwM_lo hD_lo _ _].
        unfold mkChildQS; cbn zeta; constructor; cbn [
          nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
        - exact (noK1_dropB hno_s).
        - unfold P_c; rewrite countBin_dropB, hcb_s; exact hpowP.
        - intros _; exact (leadB_dropB P_s).
        - pose proof (evalPhi_leadB_dropB 0 P_s) as hd_phi.
          unfold P_c; clear - hd_phi hw_s hmod; lia.
        - pose proof (N.mul_le_mono_r _ _ (leadB P_s) (pow2N_pos (nd_db_shift nd))) as hle_lb.
          assert (hm_add : pow2N (nd_db_shift nd) * deltaB P =
                           pow2N (nd_db_shift nd) * leadB P_s + pow2N (nd_db_shift nd) * deltaB P_c)
            by (unfold P_c; rewrite <- hdb_s, hdb_split; ring).
          unfold J_c; clear - hdb hle_lb hm_add; lia.
        - intros hseq.
          pose proof (hD_lo hseq) as hd0.
          assert (heq_sum : deltaB P_c + J_c = deltaB P + j_val)
            by (unfold P_c, J_c; clear - hdb_split hdb_s; lia).
          rewrite heq_sum; exact hd0. }
      destruct (hcl_q u_val k0 d0 J_c P_c (@JBoundsValid_mono_J _ _ _ J_c hnjb ltac:(unfold J_c; lia)) hns_q)
        as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep_tm) hstar) hinv).
Qed.

#[local] Arguments stepCTInner : simpl never.

Local Lemma stepCTBody_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms qs_hi : N)
    (hs5 : nd_s nd <= 5) (hfr : nd_has_i1_front nd = true) (hms : ms = msOf (nd_s nd)) :
  forall (ct : N) (memo : MemoTree),
    fst (stepCTBody stepFn nd ms qs_hi ct memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (stepCTBody stepFn nd ms qs_hi ct memo)) /\
    (forall u_val k0 d0 j_val (P P_s : list BecTok1),
      NodeState nd u_val k0 d0 j_val P ->
      evalPhi 2 P = ct * (ms * u_val) ->
      noK1 P_s = true ->
      countBin P_s = countBin P ->
      deltaB P_s = deltaB P ->
      evalPhi 0 P_s = (k0 + nd_extra_B nd + j_val + 3) mod (ms * u_val) ->
      2 * (ms * u_val) <= k0 + nd_extra_B nd + j_val + 3 ->
      (k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2 <= qs_hi ->
      (forall yc tyc yq : list BecTok1,
        RelT0Pow ct (nd_Y nd) yc -> RelT M1 yc tyc ->
        RelT0Pow ((k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2) tyc yq ->
        exists W : list BecTok1,
          RelT M1 (P ++ nd_Y nd) W /\
          RelT0Pow (k0 + nd_extra_B nd + j_val + 1) W (P_s ++ yq)) ->
      exists k' tail', nodeCfg nd k0 j_val P -->* cfgCollar k' tail' /\
        (InC0 k' tail' \/ InC1 k' tail')).
Proof.
  intros ct memo hok hm.
  unfold stepCTBody in hok |- *; cbn zeta in hok |- *.
  remember (pow2N (nd_s nd + 1)) as sh2 eqn:Hsh2.
  remember (pow2N (nd_s nd + 2)) as sh4 eqn:Hsh4.
  destruct ((nd_s nd =? nd_db_shift nd) &&
            holdsLinearAllUK 64 (7 - Z.of_N (2 * nd_wj_k nd))%Z
              (Z.of_N (128 * ct + 2 * nd_wj_hi_u nd) - Z.of_N (128 * nd_wRQ nd))%Z
              (2 * nd_wj_hi_c nd)%Z
              (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) eqn:Hpr1.
  - cbn [snd]; split; [exact hm |].
    intros u_val k0 d0 j_val P P_s hst hpsi _ _ _ _ _ _ _.
    apply Bool.andb_true_iff in Hpr1 as [hseq hlin]; apply N.eqb_eq in hseq.
    pose proof (holdsLinearAllUK_sound (nst_U _ _ _ _ _ _ hst) (nst_K64 _ _ _ _ _ _ hst)
                  (nst_klo _ _ _ _ _ _ hst) (nst_khi _ _ _ _ _ _ hst) hlin) as hp.
    pose proof (ct_sh_ident nd ms ct u_val P hs5 hms hpsi) as hident.
    pose proof (nst_hwj _ _ _ _ _ _ hst hfr hseq) as hwj.
    pose proof (nst_wM_lo _ _ _ _ _ _ hst) as hwM.
    rewrite <- Hsh2, <- Hsh4 in hident, hwj.
    assert (hring_pr1 :
      ((7 - Z.of_N (2 * nd_wj_k nd)) * Z.of_N k0 +
       (Z.of_N (128 * ct + 2 * nd_wj_hi_u nd) - Z.of_N (128 * nd_wRQ nd)) * Z.of_N u_val +
       2 * nd_wj_hi_c nd =
       (Z.of_N (7 * k0 + 4 * d0) - Z.of_N (128 * nd_wRQ nd * u_val)) +
       (Z.of_N (sh2 * evalPhi 0 P) + Z.of_N (sh4 * deltaB P) +
        Z.of_N (2 * nd_wj_hi_u nd * u_val) + 2 * nd_wj_hi_c nd -
        (Z.of_N (4 * d0) + Z.of_N (2 * nd_wj_k nd * k0))) +
       (Z.of_N (128 * ct * u_val) - Z.of_N (sh2 * evalPhi 0 P + sh4 * deltaB P)))%Z)
      by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
    exfalso; clear - hp hwM hwj hident hring_pr1; lia.
  - destruct ((nd_s nd =? nd_db_shift nd) &&
              holdsLinearAllUK 64 (7 - Z.of_N sh4)%Z
                (Z.of_N (128 * ct + sh2 * nd_kj_hi_u nd) - Z.of_N (128 * nd_wRQ nd))%Z
                (Z.of_N sh2 * nd_kj_hi_c nd)%Z
                (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)) eqn:Hpr2.
    + cbn [snd]; split; [exact hm |].
      intros u_val k0 d0 j_val P P_s hst hpsi _ _ _ _ _ _ _.
      apply Bool.andb_true_iff in Hpr2 as [hseq hlin]; apply N.eqb_eq in hseq.
      pose proof (holdsLinearAllUK_sound (nst_U _ _ _ _ _ _ hst) (nst_K64 _ _ _ _ _ _ hst)
                    (nst_klo _ _ _ _ _ _ hst) (nst_khi _ _ _ _ _ _ hst) hlin) as hp.
      pose proof (ct_4d_bound nd ms ct u_val k0 d0 j_val P hs5 hms hst hseq hpsi) as hwM2.
      pose proof (nst_kj _ _ _ _ _ _ hst hfr) as hkj.
      pose proof (Z.mul_le_mono_nonneg_l _ _ (Z.of_N sh2) ltac:(lia) hkj) as hkj_sh.
      assert (hsh4_2sh2 : sh4 = 2 * sh2)
        by (rewrite Hsh4; replace (nd_s nd + 2) with ((nd_s nd + 1) + 1) by lia;
            rewrite pow2N_succ, <- Hsh2; reflexivity).
      rewrite <- Hsh4 in hwM2.
      rewrite hsh4_2sh2 in hp, hwM2.
      assert (hring_pr2 :
        ((7 - Z.of_N (2 * sh2)) * Z.of_N k0 +
         (Z.of_N (128 * ct + sh2 * nd_kj_hi_u nd) - Z.of_N (128 * nd_wRQ nd)) * Z.of_N u_val +
         Z.of_N sh2 * nd_kj_hi_c nd =
         (Z.of_N (7 * k0 + 128 * ct * u_val + (2 * sh2) * j_val) -
          Z.of_N (128 * nd_wRQ nd * u_val)) +
         (Z.of_N sh2 * (Z.of_N (nd_kj_hi_u nd * u_val) + nd_kj_hi_c nd) -
          Z.of_N sh2 * Z.of_N (2 * (k0 + j_val))))%Z)
        by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
      exfalso; clear - hp hwM2 hkj_sh hring_pr2; lia.
    + destruct (t0PowNorm wordFuel ct (nd_Y nd)) as [yc |] eqn:Hyc; [| discriminate hok].
      destruct (t1Norm wordFuel yc) as [tyc |] eqn:Htyc; [| discriminate hok].
      exact (stepCTInner_sound stepFn hstep nd ms qs_hi sh2 sh4 ct hs5 hfr hms Hsh2 Hsh4
               yc tyc (t0PowNorm_sound Hyc) (t1Norm_sound Htyc) (t1Norm_noTrailZero Htyc)
               memo hok hm).
Qed.

#[local] Arguments stepCTBody : simpl never.
#[local] Arguments verifyWaveI0 : simpl never.

Local Lemma verifyWaveI1_sound (stepFn : SymWaveNode -> MemoTree -> bool * MemoTree)
    (hstep : forall x m, fst (stepFn x m) = true -> MemoValid NodeClosed m ->
               NodeClosed x /\ MemoValid NodeClosed (snd (stepFn x m)))
    (nd : SymWaveNode) (ms ms_next two_d_hi_u : N) (memo : MemoTree)
    (hkhic : (nd_k_hi_c nd <= 0)%Z) (htz : noTrailZero (nd_Y nd) = true)
    (hs5 : nd_s nd <= 5) (hfr : nd_has_i1_front nd = true)
    (hms_eq : ms = msOf (nd_s nd)) (hmsn_eq : ms_next = msOf (nd_s nd + 1))
    (h2d_eq : two_d_hi_u = twoDInitHiU nd)
    (hok : fst (verifyWaveI1 stepFn nd ms ms_next two_d_hi_u memo) = true)
    (hm : MemoValid NodeClosed memo) :
  NodeClosed nd /\ MemoValid NodeClosed (snd (verifyWaveI1 stepFn nd ms ms_next two_d_hi_u memo)).
Proof.
  assert (hms_pos : 0 < ms) by (rewrite hms_eq; apply msOf_pos; lia).
  assert (hmsn_pos : 0 < ms_next) by (rewrite hmsn_eq; apply msOf_pos; lia).
  assert (hms_dbl : 2 * ms_next = ms) by (rewrite hms_eq, hmsn_eq; apply msOf_succ; lia).
  unfold verifyWaveI1 in hok |- *; cbn zeta in hok |- *.
  destruct (negb (holdsLinearAllUK 64 (-1)%Z (Z.of_N (2 * ms)) (- Z.of_N (nd_extra_B nd + 3))%Z
                   (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd))) eqn:Hg_2ms;
    [discriminate hok |].
  apply Bool.negb_false_iff in Hg_2ms.
  remember (floorMinU1
              (Z.of_N (nd_k_lo_u nd) - Z.of_N (ms + ms_next))%Z
              (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 4))%Z ms_next) as qa_lo eqn:Hqalo.
  remember (floorMaxU1
              (Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd))
              (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd)) + nd_w_hi_c nd)%Z
              (2 * ms_next)) as qa_hi eqn:Hqahi.
  destruct ((qa_lo <=? qa_hi) && (4096 <? qa_hi - qa_lo)); [discriminate hok |].
  remember (computeCntA nd ms_next qa_lo qa_hi) as cntA0 eqn:HcntA.
  destruct (runRange 13%nat (stepQABody stepFn nd ms_next) qa_lo cntA0 memo) as [okA memoA] eqn:HpA.
  destruct okA; [cbn [negb] in hok |- * | discriminate hok].
  destruct (runRange_sound (stepQABody stepFn nd ms_next)
              (stepQABody_sound stepFn hstep nd ms_next htz)
              13%nat qa_lo cntA0 memo ltac:(rewrite HpA; reflexivity) hm) as [hmemoA hqa_loop].
  rewrite HpA in hmemoA; cbn [snd] in hmemoA.
  assert (hqa_all : forall qa : N, qa_lo <= qa -> qa <= qa_hi ->
      exists ya : list BecTok1,
        RelT0Pow qa (nd_Y nd) ya /\ noTrailZero ya = true /\
        NodeClosed (mkChildQA nd ms_next ya)).
  { intros qa hqlo hqhi.
    pose proof HcntA as HcntA_u; unfold computeCntA in HcntA_u.
    assert (hqa_lt_f : (qa_hi <? qa_lo) = false) by (apply N.ltb_ge; clear - hqlo hqhi; lia).
    rewrite hqa_lt_f in HcntA_u.
    destruct (findL0Anchor 7%nat (nd_Y nd) qa_lo qa_hi) as [[[qa0 wya0] pya0] |] eqn:HancA.
    - cbn zeta in HcntA_u.
      set (nx_hi := mkWaveNode
        (nd_s nd + 1) (nd_db_shift nd) false
        (nd_k_lo_u nd) (nd_k_lo_c nd) (nd_k_hi_u nd) (nd_k_hi_c nd)
        0 0%Z ms_next (-1)%Z
        (nd_extra_B nd + 1) (nd_scaled_db_u nd + pow2N (nd_db_shift nd) * ms_next) (nd_scaled_db_c nd)
        (nd_kj_hi_u nd) (nd_kj_hi_c nd) (nd_wj_k nd) (nd_wj_hi_u nd) (nd_wj_hi_c nd)
        (nd_jb nd) (nd_Y nd) (nd_wRQ nd) (nd_pRQ nd)) in HcntA_u.
      destruct (checkAbstract nx_hi true true (wya0 + (qa_hi - qa0)) (pya0 + (qa_hi - qa0))) eqn:Ha_hi.
      + destruct (N.lt_ge_cases qa qa0) as [hlt | hge].
        * exact (hqa_loop qa hqlo ltac:(rewrite HcntA_u; clear - hqlo hlt; lia)).
        * destruct (findL0Anchor_sound 7%nat (nd_Y nd) qa_lo qa_hi qa0 wya0 pya0 htz HancA)
            as [_ [_ [y0 [hy0_rel [hy0_no [hy0_tz [hy0_I [hwy0 hpy0]]]]]]]].
          set (ya := t0Pow (qa - qa0) y0).
          assert (hrel : RelT0Pow qa (nd_Y nd) ya)
            by (replace qa with (qa0 + (qa - qa0)) by (clear - hge; lia);
                exact (RelT0Pow_trans hy0_rel (RelT0Pow_t0Pow _ hy0_no))).
          pose proof (noK1_t0Pow (qa - qa0) hy0_no) as hno; fold ya in hno.
          pose proof (noTrailZero_t0Pow (qa - qa0) hy0_no hy0_tz) as htz_ya; fold ya in htz_ya.
          pose proof (hasI_t0Pow (qa - qa0) hy0_no hy0_I) as hI_ya; fold ya in hI_ya.
          assert (hwy : evalPhi 0 ya <= wya0 + (qa_hi - qa0))
            by (unfold ya; rewrite (evalPhi_t0Pow 0 _ hy0_no), hwy0; clear - hqhi hge; lia).
          assert (hpy : evalPhi 22 ya <= pya0 + (qa_hi - qa0))
            by (unfold ya; rewrite (evalPhi_t0Pow 22 _ hy0_no), hpy0; clear - hqhi hge; lia).
          assert (hchk_ya : checkAbstract (mkChildQA nd ms_next ya) true true
                              (wya0 + (qa_hi - qa0)) (pya0 + (qa_hi - qa0)) = true).
          { exact (checkAbstract_mono nx_hi (mkChildQA nd ms_next ya) true true _ _ _ _
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              (fun h => h) (N.le_refl _) (N.le_refl _) (JBoundsLe_refl _) Ha_hi). }
          exists ya; split; [exact hrel | split; [exact htz_ya |]].
          intros u_val k0 d0 j_c P_c hns.
          exact (checkAbstract_sound hns hno (fun _ => hI_ya) hwy hpy hchk_ya).
      + exact (hqa_loop qa hqlo ltac:(rewrite HcntA_u; clear - hqlo hqhi; lia)).
    - exact (hqa_loop qa hqlo ltac:(rewrite HcntA_u; clear - hqlo hqhi; lia)). }
  remember (pow2N (nd_db_shift nd)) as sh eqn:Hsh.
  remember (floorMaxU1
              (Z.of_N ((two_d_hi_u + 2 * nd_scaled_db_u nd) / sh + 1 + nd_w_hi_u nd))
              (nd_w_hi_c nd + Z.of_N ((2 * nd_scaled_db_c nd) / sh + 1))%Z ms) as ctot_max eqn:Hctot.
  destruct (4096 <? ctot_max); [discriminate hok |].
  remember ((two_d_hi_u + 1) / 2) as d_hi_u eqn:Hdhi.
  remember ((floorMaxU1
               (Z.of_N (nd_k_hi_u nd + d_hi_u + nd_scaled_db_u nd))
               (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd))%Z ms) - 2)
    as qs_hi_1 eqn:Hqshi1.
  remember ((floorMaxU1
               (Z.of_N (nd_kj_hi_u nd))
               (nd_kj_hi_c nd + Z.of_N (2 * (nd_extra_B nd + 3)))%Z (2 * ms)) - 2)
    as qs_hi_2 eqn:Hqshi2.
  remember (N.min qs_hi_1 qs_hi_2) as qs_hi eqn:Hqshi.
  destruct (runRange 13%nat (stepCTBody stepFn nd ms qs_hi) 0 (ctot_max + 1) memoA)
    as [okC memoC] eqn:HpC.
  destruct okC; [| discriminate hok].
  destruct (runRange_sound (stepCTBody stepFn nd ms qs_hi)
              (stepCTBody_sound stepFn hstep nd ms qs_hi hs5 hfr hms_eq)
              13%nat 0 (ctot_max + 1) memoA ltac:(rewrite HpC; reflexivity) hmemoA)
    as [hmemoC hct_loop].
  rewrite HpC in hmemoC; cbn [snd] in hmemoC |- *.
  assert (hcl_nd : NodeClosed nd).
  { intros u_val k0 d0 j_val P hst.
    pose proof (nst_U _ _ _ _ _ _ hst) as hU.
    pose proof (nst_K64 _ _ _ _ _ _ hst) as hK64.
    pose proof (nst_noP _ _ _ _ _ _ hst) as hnoP.
    assert (hpowP : 2 ^ countBin P = ms * u_val)
      by (rewrite (nst_powP _ _ _ _ _ _ hst), hms_eq; reflexivity).
    assert (hm_ge1 : 1 <= countBin P).
    { assert (hm2 : 2 <= ms).
      { rewrite hms_eq.
        assert (nd_s nd = 0 \/ nd_s nd = 1 \/ nd_s nd = 2 \/ nd_s nd = 3 \/ nd_s nd = 4 \/ nd_s nd = 5)
          as [e | [e | [e | [e | [e | e]]]]] by (clear - hs5; lia); rewrite e; cbn; lia. }
      assert (h2 : 2 <= 2 ^ countBin P) by (rewrite hpowP; clear - hm2 hU; nia).
      destruct (N.eq_dec (countBin P) 0) as [hc0 | hc1]; [rewrite hc0 in h2; cbn in h2; lia | lia]. }
    assert (h2ms : 2 * (ms * u_val) <= k0 + nd_extra_B nd + j_val + 3).
    { pose proof (holdsLinearAllUK_sound hU hK64 (nst_klo _ _ _ _ _ _ hst)
                    (nst_khi _ _ _ _ _ _ hst) Hg_2ms) as hp.
      rewrite <- N2Z.inj_mul in hp.
      replace ((2 * ms) * u_val) with (2 * (ms * u_val)) in hp by ring.
      clear - hp; lia. }
    pose proof (twoDInitHiU_sound nd u_val k0 d0 hU (nst_khi _ _ _ _ _ _ hst) hkhic
                  (nst_d1 _ _ _ _ _ _ hst) (nst_d2 _ _ _ _ _ _ hst)) as h2d.
    rewrite <- h2d_eq in h2d.
    destruct (prefix_wave_dichotomy_aux (countBin P) (countB P) P
                (k0 + nd_extra_B nd + j_val + 1) hm_ge1 eq_refl eq_refl hnoP
                ltac:(rewrite hpowP; clear - h2ms; lia))
      as [[P_next [dJ [qa [hno_n [hcb_n [hdb_n [hlo_n [hhi_n hstep_n]]]]]]]] |
          [P_s [ct [hpsi_s [hno_s [hcb_s [hdb_s [hw_s hstep_s]]]]]]]].
    - (* Form 1: Absorbed -> hqa_all *)
      assert (hpow_m1 : 2 ^ (countBin P - 1) = ms_next * u_val).
      { assert (hp1 : 2 ^ countBin P = 2 * (2 ^ (countBin P - 1)))
          by (replace (countBin P) with ((countBin P - 1) + 1) at 1 by (clear - hm_ge1; lia);
              exact (pow2_succ _)).
        rewrite hpowP, <- hms_dbl in hp1; clear - hp1; lia. }
      rewrite hpow_m1 in hdb_n, hlo_n.
      rewrite hpowP in hhi_n.
      assert (hqa_lo : qa_lo <= qa).
      { rewrite Hqalo; apply (floorMinU1_le _ _ ms_next u_val qa hU hmsn_pos).
        pose proof (nst_klo _ _ _ _ _ _ hst) as hklo.
        assert (hmsnU_pos : 1 <= ms_next * u_val) by (clear - hmsn_pos hU; nia).
        replace (ms + ms_next) with (3 * ms_next) by (clear - hms_dbl; lia).
        assert (hring_qalo :
          ((Z.of_N (nd_k_lo_u nd) - Z.of_N (3 * ms_next)) * Z.of_N u_val +
           (nd_k_lo_c nd + Z.of_N (nd_extra_B nd + 4)) -
           Z.of_N (ms_next * u_val * (qa + 1)) =
           (Z.of_N (nd_k_lo_u nd * u_val) + nd_k_lo_c nd - Z.of_N k0) +
           (Z.of_N ((k0 + nd_extra_B nd + j_val + 1) + 3) -
            Z.of_N ((ms_next * u_val) * (qa + 3))) -
           Z.of_N j_val - Z.of_N (ms_next * u_val))%Z)
          by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
        clear - hklo hlo_n hmsnU_pos hring_qalo; lia. }
      assert (hqa_hi : qa <= qa_hi).
      { rewrite Hqahi; apply (floorMaxU1_ge _ _ (2 * ms_next) u_val qa hU ltac:(lia)).
        pose proof (evalPhi_eq_zero_add_deltaB 2 P) as he2.
        pose proof (nst_db _ _ _ _ _ _ hst) as hdb.
        pose proof (nst_khi _ _ _ _ _ _ hst) as hkhi.
        pose proof (nst_whi _ _ _ _ _ _ hst) as hwhi.
        pose proof (N.mul_le_mono_r _ _ (deltaB P) (pow2N_pos (nd_db_shift nd))) as hsh_le.
        assert (hdb_le : deltaB P + j_val <= d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd)
          by (clear - hdb hsh_le; lia).
        rewrite hms_dbl.
        assert (hring_qahi :
          (Z.of_N ((ms * u_val) * qa) -
           (Z.of_N (2 * nd_k_hi_u nd + nd_w_hi_u nd + two_d_hi_u + 2 * nd_scaled_db_u nd) * Z.of_N u_val +
            (2 * (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd)) + nd_w_hi_c nd)) =
           (Z.of_N ((ms * u_val) * qa) -
            Z.of_N (2 * (k0 + nd_extra_B nd + j_val + 1) + 2 + evalPhi 2 P)) +
           (Z.of_N (evalPhi 2 P) - Z.of_N (evalPhi 0 P + 2 * deltaB P)) +
           2 * (Z.of_N k0 - (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)) +
           (Z.of_N (evalPhi 0 P) - (Z.of_N (nd_w_hi_u nd * u_val) + nd_w_hi_c nd)) +
           2 * (Z.of_N (deltaB P + j_val) -
                Z.of_N (d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd)) +
           (Z.of_N (2 * d0) - Z.of_N (two_d_hi_u * u_val)) - 2)%Z)
          by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
        clear - hhi_n he2 hkhi hwhi hdb_le h2d hring_qahi; lia. }
      destruct (hqa_all qa hqa_lo hqa_hi) as [ya [hya_rel [hya_tz hcl_ya]]].
      destruct (hstep_n (nd_Y nd) ya hya_rel) as [W [ht1_W hpow_W]].
      pose proof (@collar_step_inC1_pow_raw (k0 + nd_extra_B nd + j_val)
                    (P ++ nd_Y nd) W (repB dJ ++ (P_next ++ ya))
                    ltac:(clear - hK64; lia) ht1_W hpow_W) as hstep_tm.
      set (J_c := j_val + dJ + leadB P_next).
      set (P_c := dropB P_next).
      assert (hcfg_in : nodeCfg nd k0 j_val P =
                        cfgCollar (k0 + nd_extra_B nd + j_val) (TokI :: Tok1 :: (P ++ nd_Y nd)))
        by (unfold nodeCfg; rewrite hfr; reflexivity).
      assert (hcfg_out : cfgCollar (k0 + nd_extra_B nd + j_val + 1) (repB dJ ++ (P_next ++ ya)) =
                         nodeCfg (mkChildQA nd ms_next ya) k0 J_c P_c).
      { unfold nodeCfg, mkChildQA; cbn [nd_extra_B nd_has_i1_front nd_Y].
        assert (h1 : P_next ++ ya = repB (leadB P_next) ++ (P_c ++ ya))
          by (unfold P_c; rewrite app_assoc, rep_leadB_dropB; reflexivity).
        rewrite h1, app_assoc, <- repB_add, cfgCollar_repB; f_equal; unfold J_c; lia. }
      rewrite <- hcfg_in, hcfg_out in hstep_tm.
      pose proof (deltaB_leadB_dropB P_next) as hdb_split.
      assert (hns_ya : NodeState (mkChildQA nd ms_next ya) u_val k0 d0 J_c P_c).
      { destruct hst as [_ _ _ hdbs _ _ _ _ _ hklo hkhi _ _ hjb hdb hd1 hd2 hwM_lo _ _ _].
        constructor; cbn [
          mkChildQA nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
          nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
          nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
          try assumption; try (intros h; discriminate h);
          match goal with
          | |- (_ <= _)%N => try (clear - hs5 hdbs; lia)
          | |- (_ <= _)%Z => try (clear; lia)
          | _ => idtac
          end.
        - exact (noK1_dropB hno_n).
        - unfold P_c; rewrite <- hmsn_eq, countBin_dropB, hcb_n, hpow_m1; reflexivity.
        - intros _; exact (leadB_dropB P_next).
        - pose proof (evalPhi_leadB_dropB 0 P_next) as hd_phi.
          pose proof (evalPhi_zero_lt_pow_countBin P_next) as hlt_p.
          rewrite hcb_n, hpow_m1 in hlt_p.
          unfold P_c; clear - hd_phi hlt_p; lia.
        - exact (@JBoundsValid_mono_J _ _ _ J_c hjb ltac:(unfold J_c; lia)).
        - rewrite <- Hsh in hdb |- *.
          assert (hsh_pos : 1 <= sh) by (rewrite Hsh; exact (pow2N_pos (nd_db_shift nd))).
          pose proof (N.mul_le_mono_r 1 sh (dJ + leadB P_next) hsh_pos) as hle_dj.
          pose proof (N.mul_le_mono_l _ _ sh hdb_n) as hmul_n.
          assert (hdist1 : sh * (deltaB P_next + dJ) = sh * deltaB P_c + sh * (dJ + leadB P_next))
            by (unfold P_c; rewrite hdb_split; ring).
          assert (hdist2 : sh * (deltaB P + ms_next * u_val) + nd_scaled_db_u nd * u_val =
                           sh * deltaB P + (nd_scaled_db_u nd + sh * ms_next) * u_val)
            by ring.
          unfold J_c; clear - hdb hle_dj hmul_n hdist1 hdist2; lia.
        - intros h; clear - hdbs h; lia. }
      destruct (hcl_ya u_val k0 d0 J_c P_c hns_ya) as [k' [tail' [hstar hinv]]].
      exists k', tail'; exact (conj (etrans (p_to_e hstep_tm) hstar) hinv).
    - (* Form 2: Swept -> hct_loop *)
      rewrite hpowP in hpsi_s, hw_s, hstep_s.
      replace ((k0 + nd_extra_B nd + j_val + 1) + 2) with (k0 + nd_extra_B nd + j_val + 3) in hw_s, hstep_s
        by lia.
      assert (hct_le : ct <= ctot_max).
      { rewrite Hctot; apply (floorMaxU1_ge _ _ ms u_val ct hU hms_pos).
        pose proof (evalPhi_eq_zero_add_deltaB 2 P) as he2.
        pose proof (nst_db _ _ _ _ _ _ hst) as hdb.
        pose proof (nst_whi _ _ _ _ _ _ hst) as hwhi.
        rewrite <- Hsh in hdb.
        assert (hsh_pos : 0 < sh) by (rewrite Hsh; pose proof (pow2N_pos (nd_db_shift nd)); lia).
        set (a_hi := two_d_hi_u + 2 * nd_scaled_db_u nd).
        set (c_hi := 2 * nd_scaled_db_c nd).
        destruct (div_mod_spec a_hi sh hsh_pos) as [qA [rA [hqA [_ [hdivA hmodA]]]]].
        destruct (div_mod_spec c_hi sh hsh_pos) as [qC [rC [hqC [_ [hdivC hmodC]]]]].
        fold a_hi in hqA; fold c_hi in hqC; rewrite hqA, hqC.
        assert (hsh_2db : sh * (2 * deltaB P) <= a_hi * u_val + c_hi).
        { assert (hr1 : sh * (2 * deltaB P) = 2 * (sh * deltaB P)) by ring.
          assert (hr2 : a_hi * u_val = two_d_hi_u * u_val + 2 * (nd_scaled_db_u nd * u_val))
            by (unfold a_hi; ring).
          unfold c_hi; clear - hdb h2d hr1 hr2; lia. }
        assert (hAU : a_hi <= sh * (qA + 1))
          by (replace (sh * (qA + 1)) with (sh * qA + sh) by ring; clear - hdivA hmodA; lia).
        pose proof (N.mul_le_mono_r _ _ u_val hAU) as hAU2.
        assert (hCU : c_hi < sh * (qC + 1))
          by (replace (sh * (qC + 1)) with (sh * qC + sh) by ring; clear - hdivC hmodC; lia).
        assert (hlt_sh : sh * (2 * deltaB P) < sh * ((qA + 1) * u_val + (qC + 1))).
        { replace (sh * ((qA + 1) * u_val + (qC + 1)))
            with ((sh * (qA + 1)) * u_val + sh * (qC + 1)) by ring.
          clear - hsh_2db hAU2 hCU; lia. }
        pose proof (n_le_of_pos_mul_lt hlt_sh) as h2db_lt.
        assert (hpsi_eq2 : (ms * u_val) * ct = evalPhi 0 P + 2 * deltaB P)
          by (rewrite N.mul_comm, <- hpsi_s, he2; reflexivity).
        assert (hring_ct :
          (Z.of_N ((ms * u_val) * ct) -
           (Z.of_N (qA + 1 + nd_w_hi_u nd) * Z.of_N u_val + (nd_w_hi_c nd + Z.of_N (qC + 1))) =
           (Z.of_N (evalPhi 0 P) - (Z.of_N (nd_w_hi_u nd * u_val) + nd_w_hi_c nd)) +
           (Z.of_N (2 * deltaB P) - Z.of_N ((qA + 1) * u_val + (qC + 1))) +
           (Z.of_N ((ms * u_val) * ct) - Z.of_N (evalPhi 0 P + 2 * deltaB P)))%Z)
          by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
        clear - hwhi h2db_lt hpsi_eq2 hring_ct; lia. }
      remember ((k0 + nd_extra_B nd + j_val + 3) / (ms * u_val) - 2) as qs eqn:Hqs_def.
      assert (hqs_hi : qs <= qs_hi).
      { assert (hmsU_pos : 0 < ms * u_val) by (clear - hms_pos hU; nia).
        destruct (div_mod_spec (k0 + nd_extra_B nd + j_val + 3) (ms * u_val) hmsU_pos)
          as [d_qs [rem_qs [hd_qs [_ [hdiv hmod]]]]].
        assert (hge2 : 2 <= d_qs).
        { destruct (N.lt_ge_cases d_qs 2) as [hlt2 | hge2]; [| exact hge2].
          assert (d_qs = 0 \/ d_qs = 1) as [-> | ->] by lia;
            clear - h2ms hdiv hmod; lia. }
        rewrite hd_qs in Hqs_def.
        assert (hd_eq : d_qs = qs + 2) by (clear - Hqs_def hge2; lia).
        rewrite hd_eq in hdiv.
        assert (h1 : qs <= qs_hi_1).
        { assert (hge1 : qs + 2 <= floorMaxU1
                           (Z.of_N (nd_k_hi_u nd + d_hi_u + nd_scaled_db_u nd))
                           (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd))%Z ms).
          { apply (floorMaxU1_ge _ _ ms u_val (qs + 2) hU hms_pos).
            pose proof (nst_khi _ _ _ _ _ _ hst) as hkhi.
            pose proof (nst_db _ _ _ _ _ _ hst) as hdb.
            pose proof (N.mul_le_mono_r _ _ (deltaB P) (pow2N_pos (nd_db_shift nd))) as hsh_le.
            assert (hJ_le : j_val <= d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd)
              by (clear - hdb hsh_le; lia).
            assert (hd_le : d0 <= d_hi_u * u_val).
            { destruct (div_mod_spec (two_d_hi_u + 1) 2 ltac:(lia))
                as [qd [rd [hqd [_ [hd_div hd_mod]]]]].
              rewrite <- Hdhi in hqd; subst qd.
              assert (h2_dhi : two_d_hi_u <= 2 * d_hi_u) by (clear - hd_div hd_mod; lia).
              pose proof (N.mul_le_mono_r _ _ u_val h2_dhi) as h2u.
              replace ((2 * d_hi_u) * u_val) with (2 * (d_hi_u * u_val)) in h2u by ring.
              clear - h2d h2u; lia. }
            assert (hring_qs1 :
              (Z.of_N (ms * u_val * (qs + 2)) -
               (Z.of_N (nd_k_hi_u nd + d_hi_u + nd_scaled_db_u nd) * Z.of_N u_val +
                (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd))) =
               (Z.of_N ((ms * u_val) * (qs + 2)) - Z.of_N (k0 + nd_extra_B nd + j_val + 3)) +
               (Z.of_N k0 - (Z.of_N (nd_k_hi_u nd * u_val) + nd_k_hi_c nd)) +
               (Z.of_N j_val - Z.of_N (d0 + nd_scaled_db_u nd * u_val + nd_scaled_db_c nd)) +
               (Z.of_N d0 - Z.of_N (d_hi_u * u_val)))%Z)
              by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
            clear - hdiv hkhi hJ_le hd_le hring_qs1; lia. }
          rewrite Hqshi1.
          remember (floorMaxU1
            (Z.of_N (nd_k_hi_u nd + d_hi_u + nd_scaled_db_u nd))
            (nd_k_hi_c nd + Z.of_N (nd_extra_B nd + 3 + nd_scaled_db_c nd))%Z ms) as fm1.
          clear - hge1; lia. }
        assert (h2 : qs <= qs_hi_2).
        { assert (hge2_fm : qs + 2 <= floorMaxU1
                              (Z.of_N (nd_kj_hi_u nd))
                              (nd_kj_hi_c nd + Z.of_N (2 * (nd_extra_B nd + 3)))%Z (2 * ms)).
          { apply (floorMaxU1_ge _ _ (2 * ms) u_val (qs + 2) hU ltac:(lia)).
            pose proof (nst_kj _ _ _ _ _ _ hst hfr) as hkj.
            assert (hring_qs2 :
              (Z.of_N ((2 * ms) * u_val * (qs + 2)) -
               (Z.of_N (nd_kj_hi_u nd) * Z.of_N u_val +
                (nd_kj_hi_c nd + Z.of_N (2 * (nd_extra_B nd + 3)))) =
               2 * (Z.of_N ((ms * u_val) * (qs + 2)) - Z.of_N (k0 + nd_extra_B nd + j_val + 3)) +
               (Z.of_N (2 * (k0 + j_val)) - (Z.of_N (nd_kj_hi_u nd * u_val) + nd_kj_hi_c nd)))%Z)
              by (repeat (rewrite N2Z.inj_mul || rewrite N2Z.inj_add); ring).
            clear - hdiv hkj hring_qs2; lia. }
          rewrite Hqshi2.
          remember (floorMaxU1
            (Z.of_N (nd_kj_hi_u nd))
            (nd_kj_hi_c nd + Z.of_N (2 * (nd_extra_B nd + 3)))%Z (2 * ms)) as fm2.
          clear - hge2_fm; lia. }
        rewrite Hqshi; clear - h1 h2; lia. }
      subst qs.
      exact (hct_loop ct ltac:(lia) ltac:(clear - hct_le; lia) u_val k0 d0 j_val P P_s
               hst hpsi_s hno_s hcb_s hdb_s hw_s h2ms hqs_hi (hstep_s (nd_Y nd))). }
  exact (conj hcl_nd (memoInsert_sound hmemoC hcl_nd)).
Qed.

#[local] Arguments verifyWaveI1 : simpl never.

Local Lemma verifyWaveNode_sound :
  forall (fuel : nat) (nd0 : SymWaveNode) (memo : MemoTree),
    fst (verifyWaveNode fuel nd0 memo) = true ->
    MemoValid NodeClosed memo ->
    NodeClosed nd0 /\ MemoValid NodeClosed (snd (verifyWaveNode fuel nd0 memo)).
Proof.
  induction fuel as [| fuel' IH]; intros nd0 memo hok hm; [discriminate hok |].
  cbn [verifyWaveNode] in hok |- *; cbn zeta in hok |- *.
  set (nd := canonNode nd0) in *.
  assert (lift_cl : NodeClosed nd -> NodeClosed nd0).
  { intros hcl u_val k0 d0 j_val P hst.
    rewrite <- (canonNode_cfg nd0 k0 j_val P).
    exact (hcl u_val k0 d0 j_val P (canonNode_state hst)). }
  destruct (negb (nd_k_hi_c nd <=? 0)%Z || (nd_extra_B nd =? 0)) eqn:Hg1; [discriminate hok |].
  apply Bool.orb_false_iff in Hg1 as [hkhic_b _].
  apply Bool.negb_false_iff in hkhic_b; apply Z.leb_le in hkhic_b.
  destruct (nd_has_i1_front nd && (nd_s nd =? nd_db_shift nd) &&
            negb (nd_wj_k nd =? pow2N (nd_s nd))); [discriminate hok |].
  set (yL0 := noK1 (nd_Y nd)) in *.
  set (yHI := hasI (nd_Y nd)) in *.
  set (wy := if yL0 then evalPhi 0 (nd_Y nd) else 0) in *.
  set (py := if yL0 then evalPhi 22 (nd_Y nd) else 0) in *.
  destruct (yL0 && checkAbstract nd true yHI wy py) eqn:Habs.
  - apply Bool.andb_true_iff in Habs as [hyL0 hchk].
    assert (hwy_eq : wy = evalPhi 0 (nd_Y nd)) by (unfold wy; rewrite hyL0; reflexivity).
    assert (hpy_eq : py = evalPhi 22 (nd_Y nd)) by (unfold py; rewrite hyL0; reflexivity).
    assert (hcl_nd : NodeClosed nd).
    { intros u_val k0 d0 j_val P hst.
      refine (checkAbstract_sound hst hyL0 (fun h => h) _ _ hchk);
        [rewrite hwy_eq; lia | rewrite hpy_eq; lia]. }
    exact (conj (lift_cl hcl_nd) hm).
  - destruct (memoContains memo nd) eqn:Hmem.
    + exact (conj (lift_cl (memoContains_sound hm Hmem)) hm).
    + destruct (isEmptyWord (nd_Y nd) || negb (noTrailZero (nd_Y nd))) eqn:Hg3; [discriminate hok |].
      apply Bool.orb_false_iff in Hg3 as [_ htz]; apply Bool.negb_false_iff in htz.
      destruct ((6 <=? nd_s nd) || (negb (nd_has_i1_front nd) && (5 <=? nd_s nd))) eqn:Hg4;
        [discriminate hok |].
      apply Bool.orb_false_iff in Hg4 as [hs6_f hs5_i0].
      apply N.leb_gt in hs6_f; assert (hs5 : nd_s nd <= 5) by lia.
      destruct (nd_has_i1_front nd) eqn:Hfr; cbn [negb] in hok, hs5_i0 |- *.
      * destruct (verifyWaveI1_sound (verifyWaveNode fuel') IH nd
                    (msOf (nd_s nd)) (msOf (nd_s nd + 1)) (twoDInitHiU nd) memo
                    hkhic_b htz hs5 Hfr eq_refl eq_refl eq_refl hok hm) as [hcl_nd hm'].
        exact (conj (lift_cl hcl_nd) hm').
      * cbn [andb] in hs5_i0; apply N.leb_gt in hs5_i0; assert (hs4 : nd_s nd <= 4) by lia.
        destruct (verifyWaveI0_sound (verifyWaveNode fuel') IH nd
                    (msOf (nd_s nd)) (msOf (nd_s nd + 1)) (twoDInitHiU nd) memo
                    hkhic_b htz hs4 Hfr eq_refl eq_refl eq_refl hok hm) as [hcl_nd hm'].
        exact (conj (lift_cl hcl_nd) hm').
Qed.

#[local] Arguments verifyWaveNode : simpl never.

Local Lemma checkRoot_sound (r : SymWaveNode) (memo : MemoTree)
    (hok : fst (checkRoot r memo) = true) (hm : MemoValid NodeClosed memo) :
  NodeClosed r /\ MemoValid NodeClosed (snd (checkRoot r memo)).
Proof.
  exact (verifyWaveNode_sound 13%nat r memo hok hm).
Qed.

#[local] Arguments checkRoot : simpl never.

Local Lemma evalPhi_zero_dropB (w : list BecTok1) : evalPhi 0 (dropB w) = evalPhi 0 w.
Proof.
  pose proof (evalPhi_leadB_dropB 0 w); lia.
Qed.

Local Lemma checkOneRQSlabs_sound :
  forall (rem : nat) (rq : list BecTok1) (wrq prq global_klo_u : N)
    (global_klo_c : Z) (memo : MemoTree),
    (rem <= 8)%nat ->
    wrq = evalPhi 0 rq -> prq = evalPhi 22 rq ->
    64 <= global_klo_u ->
    ((global_klo_u = 64 /\ global_klo_c = (-1)%Z) \/ global_klo_c = 1%Z) ->
    fst (checkOneRQSlabs rem rq wrq prq global_klo_u global_klo_c memo) = true ->
    MemoValid NodeClosed memo ->
    MemoValid NodeClosed (snd (checkOneRQSlabs rem rq wrq prq global_klo_u global_klo_c memo)) /\
    (forall (u_val k0 d0 : N) (PQ : list BecTok1),
      1 <= u_val -> 64 <= k0 ->
      noK1 PQ = true -> 2 ^ countBin PQ = 64 * u_val ->
      evalPhi 0 PQ + 64 * u_val = k0 + 1 ->
      deltaB PQ = d0 ->
      2 * d0 <= 64 * wrq * u_val ->
      20 * d0 + 64 * prq * u_val + 1 <= 52 * k0 ->
      128 * wrq * u_val + 1 <= 7 * k0 + 4 * d0 ->
      (Z.of_N (global_klo_u * u_val) + global_klo_c <= Z.of_N k0)%Z ->
      (Z.of_N ((64 + 8 * N.of_nat (8 - rem)%nat) * u_val) +
         (if Nat.eqb rem 8%nat then (-1)%Z else 1%Z) <= Z.of_N k0)%Z ->
      (Z.of_N k0 <= Z.of_N (128 * u_val) - 4)%Z ->
      exists k' tail',
        cfgCollar (k0 + 1) (prefixMod 2 PQ ++ (Tok1 :: rq)) -->* cfgCollar k' tail' /\
        (InC0 k' tail' \/ InC1 k' tail')).
Proof.
  induction rem as [| rem' IH]; intros rq wrq prq gku gkc memo hrem8 hwrq hprq hgk64 hgkc hok hm.
  - cbn [checkOneRQSlabs snd].
    split; [exact hm | intros u_val k0 d0 PQ _ _ _ _ _ _ _ _ _ _ hlo hhi].
    change ((Z.of_N ((64 + 8 * 8) * u_val) + 1 <= Z.of_N k0)%Z) in hlo.
    replace ((64 + 8 * 8) * u_val) with (128 * u_val) in hlo by lia.
    clear - hlo hhi; lia.
  - cbn [checkOneRQSlabs] in hok |- *; cbn zeta in hok |- *.
    set (slab := N.of_nat (8 - S rem')%nat) in *.
    set (s_lo_u0 := 64 + 8 * slab) in *.
    set (s_lo_c0 := if slab =? 0 then (-1)%Z else 1%Z) in *.
    set (s_hi_u := 64 + 8 * (slab + 1)) in *.
    set (s_hi_c := if slab =? 7 then (-4)%Z else 0%Z) in *.
    assert (hs_hi_ge72 : 72 <= s_hi_u) by (unfold s_hi_u; lia).
    assert (next_slab : forall (u_val k0 : N),
        (Z.of_N (s_hi_u * u_val) + s_hi_c < Z.of_N k0)%Z ->
        (Z.of_N k0 <= Z.of_N (128 * u_val) - 4)%Z ->
        (Z.of_N ((64 + 8 * N.of_nat (8 - rem')%nat) * u_val) +
           (if Nat.eqb rem' 8%nat then (-1)%Z else 1%Z) <= Z.of_N k0)%Z).
    { intros u_val k0 hgt hhi.
      destruct rem' as [| r'].
      - assert (hsl7 : slab = 7) by (unfold slab; lia).
        unfold s_hi_u, s_hi_c in hgt; rewrite hsl7 in hgt.
        change ((Z.of_N (128 * u_val) + (-4) < Z.of_N k0)%Z) in hgt.
        clear - hgt hhi; lia.
      - assert (hlt7 : (slab =? 7) = false) by (apply N.eqb_neq; unfold slab; lia).
        assert (hbr8 : Nat.eqb (S r') 8%nat = false) by (apply Nat.eqb_neq; lia).
        assert (hsub : N.of_nat (8 - S r')%nat = slab + 1) by (unfold slab; lia).
        unfold s_hi_u, s_hi_c in hgt; rewrite hlt7 in hgt.
        rewrite hbr8, hsub; lia. }
    destruct (s_hi_u <? gku) eqn:Hsk1.
    + apply N.ltb_lt in Hsk1.
      assert (hgkc1 : gkc = 1%Z)
        by (destruct hgkc as [[he64 _] | h1]; [lia | exact h1]).
      destruct (IH rq wrq prq gku gkc memo ltac:(lia) hwrq hprq hgk64 hgkc hok hm)
        as [hm_out hrec].
      split; [exact hm_out |].
      intros u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo hlo0 hhi.
      pose proof (N.mul_le_mono_r (s_hi_u + 1) gku u_val ltac:(lia)) as hmul_u.
      assert (hgt : (Z.of_N (s_hi_u * u_val) + s_hi_c < Z.of_N k0)%Z).
      { assert (hs_c : (s_hi_c <= 0)%Z) by (unfold s_hi_c; destruct (slab =? 7); lia).
        replace ((s_hi_u + 1) * u_val) with (s_hi_u * u_val + u_val) in hmul_u by ring.
        rewrite hgkc1 in hglo; clear - hU hmul_u hs_c hglo; clearbody s_hi_u s_hi_c; lia. }
      exact (hrec u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo
               (next_slab u_val k0 hgt hhi) hhi).
    + remember (if s_lo_u0 <? gku then (gku, gkc)
                else if s_lo_u0 =? gku then (s_lo_u0, Z.max s_lo_c0 gkc)
                else (s_lo_u0, s_lo_c0)) as slo_pair eqn:Hslo.
      destruct slo_pair as [s_lo_u s_lo_c]; cbn zeta in hok |- *.
      assert (hslo_spec : forall (u_val k0 : N),
          (Z.of_N ((64 + 8 * N.of_nat (8 - S rem')%nat) * u_val) +
             (if Nat.eqb (S rem') 8%nat then (-1)%Z else 1%Z) <= Z.of_N k0)%Z ->
          (Z.of_N (gku * u_val) + gkc <= Z.of_N k0)%Z ->
          64 <= s_lo_u /\ (Z.of_N (s_lo_u * u_val) + s_lo_c <= Z.of_N k0)%Z).
      { intros u_val k0 hlo0 hglo.
        assert (hlo0' : (Z.of_N (s_lo_u0 * u_val) + s_lo_c0 <= Z.of_N k0)%Z).
        { unfold s_lo_u0, s_lo_c0, slab.
          destruct (Nat.eq_dec (S rem') 8%nat) as [he8 | hne8].
          - assert (hb1 : (N.of_nat (8 - S rem')%nat =? 0) = true) by (apply N.eqb_eq; lia).
            assert (hb2 : Nat.eqb (S rem') 8%nat = true) by (apply Nat.eqb_eq; exact he8).
            rewrite hb1; rewrite hb2 in hlo0; exact hlo0.
          - assert (hb1 : (N.of_nat (8 - S rem')%nat =? 0) = false) by (apply N.eqb_neq; lia).
            assert (hb2 : Nat.eqb (S rem') 8%nat = false) by (apply Nat.eqb_neq; exact hne8).
            rewrite hb1; rewrite hb2 in hlo0; exact hlo0. }
        pose proof Hslo as Hslo_u.
        destruct (s_lo_u0 <? gku) eqn:Hlt_slo.
        - injection Hslo_u as -> ->; exact (conj hgk64 hglo).
        - destruct (s_lo_u0 =? gku) eqn:Heq_slo.
          + apply N.eqb_eq in Heq_slo; injection Hslo_u as -> ->.
            split; [unfold s_lo_u0; lia |].
            rewrite Heq_slo in hlo0' |- *; clear - hlo0' hglo; lia.
          + injection Hslo_u as -> ->.
            split; [unfold s_lo_u0; lia | exact hlo0']. }
      destruct ((s_lo_u =? s_hi_u) && negb (s_lo_c <=? s_hi_c)%Z) eqn:Hsk2.
      * apply Bool.andb_true_iff in Hsk2 as [hu_eq hc_gt].
        apply N.eqb_eq in hu_eq; apply Bool.negb_true_iff in hc_gt; apply Z.leb_gt in hc_gt.
        destruct (IH rq wrq prq gku gkc memo ltac:(lia) hwrq hprq hgk64 hgkc hok hm)
          as [hm_out hrec].
        split; [exact hm_out |].
        intros u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo hlo0 hhi.
        destruct (hslo_spec u_val k0 hlo0 hglo) as [_ hklo].
        rewrite hu_eq in hklo.
        exact (hrec u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo
                 (next_slab u_val k0 ltac:(clear - hc_gt hklo; clearbody s_hi_u s_hi_c; lia) hhi) hhi).
      * set (y1 := norm1 (Tok1 :: rq)) in *.
        set (nb := mkWaveNode
          0 0 false
          s_lo_u s_lo_c s_hi_u s_hi_c
          (s_lo_u - 64) (s_lo_c + 3)%Z (s_hi_u - 64) (s_hi_c + 3)%Z
          1 0 0
          (2 * s_hi_u) (2 * s_hi_c)%Z
          0 0 0%Z
          emptyJB y1 wrq prq) in *.
        destruct (checkRoot nb memo) as [ok memo'] eqn:HpR.
        destruct ok; [cbn [negb] in hok |- * | discriminate hok].
        destruct (checkRoot_sound nb memo ltac:(rewrite HpR; reflexivity) hm) as [hcl_nb hmemo'].
        rewrite HpR in hmemo'; cbn [snd] in hmemo'.
        destruct (IH rq wrq prq gku gkc memo' ltac:(lia) hwrq hprq hgk64 hgkc hok hmemo')
          as [hm_out hrec].
        split; [exact hm_out |].
        intros u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo hlo0 hhi.
        destruct (Z_le_gt_dec (Z.of_N k0) (Z.of_N (s_hi_u * u_val) + s_hi_c)) as [hkhi | hgt].
        -- destruct (hslo_spec u_val k0 hlo0 hglo) as [hslo64 hklo].
           set (PQ2 := prefixMod 2 PQ).
           set (j_val := leadB PQ2).
           set (P := dropB PQ2).
           destruct (prefixMod_props PQ hnoPQ 2) as [hno2 [hcb2 [hdb2 [hw2 [_ _]]]]].
           fold PQ2 in hno2, hcb2, hdb2, hw2.
           assert (hw2_exact : evalPhi 0 PQ2 = k0 + 3 - 64 * u_val).
           { rewrite hw2, hpowPQ, (N.mod_small (evalPhi 0 PQ + 2) (64 * u_val) ltac:(clear - hwPQ hhi; lia)).
             clear - hwPQ hhi; lia. }
           assert (hwP : evalPhi 0 P = k0 + 3 - 64 * u_val)
             by (unfold P; rewrite evalPhi_zero_dropB; exact hw2_exact).
           assert (hwP_eq : evalPhi 0 P + 64 * u_val = k0 + 3)
             by (clear - hwP hwPQ; lia).
           pose proof (deltaB_leadB_dropB PQ2) as hdb_split.
           assert (hns : NodeState nb u_val k0 d0 j_val P).
           { unfold nb; clearbody s_hi_u s_hi_c; constructor; cbn [
               nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
               nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
               nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
               try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
             - exact (noK1_dropB hno2).
             - unfold P; rewrite msOf_0, countBin_dropB, hcb2; exact hpowPQ.
             - intros _; exact (leadB_dropB PQ2).
             - exact (noTrailZero_norm1 (Tok1 :: rq)).
             - assert (hsub : (s_lo_u - 64) * u_val + 64 * u_val = s_lo_u * u_val)
                 by (rewrite <- N.mul_add_distr_r; f_equal; lia).
               clear - hwP_eq hsub hklo; lia.
             - exact (JBoundsValid_empty u_val j_val).
             - rewrite pow2N_0; unfold P, j_val; clear - hdb_split hdb2 hdbPQ; lia.
             - intros _; rewrite pow2N_0; unfold P, j_val; clear - hdb_split hdb2 hdbPQ; lia. }
           destruct (hcl_nb u_val k0 d0 j_val P hns) as [k' [tail' [hstar hinv]]].
           assert (hcfg_eq : nodeCfg nb k0 j_val P = cfgCollar (k0 + 1) (PQ2 ++ (Tok1 :: rq))).
           { unfold nodeCfg, nb, y1; cbn [nd_extra_B nd_has_i1_front nd_Y].
             rewrite cfgCollar_append_norm1.
             assert (hrw : PQ2 ++ (Tok1 :: rq) = repB j_val ++ (P ++ (Tok1 :: rq)))
               by (unfold j_val, P; rewrite app_assoc, rep_leadB_dropB; reflexivity).
             rewrite hrw, cfgCollar_repB; f_equal; lia. }
           rewrite hcfg_eq in hstar.
           exists k', tail'; exact (conj hstar hinv).
        -- exact (hrec u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ hdbPQ hd1 hd2 hwM hglo
                    (next_slab u_val k0 (Z.gt_lt _ _ hgt) hhi) hhi).
Qed.

Local Lemma checkOneRQ_sound (rq : list BecTok1) (memo : MemoTree)
    (hm0 : MemoValid NodeClosed memo) (hok : fst (checkOneRQ rq memo) = true) :
  forall (u_val k0 : N) (M W PQ : list BecTok1),
    1 <= u_val -> 64 <= k0 ->
    2 * evalPhi 0 M < 7 * k0 -> evalPhi 22 M < 52 * k0 ->
    RelT M1 M W -> RelT0Pow (k0 - 1) W (PQ ++ [Tok1] ++ rq) ->
    noK1 PQ = true -> 2 ^ countBin PQ = 64 * u_val ->
    evalPhi 0 PQ + 64 * u_val = k0 + 1 ->
    evalPhi 2 M = 64 * u_val * evalPhi 2 rq ->
    evalPhi 0 M + 2 * deltaB PQ = 64 * u_val * evalPhi 0 rq ->
    evalPhi 22 M = 20 * deltaB PQ + 64 * u_val * evalPhi 22 rq ->
    exists k' tail',
      cfgCollar k0 (TokI :: Tok1 :: M) -->+ cfgCollar k' tail' /\
      (InC0 k' tail' \/ InC1 k' tail').
Proof.
  unfold checkOneRQ in hok; cbn zeta in hok.
  pose (wrq := evalPhi 0 rq); assert (Hwrq : wrq = evalPhi 0 rq) by reflexivity; clearbody wrq; rewrite <- Hwrq in hok.
  pose (prq := evalPhi 22 rq); assert (Hprq : prq = evalPhi 22 rq) by reflexivity; clearbody prq; rewrite <- Hprq in hok.
  pose (psirq := evalPhi 2 rq); assert (Hpsirq : psirq = evalPhi 2 rq) by reflexivity; clearbody psirq; rewrite <- Hpsirq in hok.
  set (q_psi_lo := (44 * 64 * psirq) / 348) in *.
  set (q_phi_lo := (64 * prq) / 52) in *.
  set (m_lo := N.max q_psi_lo q_phi_lo) in *.
  set (global_klo_u := N.max 64 m_lo) in *.
  set (global_klo_c := if 64 <=? m_lo then 1%Z else (-1)%Z) in *.
  assert (hgk64 : 64 <= global_klo_u) by exact (N.le_max_l 64 m_lo).
  assert (hgkc_inv : (global_klo_u = 64 /\ global_klo_c = (-1)%Z) \/ global_klo_c = 1%Z).
  { unfold global_klo_u, global_klo_c.
    destruct (64 <=? m_lo) eqn:Hb; [right; reflexivity |].
    apply N.leb_gt in Hb; left; split; [lia | reflexivity]. }
  remember (if (44 * 64 * psirq <=? 348 * 128) && (64 * prq <=? 52 * 128) then
              match t1Norm wordFuel rq with
              | None => (false, memo)
              | Some y1 =>
                let na := mkWaveNode
                  0 0 false
                  128 (-3)%Z 128 (-2)%Z
                  0 0%Z 0 1%Z
                  1 0 0
                  256 (-4)%Z
                  0 0 0%Z
                  emptyJB y1 wrq prq in
                checkRoot na memo
              end
            else (true, memo)) as pA eqn:HpA.
  destruct pA as [okA memoA].
  destruct okA; [cbn [negb] in hok | discriminate hok].
  assert (hpA_spec :
    MemoValid NodeClosed memoA /\
    ((44 * 64 * psirq <=? 348 * 128) = true ->
     (64 * prq <=? 52 * 128) = true ->
     exists y1 : list BecTok1,
       RelT M1 rq y1 /\ noTrailZero y1 = true /\
       NodeClosed (mkWaveNode
         0 0 false
         128 (-3)%Z 128 (-2)%Z
         0 0%Z 0 1%Z
         1 0 0
         256 (-4)%Z
         0 0 0%Z
         emptyJB y1 wrq prq))).
  { destruct ((44 * 64 * psirq <=? 348 * 128) && (64 * prq <=? 52 * 128)) eqn:HgA.
    - destruct (t1Norm wordFuel rq) as [y1 |] eqn:Ht1; [| discriminate HpA].
      cbn zeta in HpA.
      set (na := mkWaveNode
        0 0 false
        128 (-3)%Z 128 (-2)%Z
        0 0%Z 0 1%Z
        1 0 0
        256 (-4)%Z
        0 0 0%Z
        emptyJB y1 wrq prq) in HpA.
      destruct (checkRoot_sound na memo ltac:(rewrite <- HpA; reflexivity) hm0) as [hcl_na hmA].
      rewrite <- HpA in hmA; cbn [snd] in hmA.
      exact (conj hmA (fun _ _ => ex_intro _ y1
        (conj (t1Norm_sound Ht1) (conj (t1Norm_noTrailZero Ht1) hcl_na)))).
    - injection HpA as <-; split; [exact hm0 | intros h1 h2; rewrite h1, h2 in HgA; discriminate HgA]. }
  destruct hpA_spec as [hmA hna_opt].
  destruct (checkOneRQSlabs_sound 8%nat rq wrq prq global_klo_u global_klo_c memoA
              (Nat.le_refl 8%nat) Hwrq Hprq hgk64 hgkc_inv hok hmA) as [_ hslabs].
  intros u_val k0 M W PQ hU hK64 hwM hpM ht1 hpow hnoPQ hpowPQ hwPQ ec2 ec0 ec22.
  set (d0 := deltaB PQ).
  assert (hlt_pow : evalPhi 0 PQ < 64 * u_val)
    by (rewrite <- hpowPQ; exact (evalPhi_zero_lt_pow_countBin PQ)).
  assert (hk_upper : k0 + 2 <= 128 * u_val) by lia.
  assert (hk_lower : 64 * u_val <= k0 + 1) by lia.
  pose proof (conservation_22 M) as hcons.
  assert (h44 : 44 * evalPhi 2 M + 24 <= 348 * k0) by (clear - hcons hwM hpM; lia).
  assert (hd1 : 2 * d0 <= 64 * wrq * u_val)
    by (unfold d0; rewrite Hwrq; replace (64 * evalPhi 0 rq * u_val) with (64 * u_val * evalPhi 0 rq) by ring; lia).
  assert (hd2 : 20 * d0 + 64 * prq * u_val + 1 <= 52 * k0)
    by (unfold d0; rewrite Hprq; replace (64 * evalPhi 22 rq * u_val) with (64 * u_val * evalPhi 22 rq) by ring; lia).
  assert (hwM_lo : 128 * wrq * u_val + 1 <= 7 * k0 + 4 * d0)
    by (unfold d0; rewrite Hwrq; replace (128 * evalPhi 0 rq * u_val) with (2 * (64 * u_val * evalPhi 0 rq)) by ring; lia).
  assert (hpow_cons : RelT0Pow (k0 - 1) W (PQ ++ (Tok1 :: rq))) by exact hpow.
  destruct (N.lt_ge_cases (128 * u_val) (k0 + 4)) as [hk_a | hk_b].
  - (* Region A: 128 * u_val - 3 <= k0 <= 128 * u_val - 2 *)
    assert (hb_psi : (44 * 64 * psirq <=? 348 * 128) = true).
    { apply N.leb_le.
      destruct (N.lt_ge_cases (348 * 128) (44 * 64 * psirq)) as [hgt | hle]; [| exact hle].
      pose proof (N.mul_le_mono_r (348 * 128 + 1) (44 * 64 * psirq) u_val ltac:(lia)) as h1.
      assert (h2 : (44 * 64 * psirq) * u_val = 44 * evalPhi 2 M) by (rewrite Hpsirq, ec2; ring).
      replace ((348 * 128 + 1) * u_val) with (348 * (128 * u_val) + u_val) in h1 by ring.
      rewrite h2 in h1; clear - hU hk_upper h44 h1; lia. }
    assert (hb_phi : (64 * prq <=? 52 * 128) = true).
    { apply N.leb_le.
      destruct (N.lt_ge_cases (52 * 128) (64 * prq)) as [hgt | hle]; [| exact hle].
      pose proof (N.mul_le_mono_r (52 * 128 + 1) (64 * prq) u_val ltac:(lia)) as h1.
      assert (h2 : (64 * prq) * u_val = 64 * u_val * evalPhi 22 rq) by (rewrite Hprq; ring).
      replace ((52 * 128 + 1) * u_val) with (52 * (128 * u_val) + u_val) in h1 by ring.
      rewrite h2 in h1; clear - hU hk_upper hpM ec22 h1; lia. }
    destruct (hna_opt hb_psi hb_phi) as [y1 [hy1_rel [hy1_tz hcl_na]]].
    set (r := (k0 + 3) - 128 * u_val).
    assert (hdm : (evalPhi 0 PQ + 2) / (64 * u_val) = 1 /\
                  (evalPhi 0 PQ + 2) mod (64 * u_val) = r).
    { refine (@div_mod_unique (evalPhi 0 PQ + 2) (64 * u_val) 1 r _ _);
        unfold r; clear - hU hwPQ hk_a hk_upper; lia. }
    assert (hrel1 : RelT0Pow ((evalPhi 0 PQ + 2) / (2 ^ countBin PQ)) (Tok1 :: rq) y1)
      by (rewrite hpowPQ, (proj1 hdm); exact (rt0_succ (rt_t0_k1 hy1_rel) (rt0_zero y1))).
    pose proof (prefixMod_rel PQ hnoPQ 2 hrel1) as hrel2.
    assert (hpow_k1 : RelT0Pow (k0 + 1) W (prefixMod 2 PQ ++ y1))
      by (replace (k0 + 1) with ((k0 - 1) + 2) by lia; exact (RelT0Pow_trans hpow_cons hrel2)).
    pose proof (@collar_step_inC1_pow_raw k0 M W (prefixMod 2 PQ ++ y1) ltac:(lia) ht1 hpow_k1) as hstep1.
    set (PQ2 := prefixMod 2 PQ).
    set (j_val := leadB PQ2).
    set (P := dropB PQ2).
    destruct (prefixMod_props PQ hnoPQ 2) as [hno2 [hcb2 [hdb2 [hw2 [_ _]]]]].
    fold PQ2 in hno2, hcb2, hdb2, hw2.
    assert (hwP : evalPhi 0 P = r)
      by (unfold P; rewrite evalPhi_zero_dropB, hw2, hpowPQ, (proj2 hdm); reflexivity).
    pose proof (deltaB_leadB_dropB PQ2) as hdb_split.
    set (na := mkWaveNode
      0 0 false
      128 (-3)%Z 128 (-2)%Z
      0 0%Z 0 1%Z
      1 0 0
      256 (-4)%Z
      0 0 0%Z
      emptyJB y1 wrq prq) in *.
    assert (hns : NodeState na u_val k0 d0 j_val P).
    { unfold na; clearbody q_psi_lo q_phi_lo m_lo global_klo_u global_klo_c; constructor; cbn [
        nd_s nd_db_shift nd_has_i1_front nd_k_lo_u nd_k_lo_c nd_k_hi_u nd_k_hi_c
        nd_w_lo_u nd_w_lo_c nd_w_hi_u nd_w_hi_c nd_extra_B nd_scaled_db_u nd_scaled_db_c
        nd_kj_hi_u nd_kj_hi_c nd_wj_k nd_wj_hi_u nd_wj_hi_c nd_jb nd_Y nd_wRQ nd_pRQ];
        try assumption; try (intros h; discriminate h);
          match goal with |- (_ <= _)%N => try lia | |- (_ <= _)%Z => try lia | _ => idtac end.
      - exact (noK1_dropB hno2).
      - unfold P; rewrite msOf_0, countBin_dropB, hcb2; exact hpowPQ.
      - intros _; exact (leadB_dropB PQ2).
      - exact (JBoundsValid_empty u_val j_val).
      - rewrite pow2N_0; unfold P, j_val, d0; clear - hdb_split hdb2; lia.
      - intros _; rewrite pow2N_0; unfold P, j_val, d0; clear - hdb_split hdb2; lia. }
    destruct (hcl_na u_val k0 d0 j_val P hns) as [k' [tail' [hstar hinv]]].
    assert (hcfg_eq : nodeCfg na k0 j_val P = cfgCollar (k0 + 1) (PQ2 ++ y1)).
    { unfold nodeCfg, na; cbn [nd_extra_B nd_has_i1_front nd_Y].
      assert (hrw : PQ2 ++ y1 = repB j_val ++ (P ++ y1))
        by (unfold j_val, P; rewrite app_assoc, rep_leadB_dropB; reflexivity).
      rewrite hrw, cfgCollar_repB; f_equal; lia. }
    rewrite hcfg_eq in hstar.
    exists k', tail'; exact (conj (petrans hstep1 hstar) hinv).
  - (* Region B: k0 + 4 <= 128 * u_val *)
    assert (hdiv0 : (evalPhi 0 PQ + 2) / (2 ^ countBin PQ) = 0)
      by (rewrite hpowPQ; (apply N.div_small; clear - hwPQ hk_b; lia)).
    assert (hrel0 : RelT0Pow ((evalPhi 0 PQ + 2) / (2 ^ countBin PQ)) (Tok1 :: rq) (Tok1 :: rq))
      by (rewrite hdiv0; exact (rt0_zero _)).
    pose proof (prefixMod_rel PQ hnoPQ 2 hrel0) as hrel2.
    assert (hpow_k1 : RelT0Pow (k0 + 1) W (prefixMod 2 PQ ++ (Tok1 :: rq)))
      by (replace (k0 + 1) with ((k0 - 1) + 2) by lia; exact (RelT0Pow_trans hpow_cons hrel2)).
    pose proof (@collar_step_inC1_pow_raw k0 M W (prefixMod 2 PQ ++ (Tok1 :: rq)) ltac:(lia) ht1 hpow_k1) as hstep1.
    assert (hqpsi : q_psi_lo * u_val + 1 <= k0).
    { destruct (div_mod_spec (44 * 64 * psirq) 348 ltac:(lia)) as [qp [rp [hqp [_ [hdivp _]]]]].
      fold q_psi_lo in hqp; subst qp.
      assert (h1 : 348 * q_psi_lo <= 44 * 64 * psirq) by (clear - hdivp; lia).
      pose proof (N.mul_le_mono_r _ _ u_val h1) as h2.
      assert (h3 : (44 * 64 * psirq) * u_val = 44 * evalPhi 2 M) by (rewrite Hpsirq, ec2; ring).
      replace ((348 * q_psi_lo) * u_val) with (348 * (q_psi_lo * u_val)) in h2 by ring.
      rewrite h3 in h2; clear - h2 h44; clearbody q_psi_lo; lia. }
    assert (hqphi : q_phi_lo * u_val + 1 <= k0).
    { destruct (div_mod_spec (64 * prq) 52 ltac:(lia)) as [qp [rp [hqp [_ [hdivp _]]]]].
      fold q_phi_lo in hqp; subst qp.
      assert (h1 : 52 * q_phi_lo <= 64 * prq) by (clear - hdivp; lia).
      pose proof (N.mul_le_mono_r _ _ u_val h1) as h2.
      assert (h3 : (64 * prq) * u_val = 64 * u_val * evalPhi 22 rq) by (rewrite Hprq; ring).
      replace ((52 * q_phi_lo) * u_val) with (52 * (q_phi_lo * u_val)) in h2 by ring.
      rewrite h3 in h2; clear - h2 hpM ec22; clearbody q_phi_lo; lia. }
    assert (hmlo : m_lo * u_val + 1 <= k0).
    { unfold m_lo.
      destruct (N.max_spec q_psi_lo q_phi_lo) as [[_ ->] | [_ ->]]; assumption. }
    assert (hglo : (Z.of_N (global_klo_u * u_val) + global_klo_c <= Z.of_N k0)%Z).
    { unfold global_klo_u, global_klo_c.
      destruct (64 <=? m_lo) eqn:Hb.
      - apply N.leb_le in Hb.
        replace (N.max 64 m_lo) with m_lo by (clear - Hb; clearbody m_lo; lia).
        clear - hmlo; clearbody m_lo; lia.
      - apply N.leb_gt in Hb.
        replace (N.max 64 m_lo) with 64 by (clear - Hb; clearbody m_lo; lia).
        clear - hk_lower; lia. }
    destruct (hslabs u_val k0 d0 PQ hU hK64 hnoPQ hpowPQ hwPQ eq_refl hd1 hd2 hwM_lo hglo
                ltac:(change ((Z.of_N (64 * u_val) + (-1) <= Z.of_N k0)%Z); clear - hk_lower; lia)
                ltac:(clear - hk_b; lia)) as [k' [tail' [hstar hinv]]].
    exists k', tail'; exact (conj (petrans hstep1 hstar) hinv).
Qed.

Local Lemma checkAllRQ_ok : checkAllRQ = true.
Proof. vm_compute; reflexivity. Qed.

#[local] Opaque checkOneRQ allRQ.

Local Lemma allRQ_verified :
  forall rq : list BecTok1, In rq allRQ -> fst (checkOneRQ rq MLeaf) = true.
Proof.
  exact (proj1 (List.forallb_forall (fun rq => fst (checkOneRQ rq MLeaf)) allRQ) checkAllRQ_ok).
Qed.

#[local] Opaque checkAllRQ.

Local Lemma branch2_step {k0 : N} {tail : list BecTok1} (h1 : InC1 k0 tail) :
  exists k' tail', cfgCollar k0 tail -->+ cfgCollar k' tail' /\
    (InC0 k' tail' \/ InC1 k' tail').
Proof.
  destruct h1 as [hK64 [M [-> [hnoM [_ [_ [hIM [hwM hpM]]]]]]]].
  destruct (t0Pow_t1_decomp (k0 - 1) M hnoM hIM)
    as [[W [Qw [ht1 [hpow [hnoQ [hwQ hpQ]]]]]] |
        [W [PQ [RQ [ht1 [hpow [hnoPQ [_ [hwPQ [hnoRQ [htzRQ [hnhRQ [hIRQ [ec2 [ec0 ec22]]]]]]]]]]]]]]].
  - destruct (branch2_absorbed_step hK64 hwM hpM ht1 hpow hnoQ hwQ hpQ) as [k' [tail' [hstep h0]]].
    exists k', tail'; exact (conj hstep (or_introl h0)).
  - assert (hwPQ_k1 : evalPhi 0 PQ + 2 ^ countBin PQ = k0 + 1) by lia.
    pose proof (evalPhi_zero_lt_pow_countBin PQ) as hlt_pow.
    assert (hcb6 : 6 <= countBin PQ).
    { destruct (N.lt_ge_cases (countBin PQ) 6) as [hlt6 | hge6]; [| exact hge6].
      assert (countBin PQ = 0 \/ countBin PQ = 1 \/ countBin PQ = 2 \/
              countBin PQ = 3 \/ countBin PQ = 4 \/ countBin PQ = 5)
        as [hc | [hc | [hc | [hc | [hc | hc]]]]] by lia;
        rewrite hc in hwPQ_k1, hlt_pow; cbn in hwPQ_k1, hlt_pow; lia. }
    remember (2 ^ (countBin PQ - 6)) as u_val eqn:Hu_val.
    assert (hU : 1 <= u_val) by (rewrite Hu_val; pose proof (pow2_pos (countBin PQ - 6)); lia).
    assert (hpowPQ : 2 ^ countBin PQ = 64 * u_val).
    { replace (countBin PQ) with (6 + (countBin PQ - 6)) by lia.
      rewrite N.pow_add_r, <- Hu_val; cbn; reflexivity. }
    rewrite hpowPQ in hwPQ_k1, hlt_pow, ec2, ec0, ec22.
    pose proof (conservation_22 M) as hcons.
    assert (h44 : 44 * evalPhi 2 M + 24 <= 348 * k0) by (clear - hcons hwM hpM; lia).
    assert (hk_upper : k0 + 2 <= 128 * u_val) by (clear - hwPQ_k1 hlt_pow; lia).
    assert (hrq2 : evalPhi 2 RQ <= 15).
    { destruct (N.lt_ge_cases 15 (evalPhi 2 RQ)) as [hgt | hle]; [| exact hle].
      pose proof (N.mul_le_mono_l 16 (evalPhi 2 RQ) (64 * u_val) ltac:(lia)) as h1.
      clear - hU hk_upper h44 ec2 h1; lia. }
    assert (hrq22 : evalPhi 22 RQ <= 103).
    { destruct (N.lt_ge_cases 103 (evalPhi 22 RQ)) as [hgt | hle]; [| exact hle].
      pose proof (N.mul_le_mono_l 104 (evalPhi 22 RQ) (64 * u_val) ltac:(lia)) as h1.
      clear - hU hk_upper hpM ec22 h1; lia. }
    pose proof (allRQ_complete hnoRQ htzRQ hnhRQ hIRQ hrq2 hrq22) as hmem.
    pose proof (allRQ_verified RQ hmem) as hok_rq.
    assert (hm_leaf : MemoValid NodeClosed MLeaf) by exact I.
    exact (checkOneRQ_sound RQ MLeaf hm_leaf hok_rq u_val k0 M W PQ hU hK64 hwM hpM
             ht1 hpow hnoPQ hpowPQ hwPQ_k1 ec2 ec0 ec22).
Qed.

Local Lemma inv_step :
  forall c : Q * tape, InvCfg c -> exists c' : Q * tape, InvCfg c' /\ c -->+ c'.
Proof.
  intros c [k_col [tail [-> [h0 | h1]]]].
  - destruct (branch1_step h0) as [k' [tail' [hstep hinv]]].
    exists (cfgCollar k' tail'); split; [exists k', tail'; exact (conj eq_refl hinv) | exact hstep].
  - destruct (branch2_step h1) as [k' [tail' [hstep hinv]]].
    exists (cfgCollar k' tail'); split; [exists k', tail'; exact (conj eq_refl hinv) | exact hstep].
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct init_reaches_inv as [c_init [hinit hinv0]].
  exact (multistep_nonhalt tm c0 c_init (p_to_e hinit)
    (progress_nonhalt tm InvCfg c_init inv_step hinv0)).
Qed.
