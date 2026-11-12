(* 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyBool PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA".
Arguments tm _ : simpl never.

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac fast_execute :=
  intros; repeat (try solve [fast_finish]; fast_step).

Ltac fast_start_progress :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  fast_execute.

(* ========================================================================== *)
(* Tape & List-Power Helpers                                                  *)
(* ========================================================================== *)

Lemma lpow_0 {X : Type} (u : list X) : u ^^ 0 = [].
Proof. reflexivity. Qed.

Lemma lpow_1 {X : Type} (u : list X) : u ^^ 1 = u.
Proof. cbn. apply app_nil_r. Qed.

Lemma lpow_succ_r {X : Type} (u : list X) (n : nat) :
  u ^^ S n = u ^^ n ++ u.
Proof.
  change (S n) with (1 + n).
  rewrite lpow_add, lpow_1.
  symmetry. apply lpow_shift.
Qed.

Lemma swap_1_11_pow (k : nat) (s : side) :
  [S1; S1] ^^ k *> (S1 >> s) = S1 >> ([S1; S1] ^^ k *> s).
Proof.
  symmetry. exact (lpow_shift21e S1 s k).
Qed.

Lemma cons_zero_0inf : S0 >> 0inf = 0inf.
Proof.
  symmetry. apply const_unfold.
Qed.

(* ========================================================================== *)
(* 1. Micro-Step Window Lemmas                                                *)
(* ========================================================================== *)

Definition Sweep (q : Q) (r u : side) : Prop :=
  forall l : side, (l {{B}}> r) -->+ (l <{{q}} u).

Definition eraCfg (r : side) : Q * tape :=
  (S1 >> S1 >> 0inf) {{B}}> r.

Lemma win_B_000 (l r : side) :
  (l {{B}}> (S0 >> S0 >> S0 >> r)) -->+ (l <{{F}} (S0 >> S1 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_B_001 (l r : side) :
  (l {{B}}> (S0 >> S0 >> S1 >> r)) -->+ (l <{{F}} (S1 >> S1 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_B_1 (l r : side) :
  (l {{B}}> (S1 >> r)) -->+ ((S1 >> l) {{B}}> r).
Proof. fast_start_progress. Qed.

Lemma win_B_01 (l r : side) :
  (l {{B}}> (S0 >> S1 >> r)) -->+ ((S0 >> S1 >> l) {{B}}> r).
Proof. fast_start_progress. Qed.

Lemma win_1_F (l r : side) :
  ((S1 >> l) <{{F}} r) -->+ (l <{{A}} (S1 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_1_D (l r : side) :
  ((S1 >> l) <{{D}} r) -->+ (l <{{F}} (S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_1_A (l r : side) :
  ((S1 >> l) <{{A}} r) -->+ (l <{{F}} (S1 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_10_F (l r : side) :
  ((S0 >> S1 >> l) <{{F}} r) -->+ (l <{{D}} (S1 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_10_D (l r : side) :
  ((S0 >> S1 >> l) <{{D}} r) -->+ (l <{{D}} (S1 >> S0 >> r)).
Proof. fast_start_progress. Qed.

Lemma win_10_A (l r : side) :
  ((S0 >> S1 >> l) <{{A}} r) -->+ ((S1 >> S1 >> l) {{B}}> r).
Proof. fast_start_progress. Qed.

Lemma win_era_bounce (u : side) :
  ((S1 >> S1 >> 0inf) <{{D}} u) -->+ eraCfg (S0 >> u).
Proof.
  unfold eraCfg.
  rewrite (const_unfold sym S0) at 1.
  fast_start_progress.
Qed.

Lemma init_to_era0 :
  c0 -->* eraCfg ([S0; S1] *> 0inf).
Proof.
  unfold c0, tape0, eraCfg, q0, s0.
  do 4 (rewrite (const_unfold sym S0) at 2).
  cbn [Str_app].
  fast_execute.
Qed.

Lemma era_step {r u : side} (h : Sweep D r u) :
  eraCfg r -->+ eraCfg (S0 >> u).
Proof.
  exact (ptrans (h _) (win_era_bounce u)).
Qed.

(* ========================================================================== *)
(* 2. Compositional Sweep Combinators                                         *)
(* ========================================================================== *)

Lemma sweep_000 (r : side) :
  Sweep F (S0 >> S0 >> S0 >> r) (S0 >> S1 >> S0 >> r).
Proof. intro l. exact (win_B_000 l r). Qed.

Lemma sweep_001 (r : side) :
  Sweep F (S0 >> S0 >> S1 >> r) (S1 >> S1 >> S0 >> r).
Proof. intro l. exact (win_B_001 l r). Qed.

Lemma sweep_default :
  Sweep F 0inf (S0 >> S1 >> 0inf).
Proof.
  intro l.
  pose proof (win_B_000 l 0inf) as h.
  repeat rewrite cons_zero_0inf in h.
  exact h.
Qed.

Lemma sweep_1_F {r u : side} (h : Sweep F r u) :
  Sweep A (S1 >> r) (S1 >> u).
Proof.
  intro l. exact (ptrans (win_B_1 l r) (ptrans (h _) (win_1_F l u))).
Qed.

Lemma sweep_1_D {r u : side} (h : Sweep D r u) :
  Sweep F (S1 >> r) (S0 >> u).
Proof.
  intro l. exact (ptrans (win_B_1 l r) (ptrans (h _) (win_1_D l u))).
Qed.

Lemma sweep_1_A {r u : side} (h : Sweep A r u) :
  Sweep F (S1 >> r) (S1 >> u).
Proof.
  intro l. exact (ptrans (win_B_1 l r) (ptrans (h _) (win_1_A l u))).
Qed.

Lemma sweep_01_F {r u : side} (h : Sweep F r u) :
  Sweep D (S0 >> S1 >> r) (S1 >> S0 >> u).
Proof.
  intro l. exact (ptrans (win_B_01 l r) (ptrans (h _) (win_10_F l u))).
Qed.

Lemma sweep_01_D {r u : side} (h : Sweep D r u) :
  Sweep D (S0 >> S1 >> r) (S1 >> S0 >> u).
Proof.
  intro l. exact (ptrans (win_B_01 l r) (ptrans (h _) (win_10_D l u))).
Qed.

Lemma sweep_01_A_F {r u v : side} (h1 : Sweep A r u) (h2 : Sweep F u v) :
  Sweep F (S0 >> S1 >> r) (S1 >> S1 >> v).
Proof.
  intro l.
  exact (ptrans (win_B_01 l r)
    (ptrans (h1 _)
      (ptrans (win_10_A l u)
        (ptrans (h2 _)
          (ptrans (win_1_F _ v) (win_1_A l _)))))).
Qed.

Lemma sweep_01_A_D {r u v : side} (h1 : Sweep A r u) (h2 : Sweep D u v) :
  Sweep A (S0 >> S1 >> r) (S1 >> S0 >> v).
Proof.
  intro l.
  exact (ptrans (win_B_01 l r)
    (ptrans (h1 _)
      (ptrans (win_10_A l u)
        (ptrans (h2 _)
          (ptrans (win_1_D _ v) (win_1_F l _)))))).
Qed.

Lemma sweep_01_A_A {r u v : side} (h1 : Sweep A r u) (h2 : Sweep A u v) :
  Sweep A (S0 >> S1 >> r) (S1 >> S1 >> v).
Proof.
  intro l.
  exact (ptrans (win_B_01 l r)
    (ptrans (h1 _)
      (ptrans (win_10_A l u)
        (ptrans (h2 _)
          (ptrans (win_1_A _ v) (win_1_F l _)))))).
Qed.

Lemma sweep_11_pow_F (m : nat) {r u : side} (h : Sweep F r u) :
  Sweep F ([S1; S1] ^^ m *> r) ([S1; S1] ^^ m *> u).
Proof.
  induction m as [| m ih]; [exact h |].
  cbn [lpow app Str_app].
  exact (sweep_1_A (sweep_1_F ih)).
Qed.

Lemma sweep_11_pow_A (m : nat) {r u : side} (h : Sweep A r u) :
  Sweep A ([S1; S1] ^^ m *> r) ([S1; S1] ^^ m *> u).
Proof.
  induction m as [| m ih]; [exact h |].
  cbn [lpow app Str_app].
  exact (sweep_1_F (sweep_1_A ih)).
Qed.

(* ========================================================================== *)
(* 3. 8-Constructor Tree, Payload, RVal, and Tape Evaluation                  *)
(* ========================================================================== *)

Inductive Tree : Type :=
  | endZero (c : nat)
  | endStop (c : nat)
  | endOne (c : nat)
  | oneEnd (c : nat)
  | stopOne (c : nat)
  | stop (c : nat) (d : Tree)
  | od (c m : nat) (d : Tree)
  | sh (c m : nat) (u : Tree).

Fixpoint tree_eqb (t1 t2 : Tree) : bool :=
  match t1, t2 with
  | endZero c1, endZero c2 => c1 =? c2
  | endStop c1, endStop c2 => c1 =? c2
  | endOne c1, endOne c2 => c1 =? c2
  | oneEnd c1, oneEnd c2 => c1 =? c2
  | stopOne c1, stopOne c2 => c1 =? c2
  | stop c1 d1, stop c2 d2 =>
      if c1 =? c2 then tree_eqb d1 d2 else false
  | od c1 m1 d1, od c2 m2 d2 =>
      if c1 =? c2 then (if m1 =? m2 then tree_eqb d1 d2 else false) else false
  | sh c1 m1 u1, sh c2 m2 u2 =>
      if c1 =? c2 then (if m1 =? m2 then tree_eqb u1 u2 else false) else false
  | _, _ => false
  end.

Lemma tree_eqb_spec (t1 t2 : Tree) : Bool.reflect (t1 = t2) (tree_eqb t1 t2).
Proof.
  revert t2.
  induction t1 as [c1 | c1 | c1 | c1 | c1 | c1 d1 ih | c1 m1 d1 ih | c1 m1 u1 ih];
    destruct t2; cbn [tree_eqb]; try (constructor; discriminate).
  - destruct (Nat.eqb_spec c1 c); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); [| constructor; congruence].
    destruct (ih t2); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); [| constructor; congruence].
    destruct (Nat.eqb_spec m1 m); [| constructor; congruence].
    destruct (ih t2); constructor; congruence.
  - destruct (Nat.eqb_spec c1 c); [| constructor; congruence].
    destruct (Nat.eqb_spec m1 m); [| constructor; congruence].
    destruct (ih t2); constructor; congruence.
Qed.

Definition tree_c (t : Tree) : nat :=
  match t with
  | endZero c | endStop c | endOne c | oneEnd c | stopOne c
  | stop c _ | od c _ _ | sh c _ _ => c
  end.

Definition set_c (nc : nat) (t : Tree) : Tree :=
  match t with
  | endZero _ => endZero nc
  | endStop _ => endStop nc
  | endOne _ => endOne nc
  | oneEnd _ => oneEnd nc
  | stopOne _ => stopOne nc
  | stop _ d => stop nc d
  | od _ m d => od nc m d
  | sh _ m u => sh nc m u
  end.

Definition add_c (dc : nat) (t : Tree) : Tree := set_c (tree_c t + dc) t.
Definition sub_c (dc : nat) (t : Tree) : Tree := set_c (tree_c t - dc) t.

Definition mk_stop (c : nat) (d : Tree) : Tree :=
  if tree_eqb d (endZero 0) then endStop c
  else if tree_eqb d (endOne 1) then stopOne c
  else stop c d.

Definition mk_sh (c m : nat) (u : Tree) : Tree :=
  if m =? 0 then
    if tree_eqb u (endStop 1) then oneEnd c else sh c m u
  else sh c m u.

Fixpoint evalCore (t : Tree) : side :=
  match t with
  | endZero _ => 0inf
  | endStop _ => [S0; S0; S1] *> 0inf
  | endOne _ => [S1] *> 0inf
  | oneEnd _ => [S1; S0; S1; S0; S0; S1] *> 0inf
  | stopOne _ => [S0; S0; S1; S0; S1; S1] *> 0inf
  | stop _ d => [S0; S0; S1] *> ([S0; S1] ^^ tree_c d *> evalCore d)
  | od _ m d => [S1; S1] ^^ m *> (S1 >> S0 >> ([S0; S1] ^^ tree_c d *> evalCore d))
  | sh _ m u => [S1; S1] ^^ m *> (S1 >> ([S0; S1] ^^ tree_c u *> evalCore u))
  end.

Definition evalT (t : Tree) : side :=
  [S0; S1] ^^ tree_c t *> evalCore t.

Definition tailT (t : Tree) : side :=
  S1 >> ([S0; S1] ^^ (tree_c t - 1) *> evalCore t).

Lemma tree_c_set_c (nc : nat) (t : Tree) : tree_c (set_c nc t) = nc.
Proof. destruct t; reflexivity. Qed.

Lemma evalCore_set_c (nc : nat) (t : Tree) : evalCore (set_c nc t) = evalCore t.
Proof. destruct t; reflexivity. Qed.

Lemma evalT_stop (c : nat) (d : Tree) :
  evalT (stop c d) = [S0; S1] ^^ c *> ([S0; S0; S1] *> evalT d).
Proof. reflexivity. Qed.

Lemma evalT_od (c m : nat) (d : Tree) :
  evalT (od c m d) =
    [S0; S1] ^^ c *> ([S1; S1] ^^ m *> (S1 >> S0 >> evalT d)).
Proof. reflexivity. Qed.

Lemma evalT_sh (c m : nat) (u : Tree) :
  evalT (sh c m u) =
    [S0; S1] ^^ c *> ([S1; S1] ^^ m *> (S1 >> evalT u)).
Proof. reflexivity. Qed.

Lemma cons_zero_tailT {t : Tree} (hc : tree_c t >= 1) :
  S0 >> tailT t = evalT t.
Proof.
  unfold tailT, evalT.
  replace (tree_c t) with (S (tree_c t - 1)) at 2 by lia.
  cbn [lpow app Str_app]. reflexivity.
Qed.

Lemma evalT_add_c_one {t : Tree} :
  evalT (add_c 1 t) = S0 >> S1 >> evalT t.
Proof.
  unfold add_c, evalT.
  rewrite tree_c_set_c, evalCore_set_c.
  replace (tree_c t + 1) with (S (tree_c t)) by lia.
  cbn [lpow app Str_app]. reflexivity.
Qed.

Lemma tailT_add_c_one {t : Tree} (hc : tree_c t >= 1) :
  tailT (add_c 1 t) = S1 >> S0 >> tailT t.
Proof.
  unfold add_c, tailT.
  rewrite tree_c_set_c, evalCore_set_c.
  replace (tree_c t + 1 - 1) with (S (tree_c t - 1)) by lia.
  cbn [lpow app Str_app]. reflexivity.
Qed.

Lemma evalT_mk_stop (c : nat) (d : Tree) :
  evalT (mk_stop c d) = [S0; S1] ^^ c *> ([S0; S0; S1] *> evalT d).
Proof.
  unfold mk_stop.
  destruct (tree_eqb_spec d (endZero 0)) as [-> | _]; [reflexivity |].
  destruct (tree_eqb_spec d (endOne 1)) as [-> | _]; reflexivity.
Qed.

Lemma tailT_mk_stop (c : nat) (hc : c >= 1) (d : Tree) :
  tailT (mk_stop c d) =
    S1 >> ([S0; S1] ^^ (c - 1) *> ([S0; S0; S1] *> evalT d)).
Proof.
  unfold mk_stop.
  destruct (tree_eqb_spec d (endZero 0)) as [-> | _]; [reflexivity |].
  destruct (tree_eqb_spec d (endOne 1)) as [-> | _]; reflexivity.
Qed.

Lemma tailT_mk_sh (c m : nat) (hc : c >= 1) (u : Tree) :
  tailT (mk_sh c m u) =
    S1 >> ([S0; S1] ^^ (c - 1) *> ([S1; S1] ^^ m *> (S1 >> evalT u))).
Proof.
  unfold mk_sh.
  destruct (Nat.eqb_spec m 0) as [-> | _]; [| reflexivity].
  destruct (tree_eqb_spec u (endStop 1)) as [-> | _]; reflexivity.
Qed.

Inductive Payload : Type :=
  | P_tree (t : Tree)
  | P_od (d : Tree).

Definition evalP (p : Payload) : side :=
  match p with
  | P_tree t => evalT t
  | P_od d => S0 >> evalT d
  end.

Inductive RVal : Type :=
  | R_D (p : Payload)
  | R_F (m : nat) (p : Payload)
  | R_A (m : nat) (p : Payload).

Definition SweepRV (r : side) (rv : RVal) : Prop :=
  match rv with
  | R_D (P_tree t) => Sweep D r (tailT t)
  | R_D (P_od _) => False
  | R_F m p => Sweep F r ([S1; S1] ^^ m *> evalP p)
  | R_A m p => Sweep A r ([S1; S1] ^^ m *> (S1 >> evalP p))
  end.

Definition app_1_odd (m : nat) (rv : RVal) : RVal :=
  match rv with
  | R_F m0 p => R_A (m + m0) p
  | R_A m0 p => R_F (S (m + m0)) p
  | R_D p => R_F m p
  end.

Definition app_1_even (m : nat) (rv : RVal) : RVal :=
  match m with
  | 0 => rv
  | S m' =>
    match rv with
    | R_F m0 p => R_F (S m' + m0) p
    | R_A m0 p => R_A (S m' + m0) p
    | R_D p => R_A m' p
    end
  end.

Definition bump_ra (rv : RVal) : RVal :=
  match rv with
  | R_F m p => R_F (S m) p
  | R_D p => R_A 0 p
  | R_A m p => R_A (S m) p
  end.

(* ========================================================================== *)
(* 4. Structural Well-Formedness, Weights, Shield, and Measures               *)
(* ========================================================================== *)

Fixpoint WF_u (t : Tree) : Prop :=
  match t with
  | endZero c | endStop c | stopOne c => c >= 1
  | endOne c | oneEnd c => c >= 2
  | stop c d => c >= 1 /\ d <> endZero 0 /\ d <> endOne 1 /\ WF_d d
  | od c _ d => c >= 2 /\ WF_d d
  | sh c m u => c >= 2 /\ ~ (m = 0 /\ u = endStop 1) /\ WF_u u
  end
with WF_d (t : Tree) : Prop :=
  match t with
  | endZero _ | endStop _ | endOne _ | oneEnd _ | stopOne _ => True
  | stop _ d => d <> endZero 0 /\ d <> endOne 1 /\ WF_d d
  | od _ _ d => WF_d d
  | sh _ m u => ~ (m = 0 /\ u = endStop 1) /\ WF_u u
  end.

Fixpoint W0 (t : Tree) : nat :=
  match t with
  | endZero c => 2 * c + 11
  | endStop c => if c <=? 1 then 11 else 2 * c + 10
  | endOne c => 2 * c + 9
  | oneEnd c => 2 * c + 11
  | stopOne c => 2 * c + 13
  | stop c d => 2 * c + 4 + Wd d
  | od c m d => 2 * c + 2 * m + 4 + Wd d
  | sh c m u => 2 * c + 2 * m + 2 + W0 u
  end
with Wd (t : Tree) : nat :=
  match t with
  | endZero c => if c =? 0 then 10 else if c =? 1 then 13 else 2 * c + 12
  | endStop c => if c =? 0 then 11 else 2 * c + 12
  | endOne c => if c <=? 1 then 9 else 2 * c + 10
  | oneEnd c => if c =? 0 then 12 else 2 * c + 11
  | stopOne c => if c =? 0 then 14 else 2 * c + 13
  | stop c d => 2 * c + 4 + Wd d
  | od c m d => 2 * c + 2 * m + 4 + Wd d
  | sh c m u => 2 * c + 2 * m + 2 + W0 u
  end.

Definition isLeaf (t : Tree) : bool :=
  match t with
  | endZero _ | endStop _ | endOne _ | oneEnd _ | stopOne _ => true
  | _ => false
  end.

Definition stopOnePosBonus (t : Tree) : nat :=
  match t with
  | stopOne c => if 1 <=? c then 2 else 0
  | _ => 0
  end.

Definition BadRoot (t : Tree) : Prop :=
  match t with
  | stop c (stopOne cd) => (cd >= 1 /\ c = cd + 1) \/ (cd = 0 /\ c = 2)
  | sh c m (oneEnd k) => m = 0 /\ k >= 2 /\ c = k
  | sh c m (endOne k) => m = 1 /\ k >= 3 /\ c + 1 = k
  | od c m (stopOne cd) => c = 3 /\ m = 0 /\ cd = 0
  | od c m (oneEnd cd) => c = 2 /\ m = 0 /\ cd = 1
  | od c m (stop cd (endOne ce)) => c = 2 /\ m = 0 /\ cd = 0 /\ ce = 0
  | _ => False
  end.

Definition WF_r_core (t : Tree) : Prop :=
  WF_u t /\
  match t with
  | endZero _ | endStop _ | endOne _ | oneEnd _ => True
  | stopOne c => c >= 2
  | stop c d => c >= 2 /\ 2 * c + 11 >= Wd d
  | od c _ d =>
      (if tree_eqb d (endZero 1) then c >= 3 else c >= 2) /\
      2 * c + 9 >= Wd d + stopOnePosBonus d
  | sh c _ u => 2 * c + 11 >= W0 u
  end.

Definition WF_r (t : Tree) : Prop := WF_r_core t /\ ~ BadRoot t.

Definition W0_lin (t : Tree) : nat :=
  if tree_eqb t (endStop 1) then 12 else W0 t.

Definition S_tree (t : Tree) : nat :=
  match t with
  | stopOne c => 24 - 2 * c
  | endZero _ | endStop _ | endOne _ | oneEnd _ => 0
  | stop c d => Nat.max (24 - 2 * c) (Wd d + 9 - 2 * c)
  | od c _ d =>
      Nat.max (if tree_eqb d (endZero 1) then 26 - 2 * c else 0)
              (Wd d + 11 + stopOnePosBonus d - 2 * c)
  | sh c _ u => W0 u + 9 - 2 * c
  end.

Definition W_ra_tree (m : nat) (w : Tree) : nat :=
  match w with
  | endZero c => if c <=? 1 then 2 * m + 15 else 2 * m + 2 * c + 13
  | endStop c => 2 * m + 2 * c + 13
  | _ => 2 * m + 4 + W0 w
  end.

Definition W_ra_od (m : nat) (d : Tree) : nat :=
  match d with
  | endZero cd => if cd <=? 1 then 2 * m + 2 * cd + 15 else 2 * m + 2 * cd + 16
  | endOne cd => 2 * m + 2 * cd + 14
  | endStop cd => 2 * m + 2 * cd + 17
  | oneEnd cd => 2 * m + 2 * cd + 17
  | stopOne cd => 2 * m + 2 * cd + 19
  | _ => 2 * m + 6 + Wd d
  end.

Definition W_rv (rv : RVal) : nat :=
  match rv with
  | R_D (P_tree t) => W0_lin t
  | R_D (P_od _) => 0
  | R_F 0 (P_tree u) =>
      if tree_eqb u (endZero 1) then 13
      else if tree_eqb u (endOne 2) then 14
      else W0_lin (mk_stop 1 (sub_c 1 u)) - 2
  | R_F 0 (P_od _) => 0
  | R_F (S m) (P_tree u) =>
      if m =? 0 then
        if tree_eqb u (endStop 1) then 15 else W0_lin (mk_sh 2 m u) - 2
      else W0_lin (mk_sh 2 m u) - 2
  | R_F (S m) (P_od d) =>
      if tree_eqb d (endOne 1) then 2 * S m + 15
      else 2 * S m + 4 + Wd d
  | R_A m (P_tree w) => W_ra_tree m w
  | R_A m (P_od d) => W_ra_od m d
  end.

Definition evenCeil (x : nat) : nat := ((x + 1) / 2) * 2.

Definition S_ra_tree (_m : nat) (w : Tree) : nat :=
  match w with
  | endZero c | endStop c => Nat.max 24 (2 * c + 20)
  | _ => Nat.max 24 (evenCeil (W0 w + 9) + 2)
  end.

Definition S_ra_od (d : Tree) : nat :=
  match d with
  | endZero cd | endStop cd => 2 * cd + 26
  | endOne cd | oneEnd cd => 2 * cd + 24
  | stopOne cd => 2 * cd + 28
  | stop cd _ => 2 * cd + Nat.max 26 (evenCeil (Wd (set_c 0 d) + 13) + 2)
  | _ => 2 * tree_c d + Nat.max 26 (evenCeil (Wd (set_c 0 d) + 11) + 2)
  end.

Definition S_rv (rv : RVal) : nat :=
  match rv with
  | R_D (P_tree t) => S_tree t
  | R_D (P_od _) => 0
  | R_F 0 (P_tree u) => Nat.max 22 (S_tree (mk_stop 1 (sub_c 1 u)) + 2)
  | R_F 0 (P_od _) => 22
  | R_F (S m) (P_tree u) => Nat.max 22 (S_tree (mk_sh 2 m u) + 2)
  | R_F (S m) (P_od d) => Nat.max 22 (S_tree (od 2 m d) + 2)
  | R_A m (P_tree w) => S_ra_tree m w
  | R_A _ (P_od d) => S_ra_od d
  end.

Definition WF_rv (rv : RVal) : Prop :=
  match rv with
  | R_D (P_tree u) => WF_u u
  | R_D (P_od _) => False
  | R_F 0 (P_tree u) => WF_u u
  | R_F 0 (P_od _) => False
  | R_F (S _) (P_tree u) => WF_u u
  | R_F (S _) (P_od d) => WF_d d
  | R_A _ (P_tree u) => WF_u u
  | R_A _ (P_od d) => WF_d d
  end.

Definition NotBadRD (rv : RVal) : Prop :=
  rv <> R_D (P_tree (endZero 1)) /\ rv <> R_D (P_tree (endOne 2)).

Definition GoodRV (rv : RVal) : Prop :=
  match rv with
  | R_D (P_tree (endZero _)) => False
  | R_D (P_tree (endStop _)) => False
  | R_D (P_tree (endOne _)) => False
  | R_F 0 (P_tree (endZero 1)) => False
  | _ => True
  end.

Definition W_safe (rv : RVal) : nat :=
  match rv with
  | R_D (P_tree (endOne c)) => 2 * c + 10
  | R_D (P_tree (oneEnd c)) => 2 * c + 13
  | R_D (P_tree (stopOne c)) => if c <=? 1 then 18 else 2 * c + 15
  | R_F m (P_tree (endStop c)) =>
      if m =? 1 then (if c =? 1 then 17 else W_rv (R_F m (P_tree (endStop c))))
      else W_rv (R_F m (P_tree (endStop c)))
  | R_F m (P_tree (endOne c)) =>
      if m =? 0 then (if c =? 2 then 16 else W_rv (R_F m (P_tree (endOne c))))
      else W_rv (R_F m (P_tree (endOne c)))
  | R_A m (P_od (endOne cd)) =>
      if m =? 0 then 2 * cd + 15 else W_rv (R_A m (P_od (endOne cd)))
  | rv => W_rv rv
  end.

Definition BadRV (rem : nat) (rv : RVal) : Prop :=
  if rem =? 0 then
    match rv with
    | R_D (P_tree t) => BadRoot t
    | _ => False
    end
  else
    match rv with
    | R_D (P_tree t) => BadRoot (add_c rem t)
    | R_F 0 (P_tree u) => BadRoot (mk_stop rem (sub_c 1 u))
    | R_F (S m) (P_tree u) => BadRoot (mk_sh (rem + 1) m u)
    | R_F (S m) (P_od d) => BadRoot (od (rem + 1) m d)
    | R_A m (P_tree (endStop k)) => m = 1 /\ k >= 2 /\ rem = k
    | R_A m (P_tree (endOne k)) => m = 0 /\ k >= 2 /\ rem = k
    | R_A m (P_od (oneEnd cd)) =>
        (cd = 0 /\ m = 1 /\ rem = 2) \/ (cd = 1 /\ m = 0 /\ rem = 3)
    | _ => False
    end.

Definition M_u (t : Tree) : nat :=
  match t with
  | od c m d => W0 (od c m d) + 3
  | sh c m u => W0 (sh c m u) + 3
  | _ => 0
  end.

Definition M_d0 (t : Tree) : nat :=
  match t with
  | od c m d => Wd (od c m d) + 7
  | sh c m u => Wd (sh c m u) + 7
  | _ => 0
  end.

Definition M_rv (rv : RVal) : nat := W_rv rv + 2.

(* ========================================================================== *)
(* Automation Tactics for Tree/RVal Arithmetic & Case-Splitting               *)
(* ========================================================================== *)

Ltac unfold_arith :=
  unfold M_u, M_d0, M_rv, W_safe, W_rv, S_rv, S_ra_tree, S_ra_od,
         W_ra_tree, W_ra_od, W0_lin, S_tree, stopOnePosBonus, isLeaf,
         evenCeil, mk_stop, mk_sh, add_c, sub_c, set_c, tree_c in *.

Ltac norm_hyps :=
  repeat match goal with
  | H : False |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : endZero ?a = endZero ?b |- _ => injection H as H; try subst
  | H : endStop ?a = endStop ?b |- _ => injection H as H; try subst
  | H : endOne ?a = endOne ?b |- _ => injection H as H; try subst
  | H : oneEnd ?a = oneEnd ?b |- _ => injection H as H; try subst
  | H : stopOne ?a = stopOne ?b |- _ => injection H as H; try subst
  | H : stop ?c1 ?d1 = stop ?c2 ?d2 |- _ => injection H as H ?; try subst
  | H : od ?c1 ?m1 ?d1 = od ?c2 ?m2 ?d2 |- _ => injection H as H ? ?; try subst
  | H : sh ?c1 ?m1 ?u1 = sh ?c2 ?m2 ?u2 |- _ => injection H as H ? ?; try subst
  | H : endZero ?a <> endZero ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : endStop ?a <> endStop ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : endOne ?a <> endOne ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : oneEnd ?a <> oneEnd ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : stopOne ?a <> stopOne ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : P_tree ?a = P_tree ?b |- _ => injection H as H; try subst
  | H : P_od ?a = P_od ?b |- _ => injection H as H; try subst
  | H : R_D ?a = R_D ?b |- _ => injection H as H; try subst
  | H : R_F ?m1 ?p1 = R_F ?m2 ?p2 |- _ => injection H as H ?; try subst
  | H : R_A ?m1 ?p1 = R_A ?m2 ?p2 |- _ => injection H as H ?; try subst
  | H : R_F ?m ?a <> R_F ?m ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : R_D ?a <> R_D ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : P_tree ?a <> P_tree ?b |- _ =>
      let H' := fresh "Hne" in assert (H' : a <> b) by congruence; clear H
  | H : ?x = ?y |- _ =>
      first [ is_var x; subst x | is_var y; subst y | discriminate H ]
  | H : ?x <> ?x |- _ => exfalso; apply H; reflexivity
  | H : ?x = ?x -> False |- _ => exfalso; apply H; reflexivity
  end.

Ltac split_one_if :=
  cbn [Nat.add tree_eqb W0 Wd WF_u WF_d BadRoot app_1_odd app_1_even bump_ra
       set_c tree_c stopOnePosBonus isLeaf] in *;
  norm_hyps;
  match goal with
  | |- context [tree_eqb ?a ?b] =>
      let H := fresh "Heq" in destruct (tree_eqb_spec a b) as [H | H]
  | H0 : context [tree_eqb ?a ?b] |- _ =>
      let H := fresh "Heq" in destruct (tree_eqb_spec a b) as [H | H]
  | |- context [?x =? ?y] =>
      let H := fresh "Heq" in destruct (Nat.eqb_spec x y) as [H | H]
  | H0 : context [?x =? ?y] |- _ =>
      let H := fresh "Heq" in destruct (Nat.eqb_spec x y) as [H | H]
  | |- context [?x <=? ?y] =>
      let H := fresh "Hle" in destruct (Nat.leb_spec0 x y) as [H | H]
  | H0 : context [?x <=? ?y] |- _ =>
      let H := fresh "Hle" in destruct (Nat.leb_spec0 x y) as [H | H]
  end;
  norm_hyps.

Ltac crush_arith :=
  unfold BadRV, WF_r, WF_r_core, WF_rv, NotBadRD, GoodRV in *;
  unfold_arith;
  cbn [Nat.add tree_eqb W0 Wd WF_u WF_d BadRoot app_1_odd app_1_even bump_ra] in *;
  norm_hyps;
  repeat split_one_if;
  cbn [Nat.add tree_eqb W0 Wd WF_u WF_d BadRoot app_1_odd app_1_even bump_ra] in *;
  norm_hyps;
  try solve [tauto | congruence | lia
            | repeat (split || intro); norm_hyps;
              solve [tauto | congruence | lia | intuition (congruence || lia)]].

(* ========================================================================== *)
(* 5. Basic Bounds & SweepRV Combinators                                      *)
(* ========================================================================== *)

Lemma tree_c_pos_of_WF_u {u : Tree} (h : WF_u u) : tree_c u >= 1.
Proof. destruct u; crush_arith. Qed.

Lemma WF_d_of_WF_u {u : Tree} (h : WF_u u) : WF_d u.
Proof. destruct u; cbn in *; intuition. Qed.

Lemma WF_d_set_c (nc : nat) {d : Tree} (h : WF_d d) : WF_d (set_c nc d).
Proof. destruct d; cbn in *; exact h. Qed.

Lemma WF_u_add_c (k : nat) {u : Tree} (h : WF_u u) : WF_u (add_c k u).
Proof. destruct u; unfold add_c; cbn in *; intuition lia. Qed.

Lemma WF_u_mk_stop (c : nat) (hc : c >= 1) {d : Tree} (hd : WF_d d) :
  WF_u (mk_stop c d).
Proof.
  unfold mk_stop.
  destruct (tree_eqb_spec d (endZero 0)) as [-> | h1]; [cbn; lia |].
  destruct (tree_eqb_spec d (endOne 1)) as [-> | h2]; [cbn; lia |].
  cbn; auto.
Qed.

Lemma WF_u_mk_sh (c m : nat) (hc : c >= 2) {u : Tree} (hu : WF_u u) :
  WF_u (mk_sh c m u).
Proof.
  unfold mk_sh.
  destruct (Nat.eqb_spec m 0) as [-> | hm].
  - destruct (tree_eqb_spec u (endStop 1)) as [-> | hu1]; cbn; intuition lia.
  - cbn; intuition lia.
Qed.

Fixpoint W0_ge_11 (t : Tree) : W0 t >= 2 * tree_c t + 9
with Wd_ge_9 (d : Tree) : Wd d >= 9.
Proof.
  - destruct t as [c | c | c | c | c | c d | c m d | c m u].
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + pose proof (Wd_ge_9 d). cbn [W0 tree_c]. lia.
    + pose proof (Wd_ge_9 d). cbn [W0 tree_c]. lia.
    + pose proof (W0_ge_11 u). cbn [W0 tree_c]. lia.
  - destruct d as [c | c | c | c | c | c d2 | c m d2 | c m u2].
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + crush_arith.
    + pose proof (Wd_ge_9 d2). cbn [Wd]. lia.
    + pose proof (Wd_ge_9 d2). cbn [Wd]. lia.
    + pose proof (W0_ge_11 u2). cbn [Wd]. lia.
Qed.

Lemma Wd_ge_2c_9 (d : Tree) : d = endOne 1 \/ Wd d >= 2 * tree_c d + 9.
Proof.
  destruct d as [c | c | c | c | c | c d2 | c m d2 | c m u2].
  - right; crush_arith.
  - right; crush_arith.
  - destruct (Nat.eqb_spec c 1) as [-> | hne]; [left; reflexivity | right; crush_arith].
  - right; crush_arith.
  - right; crush_arith.
  - pose proof (Wd_ge_9 d2); right; cbn [Wd tree_c]; lia.
  - pose proof (Wd_ge_9 d2); right; cbn [Wd tree_c]; lia.
  - pose proof (W0_ge_11 u2); right; cbn [Wd tree_c]; lia.
Qed.

Lemma S_tree_iff_WF_r_core (k : nat) {u : Tree} (hu : WF_u u) :
  WF_r_core (add_c k u) <-> 2 * k + 20 >= S_tree u.
Proof.
  pose proof (WF_u_add_c k hu) as huk.
  unfold WF_r_core.
  split.
  - intros [_ h].
    destruct u as [c | c | c | c | c | c d | c m d | c m u2];
      try (pose proof (W0_ge_11 u2)); crush_arith.
  - intros h. split; [exact huk |].
    destruct u as [c | c | c | c | c | c d | c m d | c m u2];
      try (pose proof (W0_ge_11 u2)); crush_arith.
Qed.

Lemma sweepRV_app_1_odd (m : nat) {r : side} {rv : RVal}
    (hwf : WF_rv rv) (h : SweepRV r rv) :
  SweepRV ([S1; S1] ^^ m *> (S1 >> r)) (app_1_odd m rv).
Proof.
  destruct rv as [[u | d] | m0 p | m0 p].
  - cbn [SweepRV app_1_odd evalP] in *.
    pose proof (tree_c_pos_of_WF_u hwf) as hc.
    assert (h1 : Sweep F (S1 >> r) (evalT u)).
    { rewrite <- (cons_zero_tailT hc). exact (sweep_1_D h). }
    exact (sweep_11_pow_F m h1).
  - destruct hwf.
  - cbn [SweepRV app_1_odd] in *.
    pose proof (sweep_1_F h) as h1.
    rewrite <- (swap_1_11_pow m0 (evalP p)) in h1.
    pose proof (sweep_11_pow_A m h1) as h2.
    rewrite lpow_add, Str_app_assoc.
    exact h2.
  - cbn [SweepRV app_1_odd] in *.
    pose proof (sweep_1_A h) as h1.
    pose proof (sweep_11_pow_F m h1) as h2.
    replace (S (m + m0)) with (m + S m0) by lia.
    rewrite lpow_add, Str_app_assoc.
    cbn [lpow app Str_app].
    rewrite <- (swap_1_11_pow m0 (evalP p)).
    exact h2.
Qed.

Lemma WF_rv_app_1_odd (m : nat) {rv : RVal} (hwf : WF_rv rv) :
  WF_rv (app_1_odd m rv).
Proof.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]];
    try destruct m; cbn in *; tauto.
Qed.

Lemma sweepRV_app_1_even (m : nat) {r : side} {rv : RVal}
    (hwf : WF_rv rv) (h : SweepRV r rv) :
  SweepRV ([S1; S1] ^^ m *> r) (app_1_even m rv).
Proof.
  destruct m as [| m]; [exact h |].
  destruct rv as [[u | d] | m0 p | m0 p].
  - cbn [app_1_even SweepRV evalP] in *.
    pose proof (tree_c_pos_of_WF_u hwf) as hc.
    assert (h1 : Sweep F (S1 >> r) (evalT u)).
    { rewrite <- (cons_zero_tailT hc). exact (sweep_1_D h). }
    pose proof (sweep_1_F h1) as h2.
    pose proof (sweep_11_pow_A m h2) as h3.
    rewrite lpow_succ_r, Str_app_assoc.
    exact h3.
  - destruct hwf.
  - cbn [app_1_even SweepRV] in *.
    pose proof (sweep_11_pow_F (S m) h) as h1.
    rewrite lpow_add, Str_app_assoc.
    exact h1.
  - cbn [app_1_even SweepRV] in *.
    pose proof (sweep_11_pow_A (S m) h) as h1.
    rewrite lpow_add, Str_app_assoc.
    exact h1.
Qed.

Lemma WF_rv_app_1_even (m : nat) {rv : RVal} (hwf : WF_rv rv) :
  WF_rv (app_1_even m rv).
Proof.
  destruct m as [| m]; [exact hwf |].
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]]; cbn in *; tauto.
Qed.

(* ========================================================================== *)
(* 6. Base-Case Sweep & SweepRV Lemmas for Leaves and stop                    *)
(* ========================================================================== *)

Lemma sweep_01_pow_from_F_aux (k : nat) {r u : side} (h : Sweep F r u) :
  Sweep D ([S0; S1] ^^ S k *> r) (S1 >> ([S0; S1] ^^ k *> (S0 >> u))).
Proof.
  induction k as [| k ih].
  - cbn [lpow app Str_app]. exact (sweep_01_F h).
  - change ([S0; S1] ^^ S (S k) *> r) with (S0 >> S1 >> ([S0; S1] ^^ S k *> r)).
    change (S1 >> ([S0; S1] ^^ S k *> (S0 >> u))) with
      (S1 >> S0 >> S1 >> ([S0; S1] ^^ k *> (S0 >> u))).
    exact (sweep_01_D ih).
Qed.

Lemma sweep_01_pow_from_F (c : nat) (hc : c >= 1) {r u : side} (h : Sweep F r u) :
  Sweep D ([S0; S1] ^^ c *> r) (S1 >> ([S0; S1] ^^ (c - 1) *> (S0 >> u))).
Proof.
  pose proof (sweep_01_pow_from_F_aux (c - 1) h) as h1.
  replace (S (c - 1)) with c in h1 by lia.
  exact h1.
Qed.

Lemma sweep_01_pow_from_D (k : nat) {r u : side} (h : Sweep D r (S1 >> u)) :
  Sweep D ([S0; S1] ^^ k *> r) (S1 >> ([S0; S1] ^^ k *> u)).
Proof.
  induction k as [| k ih]; [exact h |].
  cbn [lpow app Str_app].
  exact (sweep_01_D ih).
Qed.

Lemma sweep_u_endZero (c : nat) (hc : c >= 1) :
  SweepRV (evalT (endZero c)) (R_D (P_tree (endStop c))).
Proof.
  unfold SweepRV, evalT, tailT, tree_c, evalCore.
  cbn [Str_app].
  exact (sweep_01_pow_from_F c hc sweep_default).
Qed.

Lemma sweep_u_stop_raw (c : nat) (hc : c >= 1) (r : side) :
  Sweep D ([S0; S1] ^^ c *> ([S0; S0; S1] *> r))
    (S1 >> ([S0; S1] ^^ c *> (S1 >> S0 >> r))).
Proof.
  pose proof (sweep_01_pow_from_F c hc (sweep_001 r)) as h1.
  replace ([S0; S1] ^^ c *> (S1 >> S0 >> r)) with
    ([S0; S1] ^^ (c - 1) *> (S0 >> S1 >> S1 >> S0 >> r)).
  - exact h1.
  - replace c with (S (c - 1)) at 2 by lia.
    rewrite lpow_succ_r, Str_app_assoc. reflexivity.
Qed.

Lemma sweep_u_endStop (c : nat) (hc : c >= 1) :
  SweepRV (evalT (endStop c)) (R_D (P_tree (endOne (c + 1)))).
Proof.
  unfold SweepRV, evalT, tailT, tree_c, evalCore.
  replace (c + 1 - 1) with c by lia.
  pose proof (sweep_u_stop_raw c hc 0inf) as h.
  cbn [Str_app] in *.
  rewrite cons_zero_0inf in h.
  exact h.
Qed.

Lemma sweep_u_stopOne (c : nat) (hc : c >= 1) :
  SweepRV (evalT (stopOne c)) (R_D (P_tree (od (c + 1) 0 (endOne 1)))).
Proof.
  unfold SweepRV, evalT, tailT, tree_c, evalCore.
  replace (c + 1 - 1) with c by lia.
  pose proof (sweep_u_stop_raw c hc ([S0; S1; S1] *> 0inf)) as h.
  cbn [lpow app Str_app] in *.
  exact h.
Qed.

Lemma sweep_u_stop (c : nat) (hc : c >= 1) (d : Tree) :
  SweepRV (evalT (stop c d)) (R_D (P_tree (od (c + 1) 0 d))).
Proof.
  unfold SweepRV, tailT, tree_c, evalCore.
  rewrite evalT_stop.
  replace (c + 1 - 1) with c by lia.
  cbn [lpow app Str_app].
  exact (sweep_u_stop_raw c hc (evalT d)).
Qed.

Lemma win_endOne_c1 :
  Sweep F ([S0; S1; S1] *> 0inf) ([S1; S1; S0; S1; S0; S0; S1] *> 0inf).
Proof.
  intro l.
  do 5 (rewrite (const_unfold sym S0) at 1).
  cbn [Str_app].
  fast_start_progress.
Qed.

Lemma sweep_u_endOne (c : nat) (hc : c >= 2) :
  SweepRV (evalT (endOne c)) (R_D (P_tree (oneEnd c))).
Proof.
  unfold SweepRV, evalT, tailT, tree_c, evalCore.
  pose proof (sweep_01_pow_from_F (c - 1) ltac:(lia) win_endOne_c1) as h1.
  replace ([S0; S1] ^^ c *> ([S1] *> 0inf)) with
    ([S0; S1] ^^ (c - 1) *> ([S0; S1; S1] *> 0inf)).
  2: {
    replace c with (S (c - 1)) at 2 by lia.
    rewrite lpow_succ_r, Str_app_assoc. reflexivity.
  }
  replace ([S0; S1] ^^ (c - 1) *> ([S1; S0; S1; S0; S0; S1] *> 0inf)) with
    ([S0; S1] ^^ (c - 1 - 1) *> (S0 >> ([S1; S1; S0; S1; S0; S0; S1] *> 0inf))).
  - exact h1.
  - replace (c - 1) with (S (c - 1 - 1)) at 2 by lia.
    rewrite lpow_succ_r, Str_app_assoc. reflexivity.
Qed.

Lemma win_oneEnd_c1 :
  Sweep D ([S0; S1; S1; S0; S1; S0; S0; S1] *> 0inf)
    (S1 >> ([S0; S0; S1; S0; S1; S1] *> 0inf)).
Proof.
  intro l.
  rewrite (const_unfold sym S0) at 1.
  cbn [Str_app].
  fast_start_progress.
Qed.

Lemma sweep_u_oneEnd (c : nat) (hc : c >= 2) :
  SweepRV (evalT (oneEnd c)) (R_D (P_tree (stopOne c))).
Proof.
  unfold SweepRV, evalT, tailT, tree_c, evalCore.
  pose proof (sweep_01_pow_from_D (c - 1) win_oneEnd_c1) as h1.
  replace ([S0; S1] ^^ c *> ([S1; S0; S1; S0; S0; S1] *> 0inf)) with
    ([S0; S1] ^^ (c - 1) *> ([S0; S1; S1; S0; S1; S0; S0; S1] *> 0inf)).
  - exact h1.
  - replace c with (S (c - 1)) at 2 by lia.
    rewrite lpow_succ_r, Str_app_assoc. reflexivity.
Qed.

Lemma sweep_d0_endZero :
  SweepRV (S0 >> evalT (endZero 0)) (R_F 0 (P_tree (endZero 1))).
Proof.
  cbn [SweepRV evalP evalT tree_c evalCore lpow app Str_app].
  rewrite cons_zero_0inf.
  exact sweep_default.
Qed.

Lemma sweep_d0_endStop :
  SweepRV (S0 >> evalT (endStop 0)) (R_F 0 (P_tree (endZero 2))).
Proof.
  cbn [SweepRV evalP evalT tree_c evalCore lpow app Str_app].
  exact (sweep_000 (S1 >> 0inf)).
Qed.

Lemma sweep_d0_endOne :
  SweepRV (S0 >> evalT (endOne 0)) (R_D (P_tree (endStop 1))).
Proof.
  change (S0 >> evalT (endOne 0)) with (evalT (endZero 1)).
  exact (sweep_u_endZero 1 ltac:(lia)).
Qed.

Lemma sweep_d0_oneEnd :
  SweepRV (S0 >> evalT (oneEnd 0)) (R_D (P_tree (endOne 3))).
Proof.
  change (S0 >> evalT (oneEnd 0)) with (evalT (endStop 2)).
  exact (sweep_u_endStop 2 ltac:(lia)).
Qed.

Lemma sweep_d0_stopOne :
  SweepRV (S0 >> evalT (stopOne 0)) (R_F 0 (P_tree (endOne 3))).
Proof.
  cbn [SweepRV evalP evalT tree_c evalCore lpow app Str_app].
  exact (sweep_000 ([S1; S0; S1; S1] *> 0inf)).
Qed.

Lemma sweep_d0_stop_any (d : Tree) :
  SweepRV (S0 >> evalT (stop 0 d)) (R_F 0 (P_tree (add_c 2 d))).
Proof.
  unfold SweepRV, evalP.
  rewrite evalT_stop.
  cbn [lpow app Str_app].
  assert (h2 : add_c 2 d = add_c 1 (add_c 1 d)).
  { destruct d; unfold add_c, set_c, tree_c; f_equal; lia. }
  rewrite h2, evalT_add_c_one, evalT_add_c_one.
  exact (sweep_000 (S1 >> evalT d)).
Qed.

Lemma add_c_sub_c_one {t : Tree} (hpos : tree_c t >= 1) :
  add_c 1 (sub_c 1 t) = t.
Proof.
  destruct t; unfold add_c, sub_c, set_c, tree_c in *; f_equal; lia.
Qed.

Lemma sweep_d0_od_pos (m2 : nat) {d2 : Tree} (hpos : tree_c d2 >= 1) :
  SweepRV (S0 >> evalT (od 0 m2 d2)) (R_D (P_tree (od 2 m2 (sub_c 1 d2)))).
Proof.
  unfold SweepRV.
  rewrite evalT_od.
  cbn [lpow app Str_app].
  assert (hd2 : evalT d2 = S0 >> S1 >> evalT (sub_c 1 d2)).
  { rewrite <- evalT_add_c_one, (add_c_sub_c_one hpos). reflexivity. }
  rewrite hd2.
  rewrite (swap_1_11_pow m2 (S0 >> S0 >> S1 >> evalT (sub_c 1 d2))).
  pose proof (sweep_01_F (sweep_11_pow_F m2 (sweep_001 (evalT (sub_c 1 d2))))) as h3.
  unfold tailT, evalCore, tree_c.
  cbn [Nat.sub lpow app Str_app] in *.
  rewrite (swap_1_11_pow m2 (S1 >> S0 >> evalT (sub_c 1 d2))) in h3.
  exact h3.
Qed.

Lemma sweep_P_od_pos {d : Tree} (hpos : tree_c d >= 1) :
  SweepRV (evalP (P_od d)) (R_F 1 (P_od (sub_c 1 d))).
Proof.
  unfold SweepRV, evalP.
  assert (hd : evalT d = S0 >> S1 >> evalT (sub_c 1 d)).
  { rewrite <- evalT_add_c_one, (add_c_sub_c_one hpos). reflexivity. }
  rewrite hd.
  cbn [lpow app Str_app].
  exact (sweep_001 (evalT (sub_c 1 d))).
Qed.

(* ========================================================================== *)
(* 7. Single-Step 01 on RVal (sweepRV_01_* and bump_ra)                       *)
(* ========================================================================== *)

Lemma sweepRV_01_RD {t : Tree} {r : side} (ht : WF_u t)
    (h : SweepRV r (R_D (P_tree t))) :
  SweepRV (S0 >> S1 >> r) (R_D (P_tree (add_c 1 t))).
Proof.
  cbn [SweepRV] in *.
  rewrite (tailT_add_c_one (tree_c_pos_of_WF_u ht)).
  exact (sweep_01_D h).
Qed.

Lemma sweepRV_01_RF0 {u : Tree} {r : side} (hu : WF_u u)
    (h : SweepRV r (R_F 0 (P_tree u))) :
  SweepRV (S0 >> S1 >> r) (R_D (P_tree (mk_stop 1 (sub_c 1 u)))).
Proof.
  cbn [SweepRV evalP lpow app Str_app] in *.
  pose proof (tree_c_pos_of_WF_u hu) as hc.
  assert (hu_eq : evalT u = S0 >> S1 >> evalT (sub_c 1 u)).
  { rewrite <- evalT_add_c_one, (add_c_sub_c_one hc). reflexivity. }
  rewrite hu_eq in h.
  rewrite (tailT_mk_stop 1 ltac:(lia) (sub_c 1 u)).
  cbn [Nat.sub lpow app Str_app].
  exact (sweep_01_F h).
Qed.

Lemma sweepRV_01_RF_tree (m : nat) {u : Tree} {r : side}
    (h : SweepRV r (R_F (S m) (P_tree u))) :
  SweepRV (S0 >> S1 >> r) (R_D (P_tree (mk_sh 2 m u))).
Proof.
  cbn [SweepRV evalP] in *.
  rewrite (tailT_mk_sh 2 m ltac:(lia) u).
  cbn [Nat.sub lpow app Str_app] in *.
  rewrite (swap_1_11_pow m (evalT u)).
  exact (sweep_01_F h).
Qed.

Lemma sweepRV_01_RF_od (m : nat) {d : Tree} {r : side}
    (h : SweepRV r (R_F (S m) (P_od d))) :
  SweepRV (S0 >> S1 >> r) (R_D (P_tree (od 2 m d))).
Proof.
  cbn [SweepRV evalP lpow app Str_app] in h.
  unfold SweepRV.
  change (tailT (od 2 m d)) with
    (S1 >> S0 >> S1 >> ([S1; S1] ^^ m *> (S1 >> S0 >> evalT d))).
  rewrite (swap_1_11_pow m (S0 >> evalT d)).
  exact (sweep_01_F h).
Qed.

Lemma sweepRV_01_RA (m : nat) {p : Payload} {rv0 : RVal} {r : side}
    (hwf0 : WF_rv rv0) (h1 : SweepRV r (R_A m p)) (h0 : SweepRV (evalP p) rv0) :
  SweepRV (S0 >> S1 >> r) (bump_ra (app_1_odd m rv0)).
Proof.
  cbn [SweepRV] in h1.
  pose proof (sweepRV_app_1_odd m hwf0 h0) as h2.
  destruct (app_1_odd m rv0) as [p2 | m2 p2 | m2 p2] eqn:hrv2.
  - destruct rv0; discriminate hrv2.
  - cbn [SweepRV bump_ra lpow app Str_app] in *.
    exact (sweep_01_A_F h1 h2).
  - cbn [SweepRV bump_ra lpow app Str_app] in *.
    exact (sweep_01_A_A h1 h2).
Qed.

Lemma WF_rv_bump_ra {rv2 : RVal} (hwf2 : WF_rv rv2)
    (hnotD : forall p, rv2 <> R_D p) : WF_rv (bump_ra rv2).
Proof.
  destruct rv2 as [p | [| m] [u | d] | m [u | d]];
    [exfalso; exact (hnotD p eq_refl) | ..]; cbn in *; tauto.
Qed.

Lemma app_1_odd_ne_RD (m : nat) (rv : RVal) (p : Payload) :
  app_1_odd m rv <> R_D p.
Proof. destruct rv; discriminate. Qed.

(* ========================================================================== *)
(* 8. Universal Arithmetic Sub-Lemmas for W_rv, W_safe, and S_rv              *)
(* ========================================================================== *)

Lemma W0_lin_eq (t : Tree) :
  (t = endStop 1 /\ W0_lin t = 12 /\ W0 t = 11) \/
  (t <> endStop 1 /\ W0_lin t = W0 t).
Proof.
  unfold W0_lin.
  destruct (tree_eqb_spec t (endStop 1)) as [-> | hne].
  - left; cbn; auto.
  - right; auto.
Qed.

Lemma W0_lin_add_c_one {u : Tree} (hu : WF_u u) :
  W0_lin (add_c 1 u) = W0_lin u + 2.
Proof.
  destruct u; crush_arith.
Qed.

Lemma S_tree_add_c_one {u : Tree} (hu : WF_u u) :
  S_tree (add_c 1 u) = S_tree u - 2.
Proof.
  destruct u; crush_arith.
Qed.

Lemma Wd_sub_c_one_le {u : Tree} (hu : WF_u u) :
  Wd (sub_c 1 u) <= W0 u + 2.
Proof.
  destruct u; crush_arith.
Qed.

Lemma W_rv_RF0_spec {u : Tree} (hu : WF_u u) :
  W0_lin (mk_stop 1 (sub_c 1 u)) <= W_rv (R_F 0 (P_tree u)) + 2.
Proof.
  cbn [W_rv].
  destruct (tree_eqb_spec u (endZero 1)) as [-> | h1]; [crush_arith |].
  destruct (tree_eqb_spec u (endOne 2)) as [-> | h2]; [crush_arith |].
  pose proof (W0_ge_11 (mk_stop 1 (sub_c 1 u))) as hge.
  destruct (W0_lin_eq (mk_stop 1 (sub_c 1 u))) as [[_ [hl _]] | [_ hl]]; lia.
Qed.

Lemma W_rv_RF_pos_tree_spec (m : nat) {u : Tree} (hu : WF_u u) :
  W0_lin (mk_sh 2 m u) <= W_rv (R_F (S m) (P_tree u)) + 2.
Proof.
  cbn [W_rv].
  destruct (Nat.eqb_spec m 0) as [-> | hm].
  - destruct (tree_eqb_spec u (endStop 1)) as [-> | h1]; [crush_arith |].
    pose proof (W0_ge_11 (mk_sh 2 0 u)) as hge.
    destruct (W0_lin_eq (mk_sh 2 0 u)) as [[_ [hl _]] | [_ hl]]; lia.
  - pose proof (W0_ge_11 (mk_sh 2 m u)) as hge.
    destruct (W0_lin_eq (mk_sh 2 m u)) as [[_ [hl _]] | [_ hl]]; lia.
Qed.

Ltac pose_tree_bounds :=
  repeat match goal with
  | u : Tree |- _ =>
      lazymatch goal with
      | _ : W0 u >= _ |- _ => fail
      | _ => pose proof (W0_ge_11 u); pose proof (Wd_ge_9 u)
      end
  end.

Lemma W_rv_app_1_even_le (m : nat) {rv : RVal} (hwf : WF_rv rv) :
  W_rv (app_1_even m rv) <= 2 * m + 2 + W_rv rv.
Proof.
  destruct m as [| m]; [cbn [app_1_even]; lia |].
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [w | d]].
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - pose proof (Wd_sub_c_one_le hwf) as hsub.
    destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - pose_tree_bounds; crush_arith.
  - destruct w; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma W_rv_app_1_odd_le_4 (M : nat) {rv : RVal} (hwf : WF_rv rv) :
  W_rv (app_1_odd M rv) <= 2 * M + 4 + W_rv rv.
Proof.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]].
  - destruct M as [| M].
    + pose proof (Wd_sub_c_one_le hwf) as hsub.
      destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma S_rv_app_1_odd_le (M : nat) {rv : RVal} (hwf : WF_rv rv) :
  S_rv (app_1_odd M rv) <= Nat.max 24 (evenCeil (W_rv rv + 9)).
Proof.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]].
  - destruct M as [| M].
    + pose proof (Wd_sub_c_one_le hwf) as hsub.
      destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma bump_ra_bounds {rv2 : RVal} (hwf2 : WF_rv rv2)
    (hnotD : forall p, rv2 <> R_D p)
    (hnotBad : rv2 <> R_F 0 (P_tree (endZero 1)) /\
               rv2 <> R_F 0 (P_tree (endOne 2))) :
  NotBadRD (bump_ra rv2) /\
  W_rv (bump_ra rv2) <= W_rv rv2 + 2 /\
  S_rv (bump_ra rv2) <= S_rv rv2 /\
  (forall M,
    W_rv (app_1_odd M (bump_ra rv2)) <= 2 * M + 4 + W_rv rv2 /\
    S_rv (app_1_odd M (bump_ra rv2)) <= Nat.max 24 (evenCeil (W_rv rv2 + 9))).
Proof.
  destruct rv2 as [p | [| m] [u | d] | m [w | d]].
  - exfalso; exact (hnotD p eq_refl).
  - destruct hnotBad as [hnez hneo].
    refine (conj _ (conj _ (conj _ _))); [split; discriminate | | | intro M; split].
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf2.
  - refine (conj _ (conj _ (conj _ _))); [split; discriminate | | | intro M; split].
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - refine (conj _ (conj _ (conj _ _))); [split; discriminate | | | intro M; split].
    + pose_tree_bounds; crush_arith.
    + pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
  - refine (conj _ (conj _ (conj _ _))); [split; discriminate | | | intro M; split].
    + destruct w; pose_tree_bounds; crush_arith.
    + crush_arith.
    + destruct w; pose_tree_bounds; crush_arith.
    + destruct w; pose_tree_bounds; crush_arith.
  - refine (conj _ (conj _ (conj _ _))); [split; discriminate | | | intro M; split].
    + destruct d; pose_tree_bounds; crush_arith.
    + crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma bump_ra_app_1_odd (m : nat) (rv0 : RVal) :
  bump_ra (app_1_odd m rv0) = app_1_odd (S m) rv0.
Proof.
  destruct rv0; reflexivity.
Qed.

Lemma evenCeil_mono {x y : nat} (h : x <= y) : evenCeil x <= evenCeil y.
Proof. unfold evenCeil; lia. Qed.

Lemma evenCeil_ge (x : nat) : evenCeil x >= x.
Proof. unfold evenCeil; lia. Qed.

Lemma goodRV_of_odd (m : nat) {rv0 : RVal}
    (hnb : m = 0 -> rv0 <> R_D (P_tree (endZero 1))) :
  GoodRV (app_1_odd m rv0).
Proof.
  destruct rv0 as [[t | d] | m0 p | m0 p]; [| destruct m; exact I | exact I | exact I].
  destruct m as [| m]; [| exact I].
  destruct t as [c | c | c | c | c | c d | c m2 d | c m2 u]; try exact I.
  destruct c as [| [| c]]; [exact I | exact (hnb eq_refl eq_refl) | exact I].
Qed.

Lemma notBadRD_app_1_odd (m : nat) (rv0 : RVal) : NotBadRD (app_1_odd m rv0).
Proof.
  destruct rv0; split; discriminate.
Qed.

Lemma odd_of_app_1_odd_pos (M m : nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
  W_rv (app_1_odd M (app_1_odd (S m) rv0)) <=
    2 * M + 2 + W_rv (app_1_odd (S m) rv0).
Proof.
  destruct rv0 as [[u | d] | [| m0] [u | d] | m0 [u | d]].
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf0.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf0.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma notBad_of_odd (m : nat) {rv0 : RVal}
    (hnb : m = 0 -> NotBadRD rv0) :
  app_1_odd m rv0 <> R_F 0 (P_tree (endZero 1)) /\
  app_1_odd m rv0 <> R_F 0 (P_tree (endOne 2)).
Proof.
  destruct rv0 as [p | m0 p | m0 p].
  - destruct m as [| m].
    + destruct (hnb eq_refl) as [h1 h2].
      cbn [app_1_odd]; split; congruence.
    + cbn [app_1_odd]; split; discriminate.
  - cbn [app_1_odd]; split; discriminate.
  - cbn [app_1_odd]; split; discriminate.
Qed.

Lemma W_safe_ge_W_rv {rv : RVal} : W_rv rv <= W_safe rv.
Proof.
  destruct rv as [[t | d] | [| m] [t | d] | m [t | d]];
    try destruct t; try destruct d; crush_arith.
Qed.

Lemma W_safe_app_1_even_pos (m : nat) {rv : RVal} (hwf : WF_rv rv) :
  W_safe (app_1_even (S m) rv) <= 2 * S m + 2 + W_rv rv.
Proof.
  pose proof (W_rv_app_1_even_le (S m) hwf) as he.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [w | d]].
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - pose proof (Wd_sub_c_one_le hwf) as hsub.
    destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - destruct u; pose_tree_bounds; crush_arith.
  - pose_tree_bounds; crush_arith.
  - destruct w; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma W_safe_app_1_odd_le_4 (M : nat) {rv : RVal} (hwf : WF_rv rv)
    (hnf0 : forall p, rv <> R_F 0 p)
    (hne2 : rv <> R_D (P_tree (endOne 2))) :
  W_safe (app_1_odd M rv) <= 2 * M + 4 + W_rv rv.
Proof.
  pose proof (W_rv_app_1_odd_le_4 M hwf) as ho.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]].
  - destruct M as [| M]; destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - exfalso; exact (hnf0 (P_tree u) eq_refl).
  - exfalso; exact (hnf0 (P_od d) eq_refl).
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma odd_wsafe_of_app_1_odd_pos (M m : nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
  W_safe (app_1_odd M (app_1_odd (S m) rv0)) <=
    2 * M + 2 + W_rv (app_1_odd (S m) rv0).
Proof.
  pose proof (odd_of_app_1_odd_pos M m hwf0) as ho.
  destruct rv0 as [[u | d] | [| m0] [u | d] | m0 [u | d]];
    try destruct u; try destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma W_safe_bump_ra_odd (m : nat) {rv0 : RVal} (hwf0 : WF_rv rv0)
    (hnb0 : m = 0 -> NotBadRD rv0) :
  W_safe (bump_ra (app_1_odd m rv0)) <= W_rv (app_1_odd m rv0) + 2.
Proof.
  pose proof (WF_rv_app_1_odd m hwf0) as hwf2.
  pose proof (app_1_odd_ne_RD m rv0) as hnd2.
  pose proof (notBad_of_odd m hnb0) as hnb2.
  destruct (bump_ra_bounds hwf2 hnd2 hnb2) as [_ [hb _]].
  rewrite bump_ra_app_1_odd in hb |- *.
  destruct rv0 as [[u | d] | m0 [u | d] | m0 [u | d]].
  - destruct m as [| m].
    + destruct (hnb0 eq_refl) as [h1 h2].
      destruct u; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf0.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma not_badRV_of_W_safe_le (rem M : nat) {rv : RVal} (hwf : WF_rv rv)
    (hnf0 : forall p, rv <> R_F 0 p)
    (hrem : rem >= 1) (hsafe : W_safe rv <= 2 * rem + 13) :
  ~ BadRV rem (app_1_odd M rv).
Proof.
  destruct rv as [[u | d] | [| m0] [u | d] | m0 [u | d]].
  - destruct M as [| M].
    + destruct u as [c | c | c | c | c | c d2 | c m2 d2 | c m2 u2];
        try destruct d2; pose_tree_bounds; crush_arith.
    + destruct u; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - exfalso; exact (hnf0 (P_tree u) eq_refl).
  - exfalso; exact (hnf0 (P_od d) eq_refl).
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct u; pose_tree_bounds; crush_arith.
  - destruct d as [cd | cd | cd | cd | cd | cd d2 | cd m2 d2 | cd m2 u2];
      try destruct d2; pose_tree_bounds; crush_arith.
Qed.

(* ========================================================================== *)
(* 9. Inductive Predicates PostU, PostD0, PostRV and Iteration Lemmas         *)
(* ========================================================================== *)

Definition PostRV (rv rvn : RVal) : Prop :=
  (forall r, SweepRV r rv -> SweepRV (S0 >> S1 >> r) rvn) /\
  WF_rv rvn /\
  NotBadRD rvn /\
  (forall p, rvn <> R_F 0 p) /\
  W_rv rvn <= W_rv rv + 2 /\
  W_safe rvn <= W_safe rv + 2 /\
  S_rv rvn <= S_rv rv - 2 /\
  (forall rem, S_rv rv <= 20 + 2 * S rem -> ~ BadRV (S rem) rv -> ~ BadRV rem rvn) /\
  (GoodRV rv -> GoodRV rvn) /\
  (GoodRV rv -> forall M,
    W_rv (app_1_odd M rvn) <= 2 * M + 4 + W_rv rv /\
    W_safe (app_1_odd M rvn) <= 2 * M + 4 + W_rv rv /\
    S_rv (app_1_odd M rvn) <= Nat.max 24 (evenCeil (W_rv rv + 9))).

Definition PostU (u : Tree) : Prop :=
  exists rv, SweepRV (evalT u) rv /\
    WF_rv rv /\
    (u <> endStop 1 -> NotBadRD rv) /\
    (forall p, rv <> R_F 0 p) /\
    W_rv rv <= W0 u + 2 /\
    W_safe rv <= (if isLeaf u then W0 u + 4 else W0 u + 2) /\
    (forall m, ~ (m = 0 /\ u = endStop 1) ->
      W_rv (app_1_odd m rv) <= 2 * m + 4 + W0 u /\
      W_safe (app_1_odd m rv) <= 2 * m + 4 + W0 u /\
      S_rv (app_1_odd m rv) <= Nat.max 24 (evenCeil (W0 u + 9))) /\
    (forall c m, (if isLeaf u then c >= 2 else c >= 1) ->
      ~ (m = 0 /\ u = endStop 1) ->
      W0 u <= 2 * c + 11 -> ~ BadRoot (sh c m u) -> ~ BadRV c (app_1_odd m rv)) /\
    (WF_r u -> exists tn, rv = R_D (P_tree tn) /\ WF_r tn).

Definition PostD0 (d0 : Tree) : Prop :=
  exists rv, SweepRV (S0 >> evalT d0) rv /\
    WF_rv rv /\
    NotBadRD rv /\
    (d0 <> endStop 0 -> W_rv rv <= Wd d0 + 4 /\ W_safe rv <= Wd d0 + 6) /\
    (forall m2, W_rv (app_1_even m2 rv) <= 2 * m2 + 6 + Wd d0 /\
                W_safe (app_1_even m2 rv) <= 2 * m2 + 6 + Wd d0) /\
    (forall cd m,
      let df := set_c cd d0 in
      W_rv (app_1_odd (m + 2 * cd) rv) <= 2 * m + 2 * cd + 6 + Wd df /\
      W_safe (app_1_odd (m + 2 * cd) rv) <= 2 * m + 2 * cd + 6 + Wd df /\
      S_rv (app_1_odd (m + 2 * cd) rv) <=
        Nat.max (if tree_eqb df (endZero 1) then 26 - 2 * cd
                 else Nat.max 20 (24 - 2 * cd))
                (evenCeil (Wd df + 11 + stopOnePosBonus df - 2 * cd)) /\
      (forall rem, rem >= 1 -> cd + rem >= 2 ->
        Wd df + stopOnePosBonus df <= 2 * (cd + rem) + 9 ->
        ~ BadRoot (od (cd + rem) m df) ->
        ~ BadRV rem (app_1_odd (m + 2 * cd) rv))).

Lemma S_rv_RD_of_le_20 {rv : RVal} (hwf : WF_rv rv)
    (hs : S_rv rv <= 20) (hnb0 : ~ BadRV 0 rv) :
  exists tn, rv = R_D (P_tree tn) /\ WF_r tn.
Proof.
  destruct rv as [[tn | d] | [| m] [u | d] | m [w | d]].
  - exists tn; split; [reflexivity |].
    split.
    + pose proof (S_tree_iff_WF_r_core 0 hwf) as [_ h0].
      assert (had : add_c 0 tn = tn).
      { destruct tn; unfold add_c, set_c, tree_c; f_equal; lia. }
      rewrite had in h0.
      apply h0. cbn [S_rv] in hs; lia.
    + cbn [BadRV Nat.eqb] in hnb0; exact hnb0.
  - destruct hwf.
  - cbn [S_rv] in hs; lia.
  - cbn [S_rv] in hs; lia.
  - cbn [S_rv] in hs; lia.
  - cbn [S_rv] in hs; lia.
  - destruct w; cbn [S_rv S_ra_tree] in hs; lia.
  - destruct d; cbn [S_rv S_ra_od] in hs; lia.
Qed.

Lemma iter_app_01_pos (k B : nat)
    (ih_step : forall rv', WF_rv rv' -> W_rv rv' <= B -> exists rvn, PostRV rv' rvn) :
  forall (r : side) (rv : RVal),
    SweepRV r rv ->
    WF_rv rv ->
    GoodRV rv ->
    W_rv rv + 2 * k <= B ->
    exists rvf,
      SweepRV ([S0; S1] ^^ S k *> r) rvf /\
      WF_rv rvf /\
      NotBadRD rvf /\
      (forall p, rvf <> R_F 0 p) /\
      GoodRV rvf /\
      W_rv rvf <= W_rv rv + 2 * S k /\
      W_safe rvf <= W_safe rv + 2 * S k /\
      S_rv rvf <= S_rv rv - 2 * S k /\
      (S_rv rv <= 20 + 2 * S k -> ~ BadRV (S k) rv -> ~ BadRV 0 rvf) /\
      (forall M,
        W_rv (app_1_odd M rvf) <= 2 * M + 4 + W_rv rv + 2 * k /\
        W_safe (app_1_odd M rvf) <= 2 * M + 4 + W_rv rv + 2 * k /\
        S_rv (app_1_odd M rvf) <= Nat.max 24 (evenCeil (W_rv rv + 2 * k + 9))).
Proof.
  induction k as [| k ih]; intros r rv hsw hwf hgood hw.
  - destruct (ih_step rv hwf ltac:(lia)) as
      [rv1 [hstep1 [hwf1 [hnb1 [hnf1 [hw1 [hws1 [hs1 [hbad1 [hgood1 hodd1]]]]]]]]]].
    exists rv1.
    refine (conj _ (conj hwf1 (conj hnb1 (conj hnf1 (conj (hgood1 hgood)
      (conj _ (conj _ (conj _ (conj _ _))))))))); try lia.
    + cbn [lpow app Str_app]. exact (hstep1 r hsw).
    + intros hs hnb. exact (hbad1 0 ltac:(lia) hnb).
    + intro M. destruct (hodd1 hgood M) as [how [hows hos]].
      replace (W_rv rv + 2 * 0 + 9) with (W_rv rv + 9) by lia.
      split; [lia | split; [lia | exact hos]].
  - destruct (ih_step rv hwf ltac:(lia)) as
      [rv1 [hstep1 [hwf1 [_ [_ [hw1 [hws1 [hs1 [hbad1 [hgood1 _]]]]]]]]]].
    pose proof (hstep1 r hsw) as hsw1.
    destruct (ih (S0 >> S1 >> r) rv1 hsw1 hwf1 (hgood1 hgood) ltac:(lia)) as
      [rvf [hswf [hwff [hnbf [hnff [hgoodf [hwf_w [hwf_ws [hwf_s [hbad_f hodd_f]]]]]]]]]].
    exists rvf.
    refine (conj _ (conj hwff (conj hnbf (conj hnff (conj hgoodf
      (conj _ (conj _ (conj _ (conj _ _))))))))); try lia.
    + rewrite lpow_succ_r, Str_app_assoc.
      cbn [Str_app]. exact hswf.
    + intros hs hnb.
      exact (hbad_f ltac:(lia) (hbad1 (S k) ltac:(lia) hnb)).
    + intro M. destruct (hodd_f M) as [how [hows hos]].
      pose proof (evenCeil_mono (x := W_rv rv1 + 2 * k + 9)
                                (y := W_rv rv + 2 * S k + 9) ltac:(lia)) as hmon.
      split; [lia | split; [lia | lia]].
Qed.

(* ========================================================================== *)
(* 10. Base Leaf and stop Proofs of PostU and PostD0                          *)
(* ========================================================================== *)

Lemma postU_endZero (c : nat) (hc : c >= 1) : PostU (endZero c).
Proof.
  exists (R_D (P_tree (endStop c))).
  refine (conj (sweep_u_endZero c hc) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - cbn; lia.
  - intro; split; discriminate.
  - intro; discriminate.
  - crush_arith.
  - crush_arith.
  - intros [| m] _; repeat split; crush_arith.
  - intros c' [| m] hc' _ hw0 hnbr; crush_arith.
  - intro. exists (endStop c); split; [reflexivity | crush_arith].
Qed.

Lemma postU_endStop (c : nat) (hc : c >= 1) : PostU (endStop c).
Proof.
  exists (R_D (P_tree (endOne (c + 1)))).
  refine (conj (sweep_u_endStop c hc) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - cbn; lia.
  - intro hne; assert (c <> 1) by congruence; crush_arith.
  - intro; discriminate.
  - crush_arith.
  - crush_arith.
  - intros [| m] hm;
      [assert (c <> 1) by (intro; subst; apply hm; auto) |];
      repeat split; crush_arith.
  - intros c' [| m] hc' hm hw0 hnbr;
      [assert (c <> 1) by (intro; subst; apply hm; auto) |];
      crush_arith.
  - intro. exists (endOne (c + 1)); split; [reflexivity | crush_arith].
Qed.

Lemma postU_endOne (c : nat) (hc : c >= 2) : PostU (endOne c).
Proof.
  exists (R_D (P_tree (oneEnd c))).
  refine (conj (sweep_u_endOne c hc) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - cbn; lia.
  - intro; split; discriminate.
  - intro; discriminate.
  - crush_arith.
  - crush_arith.
  - intros [| m] _; repeat split; crush_arith.
  - intros c' [| m] hc' _ hw0 hnbr; crush_arith.
  - intro. exists (oneEnd c); split; [reflexivity | crush_arith].
Qed.

Lemma postU_oneEnd (c : nat) (hc : c >= 2) : PostU (oneEnd c).
Proof.
  exists (R_D (P_tree (stopOne c))).
  refine (conj (sweep_u_oneEnd c hc) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - cbn; lia.
  - intro; split; discriminate.
  - intro; discriminate.
  - crush_arith.
  - crush_arith.
  - intros [| m] _; repeat split; crush_arith.
  - intros c' [| m] hc' _ hw0 hnbr; crush_arith.
  - intro. exists (stopOne c); split; [reflexivity | crush_arith].
Qed.

Lemma postU_stopOne (c : nat) (hc : c >= 1) : PostU (stopOne c).
Proof.
  exists (R_D (P_tree (od (c + 1) 0 (endOne 1)))).
  refine (conj (sweep_u_stopOne c hc) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - cbn; split; [lia | exact I].
  - intro; split; discriminate.
  - intro; discriminate.
  - crush_arith.
  - crush_arith.
  - intros [| m] _; repeat split; crush_arith.
  - intros c' m hc' _ hw0 _.
    cbn [isLeaf] in hc'.
    apply (not_badRV_of_W_safe_le c' m);
      [cbn; split; [lia | exact I] | intro; discriminate | lia | crush_arith].
  - intro hr. exists (od (c + 1) 0 (endOne 1)); split; [reflexivity | crush_arith].
Qed.

Lemma postU_stop (c : nat) (d : Tree) (hwf : WF_u (stop c d)) : PostU (stop c d).
Proof.
  destruct hwf as [hc [hd0 [hd1 hd]]].
  pose proof (Wd_ge_9 d) as hwd.
  assert (hwf_rv : WF_rv (R_D (P_tree (od (c + 1) 0 d)))).
  { cbn; split; [lia | exact hd]. }
  assert (hws_le : W_safe (R_D (P_tree (od (c + 1) 0 d))) <= W0 (stop c d) + 2) by crush_arith.
  exists (R_D (P_tree (od (c + 1) 0 d))).
  refine (conj (sweep_u_stop c hc d) (conj hwf_rv (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))).
  - intro; split; discriminate.
  - intro; discriminate.
  - crush_arith.
  - cbn [isLeaf]; exact hws_le.
  - intros [| m] _; repeat split; crush_arith.
  - intros c' m hc' _ hw0 _.
    cbn [isLeaf] in hc'.
    apply (not_badRV_of_W_safe_le c' m hwf_rv);
      [intro; discriminate | exact hc' | lia].
  - intros [[_ [hc2 hwd_le]] hnbr].
    exists (od (c + 1) 0 d); split; [reflexivity |].
    split; [split; [cbn; split; [lia | exact hd] | split] |].
    + crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d as [cd | cd | cd | cd | cd | cd d2 | cd m2 d2 | cd m2 u2];
        try destruct d2; crush_arith.
Qed.

Lemma postD0_endZero : PostD0 (endZero 0).
Proof.
  exists (R_F 0 (P_tree (endZero 1))).
  refine (conj sweep_d0_endZero (conj _ (conj _ (conj _ (conj _ _))))).
  - cbn; lia.
  - split; discriminate.
  - intro; crush_arith.
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))); [crush_arith | crush_arith | crush_arith |].
    intros rem hrem _ _ _; crush_arith.
Qed.

Lemma postD0_endStop : PostD0 (endStop 0).
Proof.
  exists (R_F 0 (P_tree (endZero 2))).
  refine (conj sweep_d0_endStop (conj _ (conj _ (conj _ (conj _ _))))).
  - cbn; lia.
  - split; discriminate.
  - intro h; exfalso; exact (h eq_refl).
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))); [crush_arith | crush_arith | crush_arith |].
    intros rem hrem _ _ _; crush_arith.
Qed.

Lemma postD0_endOne : PostD0 (endOne 0).
Proof.
  exists (R_D (P_tree (endStop 1))).
  refine (conj sweep_d0_endOne (conj _ (conj _ (conj _ (conj _ _))))).
  - cbn; lia.
  - split; discriminate.
  - intro; crush_arith.
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))).
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + intros rem hrem _ _ _.
      destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
Qed.

Lemma postD0_oneEnd : PostD0 (oneEnd 0).
Proof.
  exists (R_D (P_tree (endOne 3))).
  refine (conj sweep_d0_oneEnd (conj _ (conj _ (conj _ (conj _ _))))).
  - cbn; lia.
  - split; discriminate.
  - intro; crush_arith.
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))).
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + intros rem hrem hcd2 hwd hnbr.
      destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
Qed.

Lemma postD0_stopOne : PostD0 (stopOne 0).
Proof.
  exists (R_F 0 (P_tree (endOne 3))).
  refine (conj sweep_d0_stopOne (conj _ (conj _ (conj _ (conj _ _))))).
  - cbn; lia.
  - split; discriminate.
  - intro; crush_arith.
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _)));
      [crush_arith | crush_arith | crush_arith | intros rem hrem hcd2 hwd hnbr; crush_arith].
Qed.

Lemma postD0_stop {d : Tree} (hwf : WF_d (stop 0 d)) : PostD0 (stop 0 d).
Proof.
  destruct hwf as [hd0 [hd1 hd]].
  assert (hu2 : WF_u (add_c 2 d)).
  { destruct d; unfold add_c, set_c, tree_c; cbn in *; intuition lia. }
  pose proof (Wd_ge_9 d) as hwd.
  assert (hsub2 : sub_c 1 (add_c 2 d) = add_c 1 d).
  { destruct d; unfold sub_c, add_c, set_c, tree_c; f_equal; lia. }
  assert (hrf0 : W_rv (R_F 0 (P_tree (add_c 2 d))) <= Wd d + 7).
  { destruct d; pose_tree_bounds; crush_arith. }
  assert (hrf0_safe : W_safe (R_F 0 (P_tree (add_c 2 d))) <= Wd d + 9).
  { destruct d; pose_tree_bounds; crush_arith. }
  exists (R_F 0 (P_tree (add_c 2 d))).
  refine (conj (sweep_d0_stop_any d) (conj hu2 (conj _ (conj _ (conj _ _))))).
  - split; discriminate.
  - intro; cbn [Wd]; lia.
  - intros [| m2].
    + cbn [app_1_even Wd]; lia.
    + pose proof (W_rv_app_1_even_le (S m2) (rv := R_F 0 (P_tree (add_c 2 d))) hu2).
      pose proof (W_safe_app_1_even_pos m2 (rv := R_F 0 (P_tree (add_c 2 d))) hu2).
      cbn [Wd]; lia.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))).
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + intros rem hrem hcd2 hwd_le hnbr.
      destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma postD0_od_pos (m2 : nat) {d2 : Tree} (hd2 : WF_d d2) (hpos : tree_c d2 >= 1) :
  PostD0 (od 0 m2 d2).
Proof.
  assert (hu : WF_u (od 2 m2 (sub_c 1 d2))).
  { cbn; split; [lia | exact (WF_d_set_c _ hd2)]. }
  pose proof (Wd_ge_9 d2) as hwd2.
  assert (hsub_le : Wd (sub_c 1 d2) <= Wd d2).
  { destruct d2; pose_tree_bounds; crush_arith. }
  assert (hw_rv : W_rv (R_D (P_tree (od 2 m2 (sub_c 1 d2)))) <= Wd (od 0 m2 d2) + 4) by crush_arith.
  assert (hws_rv : W_safe (R_D (P_tree (od 2 m2 (sub_c 1 d2)))) =
                   W_rv (R_D (P_tree (od 2 m2 (sub_c 1 d2))))) by reflexivity.
  exists (R_D (P_tree (od 2 m2 (sub_c 1 d2)))).
  refine (conj (sweep_d0_od_pos m2 hpos) (conj hu (conj _ (conj _ (conj _ _))))).
  - split; discriminate.
  - intro; split; lia.
  - intros [| m].
    + cbn [app_1_even]; split; lia.
    + pose proof (W_rv_app_1_even_le (S m) (rv := R_D (P_tree (od 2 m2 (sub_c 1 d2)))) hu).
      pose proof (W_safe_app_1_even_pos m (rv := R_D (P_tree (od 2 m2 (sub_c 1 d2)))) hu).
      split; lia.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))).
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + intros rem hrem _ hwd_le _.
      assert (hlin : Wd (od cd m2 d2) = 2 * cd + Wd (od 0 m2 d2)) by (cbn [Wd]; lia).
      cbn [set_c stopOnePosBonus] in hwd_le.
      apply (not_badRV_of_W_safe_le rem (m + 2 * cd) (rv := R_D (P_tree (od 2 m2 (sub_c 1 d2)))) hu);
        [intro; discriminate | exact hrem | lia].
Qed.

(* ========================================================================== *)
(* 11. od Prefix Combinators and Master Mutual Induction                      *)
(* ========================================================================== *)

Lemma sweep_od_partial (k m : nat) {d : Tree} (hd : WF_d d) (hk : k + 1 <= tree_c d) :
  SweepRV ([S0; S1] ^^ k *> ([S1; S1] ^^ m *> (S1 >> S0 >> evalT d)))
          (R_A (m + 2 * k + 1) (P_od (sub_c (k + 1) d))).
Proof.
  induction k as [| k ih].
  - pose proof (sweep_P_od_pos (d := d) ltac:(lia)) as h0.
    assert (hwf0 : WF_rv (R_F 1 (P_od (sub_c 1 d)))) by exact (WF_d_set_c _ hd).
    pose proof (sweepRV_app_1_odd m hwf0 h0) as h1.
    cbn [lpow app Str_app app_1_odd evalP] in *.
    replace (m + 2 * 0 + 1) with (m + 1) by lia.
    replace (0 + 1) with 1 by lia.
    exact h1.
  - pose proof (ih ltac:(lia)) as hprev.
    assert (hpos : tree_c (sub_c (k + 1) d) >= 1).
    { unfold sub_c; rewrite tree_c_set_c; lia. }
    pose proof (sweep_P_od_pos (d := sub_c (k + 1) d) hpos) as h0.
    assert (hwf0 : WF_rv (R_F 1 (P_od (sub_c 1 (sub_c (k + 1) d))))).
    { exact (WF_d_set_c _ (WF_d_set_c _ hd)). }
    pose proof (sweepRV_01_RA (m + 2 * k + 1) hwf0 hprev h0) as hstep.
    assert (hsub : sub_c 1 (sub_c (k + 1) d) = sub_c (S k + 1) d).
    { destruct d; unfold sub_c, set_c, tree_c; f_equal; lia. }
    rewrite hsub in hstep.
    cbn [lpow app Str_app app_1_odd bump_ra] in *.
    replace (m + 2 * S k + 1) with (S (m + 2 * k + 1 + 1)) by lia.
    exact hstep.
Qed.

Lemma sweep_od_prefix (m : nat) {d : Tree} {rv0 : RVal}
    (hd : WF_d d) (hwf0 : WF_rv rv0)
    (h0 : SweepRV (S0 >> evalT (set_c 0 d)) rv0) :
  SweepRV ([S0; S1] ^^ tree_c d *> ([S1; S1] ^^ m *> (S1 >> S0 >> evalT d)))
          (app_1_odd (m + 2 * tree_c d) rv0).
Proof.
  destruct (tree_c d) as [| k] eqn:hcd.
  - assert (hd0 : set_c 0 d = d).
    { destruct d; unfold set_c, tree_c in *; f_equal; lia. }
    rewrite hd0 in h0.
    pose proof (sweepRV_app_1_odd m hwf0 h0) as h1.
    cbn [lpow app Str_app] in *.
    replace (m + 2 * 0) with m by lia.
    exact h1.
  - pose proof (sweep_od_partial k m hd ltac:(lia)) as hpart.
    assert (hsub0 : sub_c (k + 1) d = set_c 0 d).
    { destruct d; unfold sub_c, set_c, tree_c in *; f_equal; lia. }
    rewrite hsub0 in hpart.
    pose proof (sweepRV_01_RA (m + 2 * k + 1) hwf0 hpart h0) as hstep.
    rewrite bump_ra_app_1_odd in hstep.
    replace (m + 2 * S k) with (S (m + 2 * k + 1)) by lia.
    cbn [lpow app Str_app].
    exact hstep.
Qed.

Lemma odd_S_of_app_1_odd_pos (M m : nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
  S_rv (app_1_odd M (app_1_odd (S m) rv0)) <=
    Nat.max 24 (evenCeil (W_rv (app_1_odd (S m) rv0) + 7)).
Proof.
  destruct rv0 as [[u | d] | [| m0] [u | d] | m0 [u | d]];
    try destruct u; try destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma app_1_odd_pos_ne_RF0 (m : nat) (rv0 : RVal) (p : Payload) :
  app_1_odd (S m) rv0 <> R_F 0 p.
Proof.
  destruct rv0; cbn [app_1_odd]; discriminate.
Qed.

Lemma postRV_of_RA_direct (m : nat) {p : Payload} {rv0 : RVal}
    (hwf0 : WF_rv rv0)
    (hsw0 : SweepRV (evalP p) rv0)
    (hw_b : W_rv (app_1_odd (S m) rv0) <= W_rv (R_A m p) + 2)
    (hws_b : W_safe (app_1_odd (S m) rv0) <= W_safe (R_A m p) + 2)
    (hs_b : S_rv (app_1_odd (S m) rv0) <= S_rv (R_A m p) - 2)
    (hbad_b : forall rem, rem >= 1 ->
      S_rv (R_A m p) <= 20 + 2 * S rem ->
      ~ BadRV (S rem) (R_A m p) ->
      ~ BadRV rem (app_1_odd (S m) rv0)) :
  PostRV (R_A m p) (app_1_odd (S m) rv0).
Proof.
  assert (h1 : forall r, SweepRV r (R_A m p) -> SweepRV (S0 >> S1 >> r) (app_1_odd (S m) rv0)).
  { intros r hr. rewrite <- bump_ra_app_1_odd. exact (sweepRV_01_RA m hwf0 hr hsw0). }
  refine (conj h1 (conj (WF_rv_app_1_odd (S m) hwf0)
    (conj (notBadRD_app_1_odd (S m) rv0)
      (conj (app_1_odd_pos_ne_RF0 m rv0)
        (conj hw_b (conj hws_b (conj hs_b (conj _ (conj _ _))))))))).
  - intros [| r] hs hnb.
    + destruct rv0; cbn [app_1_odd BadRV Nat.eqb]; tauto.
    + exact (hbad_b (S r) ltac:(lia) hs hnb).
  - intro. apply goodRV_of_odd; discriminate.
  - intros _ M.
    pose proof (odd_of_app_1_odd_pos M m hwf0) as how.
    pose proof (odd_wsafe_of_app_1_odd_pos M m hwf0) as hows.
    pose proof (odd_S_of_app_1_odd_pos M m hwf0) as hos.
    pose proof (evenCeil_mono (x := W_rv (app_1_odd (S m) rv0) + 7)
                              (y := W_rv (R_A m p) + 9) ltac:(lia)) as hmon.
    split; [lia | split; [lia | lia]].
Qed.

Lemma postRV_of_RA_good (m : nat) {p : Payload} {rv0 : RVal}
    (hwf0 : WF_rv rv0)
    (hsw0 : SweepRV (evalP p) rv0)
    (hnb0 : m = 0 -> NotBadRD rv0)
    (hw2 : W_rv (app_1_odd m rv0) <= W_rv (R_A m p))
    (hs2 : S_rv (app_1_odd m rv0) <= S_rv (R_A m p) - 2)
    (hbad : forall rem, rem >= 1 ->
      S_rv (R_A m p) <= 20 + 2 * S rem ->
      ~ BadRV rem (app_1_odd (S m) rv0)) :
  PostRV (R_A m p) (bump_ra (app_1_odd m rv0)).
Proof.
  pose proof (WF_rv_app_1_odd m hwf0) as hwf2.
  pose proof (app_1_odd_ne_RD m rv0) as hnd2.
  pose proof (notBad_of_odd m hnb0) as hnb2.
  destruct (bump_ra_bounds hwf2 hnd2 hnb2) as [hnb_b [hw_b [hs_b hodd_b]]].
  pose proof (W_safe_bump_ra_odd m hwf0 hnb0) as hws_b.
  pose proof (W_safe_ge_W_rv (rv := R_A m p)) as hws_ge.
  refine (conj (fun r h1 => sweepRV_01_RA m hwf0 h1 hsw0)
    (conj (WF_rv_bump_ra hwf2 hnd2)
      (conj hnb_b (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))));
    try lia.
  - intro p'. rewrite bump_ra_app_1_odd. exact (app_1_odd_pos_ne_RF0 m rv0 p').
  - intros [| r] hs _.
    + rewrite bump_ra_app_1_odd. destruct rv0; cbn [app_1_odd BadRV Nat.eqb]; tauto.
    + rewrite bump_ra_app_1_odd. exact (hbad (S r) ltac:(lia) hs).
  - intro. rewrite bump_ra_app_1_odd. apply goodRV_of_odd; discriminate.
  - intros _ M.
    destruct (hodd_b M) as [how hos].
    pose proof (odd_wsafe_of_app_1_odd_pos M m hwf0) as h1.
    rewrite bump_ra_app_1_odd in how, hos, hw_b |- *.
    pose proof (evenCeil_mono (x := W_rv (app_1_odd m rv0) + 9)
                              (y := W_rv (R_A m p) + 9) ltac:(lia)) as hmon.
    split; [lia | split; [lia | lia]].
Qed.

Lemma postD0_od_0_endStop0 : PostD0 (od 0 0 (endStop 0)).
Proof.
  pose proof sweep_d0_endStop as h0.
  assert (hwf_ez2 : WF_u (endZero 2)) by (cbn; lia).
  pose proof (sweepRV_01_RF0 hwf_ez2 h0) as h1.
  assert (hev : S0 >> evalT (od 0 0 (endStop 0)) = S0 >> S1 >> (S0 >> evalT (endStop 0))).
  { rewrite evalT_od. cbn [lpow app Str_app]. reflexivity. }
  change (mk_stop 1 (sub_c 1 (endZero 2))) with (stop 1 (endZero 1)) in h1.
  rewrite <- hev in h1.
  assert (hu_st : WF_rv (R_D (P_tree (stop 1 (endZero 1))))).
  { cbn; repeat split; try lia; discriminate. }
  exists (R_D (P_tree (stop 1 (endZero 1)))).
  refine (conj h1 (conj hu_st (conj _ (conj _ (conj _ _))))).
  - split; discriminate.
  - intro; crush_arith.
  - intros [| m2]; split; crush_arith.
  - intros cd m; cbn zeta.
    refine (conj _ (conj _ (conj _ _))).
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + destruct (m + 2 * cd) as [| M] eqn:hM; crush_arith.
    + intros rem hrem _ hwd_le _.
      apply (not_badRV_of_W_safe_le rem (m + 2 * cd) hu_st);
        [intro; discriminate | exact hrem | crush_arith].
Qed.

Lemma postRV_RA_leaves (m : nat) (w : Tree) (hw : WF_u w) (hleaf : isLeaf w = true) :
  exists rvn, PostRV (R_A m (P_tree w)) rvn.
Proof.
  destruct w as [c | c | c | c | c | c d | c m2 d | c m2 u];
    try discriminate hleaf; cbn [WF_u] in hw.
  - eexists. refine (postRV_of_RA_direct m (p := P_tree (endZero c)) _ (sweep_u_endZero c hw) _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_tree (endStop c)) _ (sweep_u_endStop c hw) _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_tree (endOne c)) _ (sweep_u_endOne c hw) _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_tree (oneEnd c)) _ (sweep_u_oneEnd c hw) _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_tree (stopOne c)) _ (sweep_u_stopOne c hw) _ _ _ _);
      [cbn; split; [lia | exact I] | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
Qed.

Lemma postRV_RA_od_pos (m : nat) {d : Tree} (hd : WF_d d) (hpos : tree_c d >= 1) :
  exists rvn, PostRV (R_A m (P_od d)) rvn.
Proof.
  eexists.
  refine (postRV_of_RA_direct m (p := P_od d) (rv0 := R_F 1 (P_od (sub_c 1 d)))
            (WF_d_set_c _ hd) (sweep_P_od_pos hpos) _ _ _ _).
  - destruct d; pose_tree_bounds; crush_arith.
  - destruct d; pose_tree_bounds; crush_arith.
  - pose proof (Wd_ge_9 (set_c 0 d)).
    destruct d; pose_tree_bounds; crush_arith.
  - intros rem hrem hs hnb.
    destruct d; pose_tree_bounds; crush_arith.
Qed.

Lemma postRV_RA_od_base0 (m : nat) (d : Tree) (hd : WF_d d) (hc0 : tree_c d = 0)
    (hbase : match d with od _ _ _ | sh _ _ _ => False | _ => True end) :
  exists rvn, PostRV (R_A m (P_od d)) rvn.
Proof.
  destruct d as [c | c | c | c | c | c d2 | c m2 d2 | c m2 u2];
    try destruct hbase; cbn [tree_c] in hc0; subst c.
  - eexists. refine (postRV_of_RA_direct m (p := P_od (endZero 0)) _ sweep_d0_endZero _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem _ _; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_od (endStop 0)) _ sweep_d0_endStop _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem _ _; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_od (endOne 0)) _ sweep_d0_endOne _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_od (oneEnd 0)) _ sweep_d0_oneEnd _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - eexists. refine (postRV_of_RA_direct m (p := P_od (stopOne 0)) _ sweep_d0_stopOne _ _ _ _);
      [cbn; lia | crush_arith | crush_arith | crush_arith | intros rem hrem hs hnb; crush_arith].
  - destruct hd as [hd0 [hd1 hd2]].
    assert (hu2 : WF_u (add_c 2 d2)).
    { destruct d2; unfold add_c, set_c, tree_c; cbn in *; intuition lia. }
    pose proof (Wd_ge_9 d2) as h9.
    eexists.
    refine (postRV_of_RA_direct m (p := P_od (stop 0 d2)) (rv0 := R_F 0 (P_tree (add_c 2 d2)))
              hu2 (sweep_d0_stop_any d2) _ _ _ _).
    + destruct d2; pose_tree_bounds; crush_arith.
    + destruct d2; pose_tree_bounds; crush_arith.
    + destruct d2; pose_tree_bounds; crush_arith.
    + intros rem hrem hs hnb.
      destruct d2; pose_tree_bounds; crush_arith.
Qed.

Lemma postU_od_lt_cd (c m : nat) {d : Tree}
    (hc : c >= 2) (hd : WF_d d) (hlt : c + 1 <= tree_c d) :
  PostU (od c m d).
Proof.
  pose proof (sweep_od_partial c m hd hlt) as hpart.
  rewrite <- evalT_od in hpart.
  assert (hwf_rv : WF_rv (R_A (m + 2 * c + 1) (P_od (sub_c (c + 1) d))))
    by exact (WF_d_set_c _ hd).
  pose proof (Wd_ge_9 d) as h9.
  assert (hws_le : W_safe (R_A (m + 2 * c + 1) (P_od (sub_c (c + 1) d))) <= W0 (od c m d) + 2).
  { destruct d; pose_tree_bounds; crush_arith. }
  exists (R_A (m + 2 * c + 1) (P_od (sub_c (c + 1) d))).
  refine (conj hpart (conj hwf_rv (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - intro; split; discriminate.
  - intro; discriminate.
  - destruct d; pose_tree_bounds; crush_arith.
  - cbn [isLeaf]; exact hws_le.
  - intros M _.
    pose proof (Wd_ge_9 (sub_c (c + 1) d)) as hsub9.
    repeat split; destruct d; pose_tree_bounds; crush_arith.
  - intros c' M hc' _ hw0 _.
    cbn [isLeaf] in hc'.
    apply (not_badRV_of_W_safe_le c' M hwf_rv);
      [intro; discriminate | exact hc' | lia].
  - intros [[_ [_ hrc]] _]. exfalso.
    destruct (Wd_ge_2c_9 d) as [-> | hge]; [cbn [tree_c] in hlt; lia |].
    assert (hgt : Wd d >= 2 * tree_c d + 10).
    { destruct d; pose_tree_bounds; crush_arith. }
    crush_arith.
Qed.

Lemma postRV_step_nonRA {rv : RVal} (hwf : WF_rv rv)
    (hnotRA : forall m p, rv <> R_A m p) :
  exists rvn, PostRV rv rvn.
Proof.
  destruct rv as [[t | d] | [| m] [u | d] | m p].
  - pose proof (tree_c_pos_of_WF_u hwf) as hc.
    exists (R_D (P_tree (add_c 1 t))).
    refine (conj (fun r h => sweepRV_01_RD hwf h)
      (conj (WF_u_add_c 1 hwf)
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    + split; destruct t; crush_arith.
    + intro; discriminate.
    + cbn [W_rv]; rewrite (W0_lin_add_c_one hwf); lia.
    + destruct t; pose_tree_bounds; crush_arith.
    + cbn [S_rv]; rewrite (S_tree_add_c_one hwf); lia.
    + intros [| r] _ hbad.
      * exact hbad.
      * assert (hadd : add_c (S r) (add_c 1 t) = add_c (S (S r)) t).
        { destruct t; unfold add_c, set_c, tree_c; f_equal; lia. }
        cbn [BadRV Nat.eqb] in *; rewrite hadd; exact hbad.
    + intro hg; destruct t; crush_arith.
    + intros hg [| M]; repeat split; destruct t; pose_tree_bounds; crush_arith.
  - destruct hwf.
  - pose proof (tree_c_pos_of_WF_u hwf) as hc.
    assert (hmk_wf : WF_u (mk_stop 1 (sub_c 1 u)))
      by exact (WF_u_mk_stop 1 ltac:(lia) (WF_d_set_c _ (WF_d_of_WF_u hwf))).
    exists (R_D (P_tree (mk_stop 1 (sub_c 1 u)))).
    refine (conj (fun r h => sweepRV_01_RF0 hwf h)
      (conj hmk_wf (conj _ (conj _ (conj (W_rv_RF0_spec hwf)
        (conj _ (conj _ (conj _ (conj _ _))))))))).
    + crush_arith.
    + intro; discriminate.
    + pose proof (Wd_sub_c_one_le hwf); destruct u; pose_tree_bounds; crush_arith.
    + cbn [S_rv]; lia.
    + intros [| r] _ hbad.
      * exact hbad.
      * assert (hadd : add_c (S r) (mk_stop 1 (sub_c 1 u)) = mk_stop (S (S r)) (sub_c 1 u)).
        { unfold mk_stop.
          destruct (tree_eqb_spec (sub_c 1 u) (endZero 0)); [crush_arith |].
          destruct (tree_eqb_spec (sub_c 1 u) (endOne 1)); crush_arith. }
        cbn [BadRV Nat.eqb] in *; rewrite hadd; exact hbad.
    + intro hg.
      destruct u as [[| [| c]] | c | c | c | c | c d | c m2 d | c m2 u2]; crush_arith.
    + intros hg [| M]; pose proof (Wd_sub_c_one_le hwf);
        repeat split;
        destruct u as [[| [| c]] | c | c | c | c | c d | c m2 d | c m2 u2];
        pose_tree_bounds; crush_arith.
  - destruct hwf.
  - exists (R_D (P_tree (mk_sh 2 m u))).
    refine (conj (fun r h => sweepRV_01_RF_tree m h)
      (conj (WF_u_mk_sh 2 m ltac:(lia) hwf)
        (conj _ (conj _ (conj (W_rv_RF_pos_tree_spec m hwf)
          (conj _ (conj _ (conj _ (conj _ _))))))))).
    + crush_arith.
    + intro; discriminate.
    + destruct u; pose_tree_bounds; crush_arith.
    + cbn [S_rv]; lia.
    + intros [| r] _ hbad.
      * exact hbad.
      * assert (hadd : add_c (S r) (mk_sh 2 m u) = mk_sh (S (S r) + 1) m u).
        { unfold mk_sh, add_c, set_c, tree_c.
          destruct (m =? 0), (tree_eqb u (endStop 1)); cbn; f_equal; lia. }
        cbn [BadRV Nat.eqb] in *; rewrite hadd; exact hbad.
    + intro; crush_arith.
    + intros _ [| M]; repeat split; destruct u; pose_tree_bounds; crush_arith.
  - exists (R_D (P_tree (od 2 m d))).
    refine (conj (fun r h => sweepRV_01_RF_od m h)
      (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    + cbn; split; [lia | exact hwf].
    + split; discriminate.
    + intro; discriminate.
    + destruct d; pose_tree_bounds; crush_arith.
    + destruct d; pose_tree_bounds; crush_arith.
    + cbn [S_rv]; lia.
    + intros [| r] _ hbad.
      * exact hbad.
      * cbn [BadRV Nat.eqb add_c set_c tree_c] in *.
        replace (2 + S r) with (S (S r) + 1) by lia.
        exact hbad.
    + intro; exact I.
    + intros _ [| M]; repeat split; destruct d; pose_tree_bounds; crush_arith.
  - exfalso; exact (hnotRA m p eq_refl).
Qed.

Lemma Wd_ge_2c_10 {d : Tree} (hc : tree_c d >= 2) : Wd d >= 2 * tree_c d + 10.
Proof. destruct d; pose_tree_bounds; crush_arith. Qed.

Lemma M_d0_set_c_0_lt_od (c m : nat) (d : Tree) (hc : c >= 2) :
  M_d0 (set_c 0 d) < M_u (od c m d).
Proof. destruct d; pose_tree_bounds; crush_arith. Qed.

Lemma M_u_lt_sh (c m : nat) (u2 : Tree) :
  M_u u2 < M_u (sh c m u2).
Proof. pose proof (W0_ge_11 u2); destruct u2; crush_arith. Qed.

Lemma M_d0_lt_od0 (m2 : nat) (d2 : Tree) :
  M_d0 d2 < M_d0 (od 0 m2 d2).
Proof. destruct d2; pose_tree_bounds; crush_arith. Qed.

Lemma M_u_lt_sh0 (m2 : nat) (u2 : Tree) :
  M_u u2 < M_d0 (sh 0 m2 u2).
Proof. destruct u2; pose_tree_bounds; crush_arith. Qed.

Definition MasterStmt (n : nat) : Prop :=
  (forall u, WF_u u -> M_u u = n -> PostU u) /\
  (forall d0, WF_d d0 -> tree_c d0 = 0 -> M_d0 d0 = n -> PostD0 d0) /\
  (forall rv, WF_rv rv -> M_rv rv = n -> exists rvn, PostRV rv rvn).

Lemma master_branch_U (n : nat) (ih : forall m, m < n -> MasterStmt m) :
  forall u, WF_u u -> M_u u = n -> PostU u.
Proof.
  intros u hu hmu.
  destruct u as [c | c | c | c | c | c d | c m d | c m u2].
  - exact (postU_endZero c hu).
  - exact (postU_endStop c hu).
  - exact (postU_endOne c hu).
  - exact (postU_oneEnd c hu).
  - exact (postU_stopOne c hu).
  - exact (postU_stop c d hu).
  - (* od c m d *)
    destruct hu as [hc hd].
    destruct (Nat.leb_spec0 (c + 1) (tree_c d)) as [hlt_c | hge_c].
    + exact (postU_od_lt_cd c m hc hd hlt_c).
    + assert (hmu_eq : W0 (od c m d) + 3 = n) by (cbn [M_u] in hmu; exact hmu).
      set (d0 := set_c 0 d).
      assert (hd0_wf : WF_d d0) by exact (WF_d_set_c 0 hd).
      assert (hd0_c : tree_c d0 = 0) by exact (tree_c_set_c 0 d).
      assert (hlt_d0 : M_d0 d0 < n).
      { subst n d0; exact (M_d0_set_c_0_lt_od c m d hc). }
      destruct (ih (M_d0 d0) hlt_d0) as [_ [ih_d0 _]].
      destruct (ih_d0 d0 hd0_wf hd0_c eq_refl) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ hodd0]]]]]].
      pose proof (sweep_od_prefix m hd hwf0 hsw0) as hpref.
      assert (hdf : set_c (tree_c d) d0 = d).
      { subst d0; destruct d; reflexivity. }
      destruct (hodd0 (tree_c d) m) as [how_init [hows_init [hos_init hbad_init0]]].
      rewrite hdf in how_init, hows_init, hos_init, hbad_init0.
      assert (hgood_init : GoodRV (app_1_odd (m + 2 * tree_c d) rv0)).
      { apply goodRV_of_odd. intro. exact (proj1 hnb0). }
      pose proof (WF_rv_app_1_odd (m + 2 * tree_c d) hwf0) as hwf_init.
      destruct (Nat.eqb_spec c (tree_c d)) as [heq_c | hne_c].
      * subst c.
        rewrite <- evalT_od in hpref.
        assert (hm_pos : m + 2 * tree_c d = S (m + 2 * tree_c d - 1)) by lia.
        assert (hnf_eq : forall p', app_1_odd (m + 2 * tree_c d) rv0 <> R_F 0 p').
        { intro p'; rewrite hm_pos; apply app_1_odd_pos_ne_RF0. }
        assert (hws_eq : W_safe (app_1_odd (m + 2 * tree_c d) rv0) <= W0 (od (tree_c d) m d) + 2).
        { cbn [W0]; lia. }
        exists (app_1_odd (m + 2 * tree_c d) rv0).
        refine (conj hpref (conj hwf_init (conj (fun _ => notBadRD_app_1_odd _ _)
          (conj hnf_eq (conj _ (conj _ (conj _ (conj _ _)))))))).
        -- cbn [W0]; lia.
        -- cbn [isLeaf]; exact hws_eq.
        -- intros M _.
           pose proof (odd_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0) as how_f.
           pose proof (odd_wsafe_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0) as hows_f.
           pose proof (odd_S_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0) as hos_f.
           rewrite <- hm_pos in how_f, hows_f, hos_f.
           pose proof (evenCeil_mono
             (x := W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 7)
             (y := W0 (od (tree_c d) m d) + 9) ltac:(cbn [W0]; lia)) as hmon.
           assert (hw0_eq : W0 (od (tree_c d) m d) = 2 * tree_c d + 2 * m + 4 + Wd d)
             by reflexivity.
           repeat split; lia.
        -- intros c' M hc' _ hw0 _.
           cbn [isLeaf] in hc'.
           exact (not_badRV_of_W_safe_le c' M hwf_init hnf_eq hc' ltac:(lia)).
        -- intros [[_ [_ hrc]] _].
           pose proof (Wd_ge_2c_10 hc). lia.
      * assert (hgt : c > tree_c d) by lia.
        assert (ih_step : forall rv', WF_rv rv' -> W_rv rv' <= W0 (od c m d) ->
                            exists rvn, PostRV rv' rvn).
        { intros rv' hwf' hw'.
          assert (hlt_rv : M_rv rv' < n) by (unfold M_rv; lia).
          destruct (ih (M_rv rv') hlt_rv) as [_ [_ ih_rv]].
          exact (ih_rv rv' hwf' eq_refl). }
        set (k := c - tree_c d - 1).
        assert (hk_eq : S k = c - tree_c d) by lia.
        assert (hbudget : W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 2 * k <= W0 (od c m d)).
        { cbn [W0]; lia. }
        destruct (iter_app_01_pos k (W0 (od c m d)) ih_step _ _ hpref hwf_init hgood_init hbudget)
          as [rvf [hswf [hwff [hnbf [hnff [_ [hwf_w [hwf_ws [hwf_s [hbad_f hodd_f]]]]]]]]]].
        rewrite hk_eq in hswf, hwf_w, hwf_ws, hwf_s, hbad_f.
        assert (heval_eq :
          [S0; S1] ^^ (c - tree_c d) *>
            ([S0; S1] ^^ tree_c d *> ([S1; S1] ^^ m *> (S1 >> S0 >> evalT d))) =
          evalT (od c m d)).
        { rewrite <- Str_app_assoc, <- lpow_add.
          replace (c - tree_c d + tree_c d) with c by lia.
          reflexivity. }
        rewrite heval_eq in hswf.
        assert (hws_od : W_safe rvf <= W0 (od c m d) + 2) by (cbn [W0] in *; lia).
        exists rvf.
        refine (conj hswf (conj hwff (conj (fun _ => hnbf) (conj hnff
          (conj _ (conj _ (conj _ (conj _ _)))))))).
        -- cbn [W0] in *; lia.
        -- cbn [isLeaf]; exact hws_od.
        -- intros M _.
           destruct (hodd_f M) as [how_f [hows_f hos_f]].
           pose proof (evenCeil_mono
             (x := W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 2 * k + 9)
             (y := W0 (od c m d) + 9) ltac:(lia)) as hmon.
           repeat split; lia.
        -- intros c' M hc' _ hw0 _.
           cbn [isLeaf] in hc'.
           exact (not_badRV_of_W_safe_le c' M hwff hnff hc' ltac:(lia)).
        -- intros [[_ [hc_ez hod_ge]] hnbr].
           assert (hec_le : evenCeil (Wd d + 11 + stopOnePosBonus d - 2 * tree_c d) <=
                            2 * (c - tree_c d) + 20) by (unfold evenCeil; lia).
           assert (hcsum : tree_c d + (c - tree_c d) = c) by lia.
           assert (hbad_st : ~ BadRV (c - tree_c d) (app_1_odd (m + 2 * tree_c d) rv0)).
           { apply hbad_init0; try lia. rewrite hcsum; exact hnbr. }
           assert (hs_init_le : S_rv (app_1_odd (m + 2 * tree_c d) rv0) <= 20 + 2 * (c - tree_c d)).
           { destruct (tree_eqb_spec d (endZero 1)) as [-> | _]; cbn [tree_c] in *; lia. }
           assert (hs_le : S_rv rvf <= 20) by lia.
           exact (S_rv_RD_of_le_20 hwff hs_le (hbad_f hs_init_le hbad_st)).
  - (* sh c m u2 *)
    destruct hu as [hc [hnot1 hu2]].
    assert (hmu_eq : W0 (sh c m u2) + 3 = n) by (cbn [M_u] in hmu; exact hmu).
    assert (hlt_u2 : M_u u2 < n) by (subst n; exact (M_u_lt_sh c m u2)).
    destruct (ih (M_u u2) hlt_u2) as [ih_u _].
    destruct (ih_u u2 hu2 eq_refl) as
      [rv2 [hsw2 [hwf2 [hnb2 [_ [hw2 [_ [hodd2 [hbad2 _]]]]]]]]].
    pose proof (sweepRV_app_1_odd m hwf2 hsw2) as hsw_init.
    pose proof (WF_rv_app_1_odd m hwf2) as hwf_init.
    assert (hgood_init : GoodRV (app_1_odd m rv2)).
    { apply goodRV_of_odd. intro hm0.
      exact (proj1 (hnb2 (fun he => hnot1 (conj hm0 he)))). }
    destruct (hodd2 m hnot1) as [how_init [hows_init hos_init]].
    assert (ih_step : forall rv', WF_rv rv' -> W_rv rv' <= W0 (sh c m u2) ->
                        exists rvn, PostRV rv' rvn).
    { intros rv' hwf' hw'.
      assert (hlt_rv : M_rv rv' < n) by (unfold M_rv; lia).
      destruct (ih (M_rv rv') hlt_rv) as [_ [_ ih_rv]].
      exact (ih_rv rv' hwf' eq_refl). }
    assert (hbudget : W_rv (app_1_odd m rv2) + 2 * (c - 1) <= W0 (sh c m u2))
      by (cbn [W0]; lia).
    destruct (iter_app_01_pos (c - 1) (W0 (sh c m u2)) ih_step _ _
                hsw_init hwf_init hgood_init hbudget)
      as [rvf [hswf [hwff [hnbf [hnff [_ [hwf_w [hwf_ws [hwf_s [hbad_f hodd_f]]]]]]]]]].
    assert (hc_eq : S (c - 1) = c) by lia.
    rewrite hc_eq in hswf, hwf_w, hwf_ws, hwf_s, hbad_f.
    assert (hws_sh : W_safe rvf <= W0 (sh c m u2) + 2) by (cbn [W0] in *; lia).
    exists rvf.
    refine (conj _ (conj hwff (conj (fun _ => hnbf) (conj hnff
      (conj _ (conj _ (conj _ (conj _ _)))))))).
    + rewrite evalT_sh; exact hswf.
    + cbn [W0] in *; lia.
    + cbn [isLeaf]; exact hws_sh.
    + intros M _.
      destruct (hodd_f M) as [how_f [hows_f hos_f]].
      pose proof (evenCeil_mono
        (x := W_rv (app_1_odd m rv2) + 2 * (c - 1) + 9)
        (y := W0 (sh c m u2) + 9) ltac:(lia)) as hmon.
      repeat split; lia.
    + intros c' M hc' _ hw0 _.
      cbn [isLeaf] in hc'.
      exact (not_badRV_of_W_safe_le c' M hwff hnff hc' ltac:(lia)).
    + intros [[_ hsh_ge] hnbr].
      assert (hec_le : evenCeil (W0 u2 + 9) <= 2 * c + 20) by (unfold evenCeil; lia).
      assert (hbad_init : ~ BadRV c (app_1_odd m rv2)).
      { apply (hbad2 c m); [destruct (isLeaf u2); lia | exact hnot1 | lia | exact hnbr]. }
      exact (S_rv_RD_of_le_20 hwff ltac:(lia) (hbad_f ltac:(lia) hbad_init)).
Qed.

Lemma master_branch_D0 (n : nat) (ih : forall m, m < n -> MasterStmt m) :
  forall d0, WF_d d0 -> tree_c d0 = 0 -> M_d0 d0 = n -> PostD0 d0.
Proof.
  intros d0 hd0 hc0 hmd0.
  destruct d0 as [c | c | c | c | c | c d2 | c m2 d2 | c m2 u2];
    cbn [tree_c] in hc0; subst c.
  - exact postD0_endZero.
  - exact postD0_endStop.
  - exact postD0_endOne.
  - exact postD0_oneEnd.
  - exact postD0_stopOne.
  - exact (postD0_stop hd0).
  - (* od 0 m2 d2 *)
    destruct (Nat.eqb_spec m2 0) as [hm20 | hm2_ne0];
      [destruct (tree_eqb_spec d2 (endStop 0)) as [hd2_es | hd2_nes] |].
    + subst m2 d2; exact postD0_od_0_endStop0.
    + destruct (Nat.leb_spec0 1 (tree_c d2)) as [hpos | hc2_0];
        [exact (postD0_od_pos m2 (d2 := d2) hd0 hpos) |].
      assert (hc2 : tree_c d2 = 0) by lia.
      assert (hmd0_eq : Wd (od 0 m2 d2) + 7 = n) by (cbn [M_d0] in hmd0; exact hmd0).
      assert (hlt_d2 : M_d0 d2 < n) by (subst n; exact (M_d0_lt_od0 m2 d2)).
      destruct (ih (M_d0 d2) hlt_d2) as [_ [ih_d2 _]].
      destruct (ih_d2 d2 hd0 hc2 eq_refl) as
        [rv2 [hsw2 [hwf2 [hnb2 [hw2_not_es [hw2_ev _]]]]]].
      pose proof (sweepRV_app_1_even m2 hwf2 hsw2) as hsw_ev.
      pose proof (WF_rv_app_1_even m2 hwf2) as hwf_ev.
      assert (hw_ev_le : W_rv (app_1_even m2 rv2) <= Wd (od 0 m2 d2) + 2).
      { pose proof (proj1 (hw2_ev m2)); cbn [Wd]; lia. }
      assert (hws_ev_le : W_safe (app_1_even m2 rv2) <= Wd (od 0 m2 d2) + 2).
      { pose proof (proj2 (hw2_ev m2)); cbn [Wd]; lia. }
      assert (hlt_ev : M_rv (app_1_even m2 rv2) < n) by (unfold M_rv; lia).
      destruct (ih (M_rv (app_1_even m2 rv2)) hlt_ev) as [_ [_ ih_rv]].
      destruct (ih_rv (app_1_even m2 rv2) hwf_ev eq_refl) as
        [rvn [hstep [hwfn [hnbn [hnfn [hwn [hwsn [_ [_ [_ hodd_n]]]]]]]]]].
      assert (hsw_fin : SweepRV (S0 >> evalT (od 0 m2 d2)) rvn).
      { pose proof (hstep _ hsw_ev) as h1.
        rewrite evalT_od; cbn [lpow app Str_app].
        rewrite (swap_1_11_pow m2 (S0 >> evalT d2)).
        exact h1. }
      pose proof (Wd_ge_9 d2) as hd9.
      exists rvn.
      refine (conj hsw_fin (conj hwfn (conj hnbn
        (conj _ (conj _ _))))).
      * intro; split; lia.
      * intros [| m].
        -- cbn [app_1_even]; split; lia.
        -- pose proof (W_rv_app_1_even_le (S m) hwfn).
           pose proof (W_safe_app_1_even_pos m hwfn).
           split; lia.
      * intros cd m; cbn zeta.
        subst m2.
        pose proof (proj1 (hw2_not_es hd2_nes)) as hw_ev0_raw.
        assert (hw_ev0 : W_rv (app_1_even 0 rv2) <= Wd (od 0 0 d2))
          by (cbn [app_1_even Wd]; lia).
        pose proof (W_rv_app_1_odd_le_4 (m + 2 * cd) hwfn) as how.
        pose proof (W_safe_app_1_odd_le_4 (m + 2 * cd) hwfn hnfn (proj2 hnbn)) as hows.
        pose proof (S_rv_app_1_odd_le (m + 2 * cd) hwfn) as hos.
        pose proof (evenCeil_mono (x := W_rv rvn + 9)
                                  (y := Wd (od 0 0 d2) + 11) ltac:(lia)) as hmon.
        assert (hge24 : evenCeil (Wd (od 0 0 d2) + 11) >= 24)
          by (unfold evenCeil; cbn [Wd]; lia).
        cbn [set_c tree_eqb stopOnePosBonus].
        replace (Wd (od cd 0 d2)) with (2 * cd + Wd (od 0 0 d2)) by (cbn [Wd]; lia).
        replace (2 * cd + Wd (od 0 0 d2) + 11 + 0 - 2 * cd) with (Wd (od 0 0 d2) + 11) by lia.
        refine (conj _ (conj _ (conj _ _))); try lia.
        intros rem hrem _ hwd_le _.
        exact (not_badRV_of_W_safe_le rem (m + 2 * cd) hwfn hnfn hrem ltac:(lia)).
    + destruct (Nat.leb_spec0 1 (tree_c d2)) as [hpos | hc2_0];
        [exact (postD0_od_pos m2 (d2 := d2) hd0 hpos) |].
      assert (hc2 : tree_c d2 = 0) by lia.
      assert (hmd0_eq : Wd (od 0 m2 d2) + 7 = n) by (cbn [M_d0] in hmd0; exact hmd0).
      assert (hlt_d2 : M_d0 d2 < n) by (subst n; exact (M_d0_lt_od0 m2 d2)).
      destruct (ih (M_d0 d2) hlt_d2) as [_ [ih_d2 _]].
      destruct (ih_d2 d2 hd0 hc2 eq_refl) as
        [rv2 [hsw2 [hwf2 [hnb2 [_ [hw2_ev _]]]]]].
      pose proof (sweepRV_app_1_even m2 hwf2 hsw2) as hsw_ev.
      pose proof (WF_rv_app_1_even m2 hwf2) as hwf_ev.
      assert (hw_ev_le : W_rv (app_1_even m2 rv2) <= Wd (od 0 m2 d2) + 2).
      { pose proof (proj1 (hw2_ev m2)); cbn [Wd]; lia. }
      assert (hws_ev_le : W_safe (app_1_even m2 rv2) <= Wd (od 0 m2 d2) + 2).
      { pose proof (proj2 (hw2_ev m2)); cbn [Wd]; lia. }
      assert (hlt_ev : M_rv (app_1_even m2 rv2) < n) by (unfold M_rv; lia).
      destruct (ih (M_rv (app_1_even m2 rv2)) hlt_ev) as [_ [_ ih_rv]].
      destruct (ih_rv (app_1_even m2 rv2) hwf_ev eq_refl) as
        [rvn [hstep [hwfn [hnbn [hnfn [hwn [hwsn [_ [_ [_ hodd_n]]]]]]]]]].
      assert (hsw_fin : SweepRV (S0 >> evalT (od 0 m2 d2)) rvn).
      { pose proof (hstep _ hsw_ev) as h1.
        rewrite evalT_od; cbn [lpow app Str_app].
        rewrite (swap_1_11_pow m2 (S0 >> evalT d2)).
        exact h1. }
      pose proof (Wd_ge_9 d2) as hd9.
      exists rvn.
      refine (conj hsw_fin (conj hwfn (conj hnbn
        (conj _ (conj _ _))))).
      * intro; split; lia.
      * intros [| m].
        -- cbn [app_1_even]; split; lia.
        -- pose proof (W_rv_app_1_even_le (S m) hwfn).
           pose proof (W_safe_app_1_even_pos m hwfn).
           split; lia.
      * intros cd m; cbn zeta.
        destruct m2 as [| m2']; [contradiction |].
        assert (hg_ev : GoodRV (app_1_even (S m2') rv2)).
        { destruct rv2; exact I. }
        destruct (hodd_n hg_ev (m + 2 * cd)) as [how [hows hos]].
        pose proof (evenCeil_mono (x := W_rv (app_1_even (S m2') rv2) + 9)
                                  (y := Wd (od 0 (S m2') d2) + 11) ltac:(lia)) as hmon.
        assert (hge24 : evenCeil (Wd (od 0 (S m2') d2) + 11) >= 24)
          by (unfold evenCeil; cbn [Wd]; lia).
        cbn [set_c tree_eqb stopOnePosBonus].
        replace (Wd (od cd (S m2') d2)) with (2 * cd + Wd (od 0 (S m2') d2)) by (cbn [Wd]; lia).
        replace (2 * cd + Wd (od 0 (S m2') d2) + 11 + 0 - 2 * cd)
          with (Wd (od 0 (S m2') d2) + 11) by lia.
        refine (conj _ (conj _ (conj _ _))); try lia.
        intros rem hrem _ hwd_le _.
        exact (not_badRV_of_W_safe_le rem (m + 2 * cd) hwfn hnfn hrem ltac:(lia)).
  - (* sh 0 m2 u2 *)
    destruct hd0 as [hnot1 hu2].
    assert (hmd0_eq : Wd (sh 0 m2 u2) + 7 = n) by (cbn [M_d0] in hmd0; exact hmd0).
    assert (hlt_u2 : M_u u2 < n) by (subst n; exact (M_u_lt_sh0 m2 u2)).
    destruct (ih (M_u u2) hlt_u2) as [ih_u2 _].
    destruct (ih_u2 u2 hu2 eq_refl) as [rv2 [hsw2 [hwf2 [hnb2 [_ [hw2 [hws2 _]]]]]]].
    pose proof (sweepRV_app_1_even m2 hwf2 hsw2) as hsw_ev.
    pose proof (WF_rv_app_1_even m2 hwf2) as hwf_ev.
    assert (hw_ev_le : W_rv (app_1_even m2 rv2) <= Wd (sh 0 m2 u2) + 2).
    { pose proof (W_rv_app_1_even_le m2 hwf2); cbn [Wd]; lia. }
    assert (hws_ev_le : W_safe (app_1_even m2 rv2) <= Wd (sh 0 m2 u2) + 2).
    { destruct m2 as [| m2'].
      - cbn [app_1_even Wd] in *; destruct (isLeaf u2); lia.
      - pose proof (W_safe_app_1_even_pos m2' hwf2); cbn [Wd]; lia. }
    assert (hlt_ev : M_rv (app_1_even m2 rv2) < n) by (unfold M_rv; lia).
    destruct (ih (M_rv (app_1_even m2 rv2)) hlt_ev) as [_ [_ ih_rv]].
    destruct (ih_rv (app_1_even m2 rv2) hwf_ev eq_refl) as
      [rvn [hstep [hwfn [hnbn [hnfn [hwn [hwsn [_ [_ [_ hodd_n]]]]]]]]]].
    assert (hsw_fin : SweepRV (S0 >> evalT (sh 0 m2 u2)) rvn).
    { pose proof (hstep _ hsw_ev) as h1.
      rewrite evalT_sh; cbn [lpow app Str_app].
      rewrite (swap_1_11_pow m2 (evalT u2)).
      exact h1. }
    pose proof (W0_ge_11 u2) as hw20.
    pose proof (tree_c_pos_of_WF_u hu2) as hcu2.
    exists rvn.
    refine (conj hsw_fin (conj hwfn (conj hnbn
      (conj _ (conj _ _))))).
    + intro; split; lia.
    + intros [| m].
      * cbn [app_1_even]; split; lia.
      * pose proof (W_rv_app_1_even_le (S m) hwfn).
        pose proof (W_safe_app_1_even_pos m hwfn).
        split; lia.
    + intros cd m; cbn zeta.
      cbn [set_c tree_eqb stopOnePosBonus].
      replace (Wd (sh cd m2 u2)) with (2 * cd + Wd (sh 0 m2 u2)) by (cbn [Wd]; lia).
      replace (2 * cd + Wd (sh 0 m2 u2) + 11 + 0 - 2 * cd)
        with (Wd (sh 0 m2 u2) + 11) by lia.
      assert (hbad_sh : forall rem, rem >= 1 -> cd + rem >= 2 ->
                2 * cd + Wd (sh 0 m2 u2) + 0 <= 2 * (cd + rem) + 9 ->
                ~ BadRoot (od (cd + rem) m (sh cd m2 u2)) ->
                ~ BadRV rem (app_1_odd (m + 2 * cd) rvn)).
      { intros rem hrem _ hwd_le _.
        exact (not_badRV_of_W_safe_le rem (m + 2 * cd) hwfn hnfn hrem ltac:(lia)). }
      destruct m2 as [| m2'].
      * assert (hw_ev0 : W_rv (app_1_even 0 rv2) <= Wd (sh 0 0 u2))
          by (cbn [app_1_even Wd]; lia).
        pose proof (W_rv_app_1_odd_le_4 (m + 2 * cd) hwfn) as how.
        pose proof (W_safe_app_1_odd_le_4 (m + 2 * cd) hwfn hnfn (proj2 hnbn)) as hows.
        pose proof (S_rv_app_1_odd_le (m + 2 * cd) hwfn) as hos.
        pose proof (evenCeil_mono (x := W_rv rvn + 9)
                                  (y := Wd (sh 0 0 u2) + 11) ltac:(lia)) as hmon.
        assert (hge24 : evenCeil (Wd (sh 0 0 u2) + 11) >= 24)
          by (unfold evenCeil; cbn [Wd]; lia).
        refine (conj _ (conj _ (conj _ hbad_sh))); lia.
      * assert (hg_ev : GoodRV (app_1_even (S m2') rv2)) by (destruct rv2; exact I).
        destruct (hodd_n hg_ev (m + 2 * cd)) as [how [hows hos]].
        pose proof (evenCeil_mono (x := W_rv (app_1_even (S m2') rv2) + 9)
                                  (y := Wd (sh 0 (S m2') u2) + 11) ltac:(lia)) as hmon.
        assert (hge24 : evenCeil (Wd (sh 0 (S m2') u2) + 11) >= 24)
          by (unfold evenCeil; cbn [Wd]; lia).
        refine (conj _ (conj _ (conj _ hbad_sh))); lia.
Qed.

Lemma master_branch_RV (n : nat) (ih : forall m, m < n -> MasterStmt m) :
  forall rv, WF_rv rv -> M_rv rv = n -> exists rvn, PostRV rv rvn.
Proof.
  intros [p | m p | m [w | d]] hwf hmrv.
  - apply postRV_step_nonRA; [exact hwf | intros; discriminate].
  - apply postRV_step_nonRA; [exact hwf | intros; discriminate].
  - (* R_A m (P_tree w) *)
    destruct w as [c | c | c | c | c | c d | c m2 d2 | c m2 u2].
    + exact (postRV_RA_leaves m (endZero c) hwf eq_refl).
    + exact (postRV_RA_leaves m (endStop c) hwf eq_refl).
    + exact (postRV_RA_leaves m (endOne c) hwf eq_refl).
    + exact (postRV_RA_leaves m (oneEnd c) hwf eq_refl).
    + exact (postRV_RA_leaves m (stopOne c) hwf eq_refl).
    + destruct (postU_stop c d hwf) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ [_ [hodd0 [hbad0 _]]]]]]]]].
      destruct (hodd0 m ltac:(intros [_ h]; discriminate h)) as [how0 [_ hos0]].
      pose proof (Wd_ge_9 d) as hw9.
      pose proof (proj1 hwf) as hwc.
      eexists.
      refine (postRV_of_RA_good m (p := P_tree (stop c d)) hwf0 hsw0
                (fun _ => hnb0 ltac:(intro; discriminate)) _ _ _).
      * cbn [W_rv W_ra_tree]; exact how0.
      * cbn [S_rv S_ra_tree W0] in *. unfold evenCeil in *; lia.
      * intros rem hrem hs.
        pose proof (evenCeil_ge (W0 (stop c d) + 9)) as hge.
        cbn [S_rv S_ra_tree] in hs.
        exact (hbad0 rem (S m) ltac:(cbn [isLeaf]; lia)
                 ltac:(intros [h _]; discriminate h) ltac:(lia) ltac:(cbn; tauto)).
    + assert (hlt : M_u (od c m2 d2) < n)
        by (subst n; unfold M_u, M_rv; cbn [W_rv W_ra_tree]; lia).
      destruct (ih (M_u (od c m2 d2)) hlt) as [ih_u _].
      destruct (ih_u (od c m2 d2) hwf eq_refl) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ [_ [hodd0 [hbad0 _]]]]]]]]].
      destruct (hodd0 m ltac:(intros [_ h]; discriminate h)) as [how0 [_ hos0]].
      pose proof (Wd_ge_9 d2) as hw9.
      pose proof (proj1 hwf) as hwc.
      eexists.
      refine (postRV_of_RA_good m (p := P_tree (od c m2 d2)) hwf0 hsw0
                (fun _ => hnb0 ltac:(intro; discriminate)) _ _ _).
      * cbn [W_rv W_ra_tree]; exact how0.
      * cbn [S_rv S_ra_tree W0] in *. unfold evenCeil in *; lia.
      * intros rem hrem hs.
        pose proof (evenCeil_ge (W0 (od c m2 d2) + 9)) as hge.
        cbn [S_rv S_ra_tree] in hs.
        exact (hbad0 rem (S m) ltac:(cbn [isLeaf]; lia)
                 ltac:(intros [h _]; discriminate h) ltac:(lia) ltac:(cbn; tauto)).
    + assert (hlt : M_u (sh c m2 u2) < n)
        by (subst n; unfold M_u, M_rv; cbn [W_rv W_ra_tree]; lia).
      destruct (ih (M_u (sh c m2 u2)) hlt) as [ih_u _].
      destruct (ih_u (sh c m2 u2) hwf eq_refl) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ [_ [hodd0 [hbad0 _]]]]]]]]].
      destruct (hodd0 m ltac:(intros [_ h]; discriminate h)) as [how0 [_ hos0]].
      pose proof (W0_ge_11 u2) as hw11.
      pose proof (proj1 hwf) as hwc.
      eexists.
      refine (postRV_of_RA_good m (p := P_tree (sh c m2 u2)) hwf0 hsw0
                (fun _ => hnb0 ltac:(intro; discriminate)) _ _ _).
      * cbn [W_rv W_ra_tree]; exact how0.
      * cbn [S_rv S_ra_tree W0] in *. unfold evenCeil in *; lia.
      * intros rem hrem hs.
        pose proof (evenCeil_ge (W0 (sh c m2 u2) + 9)) as hge.
        cbn [S_rv S_ra_tree] in hs.
        exact (hbad0 rem (S m) ltac:(cbn [isLeaf]; lia)
                 ltac:(intros [h _]; discriminate h) ltac:(lia) ltac:(cbn; tauto)).
  - (* R_A m (P_od d) *)
    destruct (Nat.leb_spec0 1 (tree_c d)) as [hpos | hc0_raw];
      [exact (postRV_RA_od_pos m (d := d) hwf hpos) |].
    assert (hc0 : tree_c d = 0) by lia.
    destruct d as [c | c | c | c | c | c d2 | cd m2 d2 | cd m2 u2].
    + exact (postRV_RA_od_base0 m (endZero c) hwf hc0 I).
    + exact (postRV_RA_od_base0 m (endStop c) hwf hc0 I).
    + exact (postRV_RA_od_base0 m (endOne c) hwf hc0 I).
    + exact (postRV_RA_od_base0 m (oneEnd c) hwf hc0 I).
    + exact (postRV_RA_od_base0 m (stopOne c) hwf hc0 I).
    + exact (postRV_RA_od_base0 m (stop c d2) hwf hc0 I).
    + cbn [tree_c] in hc0; subst cd.
      assert (hlt : M_d0 (od 0 m2 d2) < n)
        by (subst n; unfold M_d0, M_rv; cbn [W_rv W_ra_od]; lia).
      destruct (ih (M_d0 (od 0 m2 d2)) hlt) as [_ [ih_d0 _]].
      destruct (ih_d0 (od 0 m2 d2) hwf eq_refl eq_refl) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ hodd0]]]]]].
      destruct (hodd0 0 m) as [how0 [_ [hos0 _]]].
      cbn [set_c tree_eqb stopOnePosBonus] in how0, hos0.
      replace (m + 2 * 0) with m in how0, hos0 by lia.
      pose proof (Wd_ge_9 d2) as hd9.
      eexists.
      refine (postRV_of_RA_good m (p := P_od (od 0 m2 d2)) hwf0 hsw0 (fun _ => hnb0) _ _ _).
      * cbn [W_rv W_ra_od]; lia.
      * cbn [S_rv S_ra_od tree_c set_c Wd] in *.
        unfold evenCeil in *; lia.
      * intros rem hrem hs.
        destruct (hodd0 0 (S m)) as [_ [_ [_ hbad0]]].
        pose proof (evenCeil_ge (Wd (od 0 m2 d2) + 11)) as hge.
        cbn [S_rv S_ra_od tree_c set_c] in hs.
        replace (S m + 2 * 0) with (S m) in hbad0 by lia.
        exact (hbad0 rem hrem ltac:(lia)
                 ltac:(cbn [set_c stopOnePosBonus]; lia) ltac:(cbn; tauto)).
    + cbn [tree_c] in hc0; subst cd.
      assert (hlt : M_d0 (sh 0 m2 u2) < n)
        by (subst n; unfold M_d0, M_rv; cbn [W_rv W_ra_od]; lia).
      destruct (ih (M_d0 (sh 0 m2 u2)) hlt) as [_ [ih_d0 _]].
      destruct (ih_d0 (sh 0 m2 u2) hwf eq_refl eq_refl) as
        [rv0 [hsw0 [hwf0 [hnb0 [_ [_ hodd0]]]]]].
      destruct (hodd0 0 m) as [how0 [_ [hos0 _]]].
      cbn [set_c tree_eqb stopOnePosBonus] in how0, hos0.
      replace (m + 2 * 0) with m in how0, hos0 by lia.
      pose proof (W0_ge_11 u2) as hu11.
      pose proof (tree_c_pos_of_WF_u (proj2 hwf)) as hcu2.
      eexists.
      refine (postRV_of_RA_good m (p := P_od (sh 0 m2 u2)) hwf0 hsw0 (fun _ => hnb0) _ _ _).
      * cbn [W_rv W_ra_od]; lia.
      * cbn [S_rv S_ra_od tree_c set_c Wd] in *.
        unfold evenCeil in *; lia.
      * intros rem hrem hs.
        destruct (hodd0 0 (S m)) as [_ [_ [_ hbad0]]].
        pose proof (evenCeil_ge (Wd (sh 0 m2 u2) + 11)) as hge.
        cbn [S_rv S_ra_od tree_c set_c] in hs.
        replace (S m + 2 * 0) with (S m) in hbad0 by lia.
        exact (hbad0 rem hrem ltac:(lia)
                 ltac:(cbn [set_c stopOnePosBonus]; lia) ltac:(cbn; tauto)).
Qed.

Theorem master_ind (n : nat) : MasterStmt n.
Proof.
  induction n as [n ih] using strong_induction.
  exact (conj (master_branch_U n ih)
        (conj (master_branch_D0 n ih)
              (master_branch_RV n ih))).
Qed.

(* ========================================================================== *)
(* 12. Top-Level Era Invariant and Non-Halting Theorem                        *)
(* ========================================================================== *)

Definition EraInv (cfg : Q * tape) : Prop :=
  exists t : Tree, WF_r t /\ cfg = eraCfg (evalT t).

Lemma era_inv_zero : EraInv (eraCfg ([S0; S1] *> 0inf)).
Proof.
  exists (endZero 1).
  split.
  - unfold WF_r, WF_r_core; cbn; repeat split; try lia; tauto.
  - unfold evalT, tree_c, evalCore.
    rewrite lpow_1. reflexivity.
Qed.

Lemma era_inv_step : forall c, EraInv c -> exists c', EraInv c' /\ c -->+ c'.
Proof.
  intros _ [t [hrt ->]].
  destruct (master_ind (M_u t)) as [hm_u _].
  destruct (hm_u t (proj1 (proj1 hrt)) eq_refl) as
    [rv [hsw [_ [_ [_ [_ [_ [_ [_ hr_step]]]]]]]]].
  destruct (hr_step hrt) as [tn [-> hrtn]].
  cbn [SweepRV] in hsw.
  pose proof (era_step hsw) as hstep.
  rewrite (cons_zero_tailT (tree_c_pos_of_WF_u (proj1 (proj1 hrtn)))) in hstep.
  exists (eraCfg (evalT tn)).
  split; [exists tn; auto | exact hstep].
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init_to_era0 |].
  eapply (progress_nonhalt tm EraInv); [exact era_inv_step | exact era_inv_zero].
Qed.
