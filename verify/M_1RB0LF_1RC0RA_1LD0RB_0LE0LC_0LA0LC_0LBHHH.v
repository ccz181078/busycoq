(* 1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN NArith PArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope bool_scope.
Open Scope N_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := Eval compute in
  (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---").
Arguments tm _ : simpl never.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* ========================================================================== *)
(* Section 1: Generic Helpers, Binary-N Word Powers, and Equality Reflections *)
(* ========================================================================== *)

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma ep_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma q_eqb_eq (q1 q2 : Q) : q_eqb q1 q2 = true <-> q1 = q2.
Proof. destruct q1, q2; simpl; split; intro H; congruence. Qed.

Lemma sym_eqb_eq (a b : Sym) : sym_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; intro H; congruence. Qed.

Fixpoint list_sym_eqb (xs ys : list Sym) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sym_eqb x y && list_sym_eqb xs' ys'
  | _, _ => false
  end.

Lemma list_sym_eqb_eq (xs ys : list Sym) : list_sym_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys.
  induction xs as [| x xs' IH]; intros [| y ys']; simpl.
  - split; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - rewrite Bool.andb_true_iff, sym_eqb_eq, IH.
    split; [intros [-> ->]; reflexivity | intro H; injection H as -> ->; auto].
Qed.

Lemma N_peano_ind (P : N -> Prop)
  (H0 : P 0) (HS : forall n : N, P n -> P (n + 1)) :
  forall n : N, P n.
Proof.
  intro n. induction n using N.peano_ind.
  - exact H0.
  - rewrite <- N.add_1_r. exact (HS n IHn).
Qed.

Lemma N_div2_le (a : N) : 2 * N.div2 a <= a.
Proof. rewrite N.div2_div. lia. Qed.

Definition npow {X : Type} (u : list X) (n : N) : list X :=
  match n with
  | N0 => []
  | Npos p => Pos.iter (fun acc => u ++ acc) [] p
  end.
Arguments npow {X} u n : simpl never.

Lemma npow_0 {X : Type} (u : list X) : npow u 0 = [].
Proof. reflexivity. Qed.

Lemma npow_succ_l {X : Type} (u : list X) (n : N) :
  npow u (n + 1) = u ++ npow u n.
Proof.
  destruct n as [| p]; unfold npow; simpl.
  - reflexivity.
  - rewrite Pos.add_1_r, Pos.iter_succ. reflexivity.
Qed.

Lemma npow_1 {X : Type} (u : list X) : npow u 1 = u.
Proof.
  change 1 with (0 + 1).
  rewrite npow_succ_l, npow_0, app_nil_r. reflexivity.
Qed.

Lemma npow_add {X : Type} (u : list X) (m n : N) :
  npow u (m + n) = npow u m ++ npow u n.
Proof.
  induction m as [| m IHm] using N_peano_ind.
  - rewrite N.add_0_l, npow_0. reflexivity.
  - replace (m + 1 + n) with ((m + n) + 1) by lia.
    rewrite !npow_succ_l, IHm, app_assoc. reflexivity.
Qed.

Lemma npow_shift {X : Type} (u : list X) (n : N) :
  npow u n ++ u = u ++ npow u n.
Proof.
  induction n as [| n IHn] using N_peano_ind.
  - rewrite npow_0, app_nil_r. reflexivity.
  - rewrite npow_succ_l, <- app_assoc, IHn. reflexivity.
Qed.

Lemma npow_succ_r {X : Type} (u : list X) (n : N) :
  npow u (n + 1) = npow u n ++ u.
Proof. rewrite npow_succ_l, npow_shift. reflexivity. Qed.

Lemma rev_npow {X : Type} (u : list X) (n : N) :
  rev (npow u n) = npow (rev u) n.
Proof.
  induction n as [| n IHn] using N_peano_ind.
  - rewrite !npow_0. reflexivity.
  - rewrite npow_succ_l, rev_app_distr, IHn, <- npow_succ_r. reflexivity.
Qed.

Lemma npow_rot {X : Type} (u w : list X) (n : N) :
  npow (u ++ w) n ++ u = u ++ npow (w ++ u) n.
Proof.
  induction n as [| n IHn] using N_peano_ind.
  - rewrite !npow_0; simpl; rewrite app_nil_r. reflexivity.
  - rewrite !npow_succ_l, <- !app_assoc, IHn. reflexivity.
Qed.

Lemma blank_b2_0 : [S0; S0] *> const S0 = const S0.
Proof. simpl. repeat rewrite <- const_unfold. reflexivity. Qed.

Lemma npow_blank0 (n : N) : npow [S0; S0] n *> const S0 = const S0.
Proof.
  induction n as [| n IHn] using N_peano_ind.
  - rewrite npow_0. reflexivity.
  - rewrite npow_succ_l, Str_app_assoc, IHn, blank_b2_0. reflexivity.
Qed.

Lemma pos_iter_opt_sound {S : Type} (eval : S -> Q * tape) (stepFn : S -> option S)
  (Hstep : forall s s', stepFn s = Some s' -> eval s -->* eval s') :
  forall (p : positive) (o : option S) (s' : S),
    Pos.iter (fun x => match x with Some y => stepFn y | None => None end) o p = Some s' ->
    exists s, o = Some s /\ eval s -->* eval s'.
Proof.
  induction p as [p IHp | p IHp | ]; intros o s' H; simpl in H.
  - destruct (Pos.iter _ (Pos.iter _ o p) p) as [sm2 | ] eqn:E2; [| discriminate].
    destruct (IHp _ _ E2) as [sm1 [E1 Hr2]].
    destruct (IHp _ _ E1) as [s0 [-> Hr1]].
    exists s0. split; [reflexivity | exact (etrans Hr1 (etrans Hr2 (Hstep _ _ H)))].
  - destruct (IHp _ _ H) as [sm [Em Hr2]].
    destruct (IHp _ _ Em) as [s0 [-> Hr1]].
    exists s0. split; [reflexivity | exact (etrans Hr1 Hr2)].
  - destruct o as [s0 | ]; [| discriminate].
    exists s0. split; [reflexivity | exact (Hstep _ _ H)].
Qed.

Corollary pos_iter_sound {S : Type} (eval : S -> Q * tape) (stepFn : S -> option S)
  (Hstep : forall s s', stepFn s = Some s' -> eval s -->* eval s')
  (p : positive) (s s' : S)
  (H : Pos.iter (fun x => match x with Some y => stepFn y | None => None end) (Some s) p = Some s') :
  eval s -->* eval s'.
Proof.
  destruct (pos_iter_opt_sound eval stepFn Hstep p (Some s) s' H) as [s0 [Heq Hr]].
  injection Heq as <-. exact Hr.
Qed.

(* ========================================================================== *)
(* Section 2: Directed Configurations, WordExits, Base Words, and Subwords    *)
(* ========================================================================== *)

Definition dirCfg (q : Q) (d : bool) (l r : side) : Q * tape :=
  if d then l {{q}}> r else l <{{q}} r.

Definition enterCfg (q : Q) (d : bool) (u : list Sym) (l r : side) : Q * tape :=
  if d then l {{q}}> (u *> r) else (rev u *> l) <{{q}} r.

Definition exitCfg (q' : Q) (d' : bool) (v : list Sym) (l r : side) : Q * tape :=
  if d' then (rev v *> l) {{q'}}> r else l <{{q'}} (v *> r).

Definition WordExit (u : list Sym) (q : Q) (d : bool)
  (v : list Sym) (q' : Q) (d' : bool) : Prop :=
  forall l r : side, enterCfg q d u l r -->* exitCfg q' d' v l r.

Fixpoint simWord (fuel : nat) (q : Q) (d : bool) (lw rw : list Sym)
  : option (list Sym * Q * bool) :=
  match fuel with
  | O => None
  | S fuel' =>
    if d then
      match rw with
      | [] => Some (rev lw, q, true)
      | a :: rw' =>
        match tm (q, a) with
        | None => None
        | Some (b, R, q') => simWord fuel' q' true (b :: lw) rw'
        | Some (b, L, q') => simWord fuel' q' false lw (b :: rw')
        end
      end
    else
      match lw with
      | [] => Some (rw, q, false)
      | a :: lw' =>
        match tm (q, a) with
        | None => None
        | Some (b, R, q') => simWord fuel' q' true (b :: lw') rw
        | Some (b, L, q') => simWord fuel' q' false lw' (b :: rw)
        end
      end
  end.

Definition runWordExit (fuel : nat) (u : list Sym) (q : Q) (d : bool)
  : option (list Sym * Q * bool) :=
  if d then simWord fuel q true [] u
  else simWord fuel q false (rev u) [].

Lemma simWord_sound_aux :
  forall (fuel : nat) (q : Q) (d : bool) (lw rw : list Sym)
    (v : list Sym) (q' : Q) (d' : bool) (l r : side),
    simWord fuel q d lw rw = Some (v, q', d') ->
    dirCfg q d (lw *> l) (rw *> r) -->* exitCfg q' d' v l r.
Proof.
  induction fuel as [| fuel' IH]; intros q d lw rw v q' d' l r H; [discriminate |].
  simpl in H.
  destruct d.
  - destruct rw as [| a rw'].
    + injection H as <- <- <-. simpl. rewrite rev_involutive. apply evstep_refl.
    + destruct (tm (q, a)) as [[[b dir_next] q_next] | ] eqn:E; [| discriminate].
      destruct dir_next.
      * eapply evstep_step; [exact (step_left E) | exact (IH _ _ _ _ _ _ _ _ _ H)].
      * eapply evstep_step; [exact (step_right E) | exact (IH _ _ _ _ _ _ _ _ _ H)].
  - destruct lw as [| a lw'].
    + injection H as <- <- <-. simpl. apply evstep_refl.
    + destruct (tm (q, a)) as [[[b dir_next] q_next] | ] eqn:E; [| discriminate].
      destruct dir_next.
      * eapply evstep_step; [exact (step_left E) | exact (IH _ _ _ _ _ _ _ _ _ H)].
      * eapply evstep_step; [exact (step_right E) | exact (IH _ _ _ _ _ _ _ _ _ H)].
Qed.

Lemma runWordExit_sound (fuel : nat) (u : list Sym) (q : Q) (d : bool)
  (v : list Sym) (q' : Q) (d' : bool) :
  runWordExit fuel u q d = Some (v, q', d') ->
  WordExit u q d v q' d'.
Proof.
  unfold runWordExit. intros H l r.
  destruct d; simpl.
  - exact (simWord_sound_aux fuel q true [] u v q' d' l r H).
  - exact (simWord_sound_aux fuel q false (rev u) [] v q' d' l r H).
Qed.

Lemma sweepWord_sound (u v : list Sym) (q : Q) (d : bool)
  (Hex : WordExit u q d v q d) (k : N) :
  WordExit (npow u k) q d (npow v k) q d.
Proof.
  induction k as [| k IHk] using N_peano_ind; unfold WordExit; intros l r.
  - rewrite !npow_0. destruct d; apply evstep_refl.
  - destruct d; cbn [enterCfg exitCfg].
    + rewrite npow_succ_l, Str_app_assoc, npow_succ_l, rev_app_distr, Str_app_assoc.
      exact (etrans (Hex l (npow u k *> r)) (IHk (rev v *> l) r)).
    + rewrite npow_succ_r, rev_app_distr, Str_app_assoc, npow_succ_r, Str_app_assoc.
      exact (etrans (Hex (rev (npow u k) *> l) r) (IHk l (v *> r))).
Qed.

Inductive B2 : Type := BZ | BY | BX | BW.

Definition b2_eqb (x y : B2) : bool :=
  match x, y with
  | BZ, BZ | BY, BY | BX, BX | BW, BW => true
  | _, _ => false
  end.

Lemma b2_eqb_eq (x y : B2) : b2_eqb x y = true <-> x = y.
Proof. destruct x, y; simpl; split; intro H; congruence. Qed.

Fixpoint list_b2_eqb (xs ys : list B2) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => b2_eqb x y && list_b2_eqb xs' ys'
  | _, _ => false
  end.

Lemma list_b2_eqb_eq (xs ys : list B2) : list_b2_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys.
  induction xs as [| x xs' IH]; intros [| y ys']; simpl.
  - split; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - rewrite Bool.andb_true_iff, b2_eqb_eq, IH.
    split; [intros [-> ->]; reflexivity | intro H; injection H as -> ->; auto].
Qed.

Definition b2Word (s : B2) : list Sym :=
  match s with
  | BZ => [S0; S0]
  | BY => [S0; S1]
  | BX => [S1; S0]
  | BW => [S1; S1]
  end.

Fixpoint concatB2 (u : list B2) : list Sym :=
  match u with
  | [] => []
  | s :: u' => b2Word s ++ concatB2 u'
  end.

Lemma concatB2_app (xs ys : list B2) :
  concatB2 (xs ++ ys) = concatB2 xs ++ concatB2 ys.
Proof.
  induction xs as [| s xs' IH]; simpl; [reflexivity | rewrite IH, app_assoc; reflexivity].
Qed.

Definition fastExit2 (q : Q) (d : bool) (s : B2) : option (B2 * Q * bool) :=
  if d then
    match q, s with
    | A, BZ => Some (BW, C, true)  | A, BY => Some (BX, A, true)
    | A, BX => Some (BZ, F, false) | A, BW => Some (BY, F, false)
    | B, BZ => Some (BY, C, false) | B, BY => Some (BX, B, true)
    | B, BX => Some (BY, B, true)  | B, BW => Some (BZ, B, false)
    | C, BZ => Some (BX, D, false) | C, BY => Some (BW, D, false)
    | C, BX => Some (BY, C, true)  | C, BW => Some (BZ, A, true)
    | D, BZ => Some (BZ, E, false) | D, BY => Some (BY, E, false)
    | D, BX => Some (BZ, C, false) | D, BW => Some (BY, C, false)
    | E, BZ => Some (BZ, A, false) | E, BY => Some (BY, A, false)
    | E, BX => Some (BZ, C, false) | E, BW => Some (BY, C, false)
    | F, BZ => Some (BZ, B, false) | F, BY => Some (BY, B, false)
    | _, _ => None
    end
  else
    match q, s with
    | A, BZ => Some (BY, B, true)  | A, BY => Some (BZ, B, false)
    | A, BX => Some (BW, B, true)  | A, BW => None
    | B, BZ => Some (BY, C, true)  | B, BY => Some (BZ, A, true)
    | B, BX => Some (BW, C, true)  | B, BW => Some (BX, A, true)
    | C, BZ => Some (BY, E, false) | C, BY => Some (BZ, B, true)
    | C, BX => Some (BY, C, false) | C, BW => Some (BX, B, true)
    | D, BZ => Some (BZ, A, false) | D, BY => Some (BX, D, false)
    | D, BX => Some (BZ, C, false) | D, BW => Some (BY, C, true)
    | E, BZ => Some (BW, C, true)  | E, BY => Some (BX, D, false)
    | E, BX => Some (BZ, F, false) | E, BW => Some (BY, C, true)
    | F, BZ => Some (BY, C, false) | F, BY => None
    | F, BX => Some (BY, B, true)  | F, BW => None
    end.
Arguments fastExit2 _ _ _ : simpl never.

Definition checkFastExit2One (q : Q) (d : bool) (s : B2) : bool :=
  match fastExit2 q d s with
  | None => true
  | Some (s', q', d') =>
    match runWordExit 10%nat (b2Word s) q d with
    | Some (v, q_out, d_out) =>
      list_sym_eqb v (b2Word s') && q_eqb q_out q' && Bool.eqb d_out d'
    | None => false
    end
  end.

Lemma fastExit2_sound (q : Q) (d : bool) (s : B2) (s' : B2) (q' : Q) (d' : bool) :
  fastExit2 q d s = Some (s', q', d') ->
  WordExit (b2Word s) q d (b2Word s') q' d'.
Proof.
  intro Hfe.
  assert (Hchk : checkFastExit2One q d s = true) by
    (destruct q, d, s; vm_compute; reflexivity).
  unfold checkFastExit2One in Hchk. rewrite Hfe in Hchk.
  destruct (runWordExit 10%nat (b2Word s) q d) as [[[v q_out] d_out] | ] eqn:Erun; [| discriminate].
  rewrite !Bool.andb_true_iff, list_sym_eqb_eq, q_eqb_eq, Bool.eqb_true_iff in Hchk.
  destruct Hchk as [[-> ->] ->].
  exact (runWordExit_sound 10%nat _ _ _ _ _ _ Erun).
Qed.

Fixpoint simSubwords (fuel : nat) (q : Q) (d : bool) (lw rw : list B2)
  : option (list B2 * Q * bool) :=
  match fuel with
  | O => None
  | S fuel' =>
    if d then
      match rw with
      | [] => Some (rev lw, q, true)
      | a :: rw' =>
        match fastExit2 q true a with
        | None => None
        | Some (s', q', d') =>
          if d' then simSubwords fuel' q' true (s' :: lw) rw'
          else simSubwords fuel' q' false lw (s' :: rw')
        end
      end
    else
      match lw with
      | [] => Some (rw, q, false)
      | a :: lw' =>
        match fastExit2 q false a with
        | None => None
        | Some (s', q', d') =>
          if d' then simSubwords fuel' q' true (s' :: lw') rw
          else simSubwords fuel' q' false lw' (s' :: rw)
        end
      end
  end.

Definition runCompositeExit (u : list B2) (q : Q) (d : bool)
  : option (list B2 * Q * bool) :=
  let fuel := (List.length u * 16 + 16)%nat in
  if d then simSubwords fuel q true [] u
  else simSubwords fuel q false (rev u) [].

Fixpoint leftSubTape (lw : list B2) (l : side) : side :=
  match lw with
  | [] => l
  | s :: lw' => rev (b2Word s) *> leftSubTape lw' l
  end.

Fixpoint rightSubTape (rw : list B2) (r : side) : side :=
  match rw with
  | [] => r
  | s :: rw' => b2Word s *> rightSubTape rw' r
  end.

Lemma rightSubTape_eq (rw : list B2) (r : side) :
  rightSubTape rw r = concatB2 rw *> r.
Proof.
  induction rw as [| s rw' IH]; simpl; [reflexivity | rewrite IH, Str_app_assoc; reflexivity].
Qed.

Lemma leftSubTape_app (xs ys : list B2) (l : side) :
  leftSubTape (xs ++ ys) l = leftSubTape xs (leftSubTape ys l).
Proof.
  induction xs as [| s xs' IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma leftSubTape_rev_eq (u : list B2) :
  forall l : side, leftSubTape (rev u) l = rev (concatB2 u) *> l.
Proof.
  induction u as [| s u' IH]; intro l; simpl; [reflexivity |].
  rewrite leftSubTape_app, rev_app_distr, Str_app_assoc. simpl.
  rewrite IH. reflexivity.
Qed.

Lemma leftSubTape_eq (lw : list B2) (l : side) :
  leftSubTape lw l = rev (concatB2 (rev lw)) *> l.
Proof.
  rewrite <- leftSubTape_rev_eq, rev_involutive. reflexivity.
Qed.

Lemma simSubwords_sound_aux :
  forall (fuel : nat) (q : Q) (d : bool) (lw rw : list B2)
    (v : list B2) (q' : Q) (d' : bool) (l r : side),
    simSubwords fuel q d lw rw = Some (v, q', d') ->
    dirCfg q d (leftSubTape lw l) (rightSubTape rw r) -->* exitCfg q' d' (concatB2 v) l r.
Proof.
  induction fuel as [| fuel' IH]; intros q d lw rw v q' d' l r H; [discriminate |].
  simpl in H.
  destruct d.
  - destruct rw as [| a rw'].
    + injection H as <- <- <-. simpl. rewrite leftSubTape_eq. apply evstep_refl.
    + destruct (fastExit2 q true a) as [[[s' q_next] d_next] | ] eqn:Efe; [| discriminate].
      pose proof (fastExit2_sound q true a s' q_next d_next Efe
        (leftSubTape lw l) (rightSubTape rw' r)) as Hex.
      destruct d_next; simpl in Hex.
      * exact (etrans Hex (IH _ _ _ _ _ _ _ _ _ H)).
      * exact (etrans Hex (IH _ _ _ _ _ _ _ _ _ H)).
  - destruct lw as [| a lw'].
    + injection H as <- <- <-. simpl. rewrite rightSubTape_eq. apply evstep_refl.
    + destruct (fastExit2 q false a) as [[[s' q_next] d_next] | ] eqn:Efe; [| discriminate].
      pose proof (fastExit2_sound q false a s' q_next d_next Efe
        (leftSubTape lw' l) (rightSubTape rw r)) as Hex.
      destruct d_next; simpl in Hex.
      * exact (etrans Hex (IH _ _ _ _ _ _ _ _ _ H)).
      * exact (etrans Hex (IH _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma runCompositeExit_sound (u : list B2) (q : Q) (d : bool)
  (v : list B2) (q' : Q) (d' : bool) :
  runCompositeExit u q d = Some (v, q', d') ->
  WordExit (concatB2 u) q d (concatB2 v) q' d'.
Proof.
  unfold runCompositeExit. intros H l r.
  destruct d; simpl.
  - pose proof (simSubwords_sound_aux _ q true [] u v q' d' l r H) as Hr.
    simpl in Hr. rewrite rightSubTape_eq in Hr. exact Hr.
  - pose proof (simSubwords_sound_aux _ q false (rev u) [] v q' d' l r H) as Hr.
    simpl in Hr. rewrite leftSubTape_rev_eq in Hr. exact Hr.
Qed.

(* ========================================================================== *)
(* Section 3: Quadratic Counter Transfers & Entry Phase (c0 -->* C(8))        *)
(* ========================================================================== *)

Lemma transferD_one (b : N) (lTail : side) :
  ([S0; S0] *> npow [S1; S0] 2 *> lTail) <{{D}} (npow [S1; S0] b *> const S0) -->*
  ([S0; S0] *> lTail) <{{D}} (npow [S1; S0] (b + 3) *> const S0).
Proof.
  assert (Hopen : WordExit [S0; S1; S0; S1; S0; S0] D false [S0; S0; S0; S1; S0; S1] C true) by
    (apply (runWordExit_sound 20%nat); vm_compute; reflexivity).
  pose proof (Hopen lTail (npow [S1; S0] b *> const S0)) as H1. simpl in H1.
  replace (npow [S1; S0] 2) with ([S1; S0; S1; S0]) by
    (change 2 with (1 + 1); rewrite npow_succ_l, npow_1; reflexivity).
  simpl in *.
  eapply etrans; [exact H1 |].
  assert (HexC : WordExit [S1; S0] C true [S0; S1] C true) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (sweepWord_sound _ _ _ _ HexC b ([S1; S0; S1; S0] *> [S0; S0] *> lTail) (const S0)) as H2.
  simpl in H2. rewrite rev_npow in H2. simpl in H2.
  eapply etrans; [exact H2 |].
  assert (HexTurn : WordExit [S0; S0] C true [S1; S0] D false) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (HexTurn (npow [S1; S0] b *> [S1; S0; S1; S0] *> [S0; S0] *> lTail) (const S0)) as H3.
  simpl in H3. rewrite <- const_unfold in H3 at 1.
  eapply etrans; [exact H3 |].
  assert (HexD : WordExit [S0; S1] D false [S1; S0] D false) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (sweepWord_sound _ _ _ _ HexD (b + 2) ([S0; S0] *> lTail) ([S1; S0] *> const S0)) as H4.
  simpl in H4. rewrite rev_npow in H4. simpl in H4.
  replace (npow [S1; S0] b *> S1 >> S0 >> S1 >> S0 >> S0 >> S0 >> lTail) with
    (npow [S1; S0] (b + 2) *> S0 >> S0 >> lTail) by
    (change (S1 >> S0 >> S1 >> S0 >> S0 >> S0 >> lTail) with
      (npow [S1; S0] 2 *> S0 >> S0 >> lTail);
     rewrite npow_add, Str_app_assoc; reflexivity).
  replace (npow [S1; S0] (b + 3) *> const S0) with
    (npow [S1; S0] (b + 2) *> S1 >> S0 >> const S0) by
    (replace (b + 3) with ((b + 2) + 1) by lia;
     rewrite npow_succ_r, Str_app_assoc; reflexivity).
  exact H4.
Qed.

Lemma transferD_batch (k : N) :
  forall (b : N) (lTail : side),
    ([S0; S0] *> npow [S1; S0] (2 * k) *> lTail) <{{D}} (npow [S1; S0] b *> const S0) -->*
    ([S0; S0] *> lTail) <{{D}} (npow [S1; S0] (b + 3 * k) *> const S0).
Proof.
  induction k as [| k IHk] using N_peano_ind; intros b lTail.
  - rewrite !N.mul_0_r, npow_0, N.add_0_r. apply evstep_refl.
  - replace (2 * (k + 1)) with (2 + 2 * k) by lia.
    rewrite npow_add, Str_app_assoc.
    eapply etrans; [apply transferD_one |].
    replace (b + 3 * (k + 1)) with ((b + 3) + 3 * k) by lia.
    apply IHk.
Qed.

Lemma transferB_one (b : N) (lTail : side) :
  ([S0; S1; S0; S0] *> npow [S0; S1] 2 *> lTail) {{B}}> (npow [S0; S1] b *> const S0) -->*
  ([S0; S1; S0; S0] *> lTail) {{B}}> (npow [S0; S1] (b + 3) *> const S0).
Proof.
  set (midL := [S0; S0] *> npow [S0; S1] 2 *> lTail).
  assert (HexB : WordExit [S0; S1] B true [S1; S0] B true) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (sweepWord_sound _ _ _ _ HexB b ([S0; S1] *> midL) (const S0)) as H1.
  simpl in H1. rewrite rev_npow in H1. simpl in H1.
  change (([S0; S1; S0; S0] *> npow [S0; S1] 2 *> lTail)) with (S0 >> S1 >> midL).
  eapply etrans; [exact H1 |].
  assert (HexTurn : WordExit [S0; S0] B true [S0; S1] C false) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (HexTurn (npow [S0; S1] (b + 1) *> midL) (const S0)) as H2.
  simpl in H2. rewrite <- const_unfold in H2 at 1.
  change Sym with sym in *.
  replace (npow [S0; S1] b *> S0 >> S1 >> midL) with (npow [S0; S1] (b + 1) *> midL) by
    (rewrite npow_succ_r, Str_app_assoc; reflexivity).
  eapply etrans; [exact H2 |].
  assert (HexCL : WordExit [S1; S0] C false [S0; S1] C false) by
    (apply (runWordExit_sound 10%nat); vm_compute; reflexivity).
  pose proof (sweepWord_sound _ _ _ _ HexCL (b + 1) midL ([S0; S1] *> const S0)) as H3.
  simpl in H3. rewrite rev_npow in H3. simpl in H3.
  eapply etrans; [exact H3 |].
  set (r2 := npow [S0; S1] (b + 2) *> const S0).
  change Sym with sym in *.
  replace (npow [S0; S1] (b + 1) *> S0 >> S1 >> const S0) with r2 by
    (unfold r2; replace (b + 2) with ((b + 1) + 1) by lia;
     rewrite npow_succ_r, Str_app_assoc; reflexivity).
  assert (HexL5 : WordExit [S0; S1; S0; S0; S0] C false [S0; S0; S0; S0; S1] B false) by
    (apply (runWordExit_sound 15%nat); vm_compute; reflexivity).
  pose proof (HexL5 (S1 >> lTail) r2) as H4. simpl in H4.
  change Sym with sym in *.
  replace midL with (S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> lTail) by
    (unfold midL; change 2 with (1 + 1); rewrite npow_succ_l, npow_1; reflexivity).
  eapply etrans; [exact H4 |].
  assert (HexB1 : WordExit [S1] B false [S0] A true) by
    (apply (runWordExit_sound 5%nat); vm_compute; reflexivity).
  pose proof (HexB1 lTail ([S0; S0; S0; S0; S1] *> r2)) as H5. simpl in H5.
  eapply etrans; [exact H5 |].
  assert (HexR7 : WordExit [S0; S0; S0] A true [S0; S1; S0] B true) by
    (apply (runWordExit_sound 15%nat); vm_compute; reflexivity).
  pose proof (HexR7 (S0 >> lTail) ([S0; S1] *> r2)) as H6. simpl in H6.
  eapply etrans; [exact H6 |].
  change Sym with sym in *.
  replace (npow [S0; S1] (b + 3) *> const S0) with (S0 >> S1 >> r2) by
    (unfold r2; replace (b + 3) with ((b + 2) + 1) by lia;
     rewrite npow_succ_l; reflexivity).
  apply evstep_refl.
Qed.

Lemma transferB_batch (k : N) :
  forall (b : N) (lTail : side),
    ([S0; S1; S0; S0] *> npow [S0; S1] (2 * k) *> lTail) {{B}}> (npow [S0; S1] b *> const S0) -->*
    ([S0; S1; S0; S0] *> lTail) {{B}}> (npow [S0; S1] (b + 3 * k) *> const S0).
Proof.
  induction k as [| k IHk] using N_peano_ind; intros b lTail.
  - rewrite !N.mul_0_r, npow_0, N.add_0_r. apply evstep_refl.
  - replace (2 * (k + 1)) with (2 + 2 * k) by lia.
    rewrite npow_add, Str_app_assoc.
    eapply etrans; [apply transferB_one |].
    replace (b + 3 * (k + 1)) with ((b + 3) + 3 * k) by lia.
    apply IHk.
Qed.

Definition EntryCfg := (Q * bool * list (B2 * N) * list (B2 * N))%type.

Definition pushLit (s : B2) (cnt : N) (stk : list (B2 * N)) : list (B2 * N) :=
  match stk with
  | [] => match s with BZ => [] | _ => [(s, cnt)] end
  | (ts, tc) :: rest =>
    if b2_eqb ts s then (ts, tc + cnt) :: rest else (s, cnt) :: stk
  end.

Definition pushRun (s : B2) (cnt : N) (stk : list (B2 * N)) : list (B2 * N) :=
  if N.eqb cnt 0 then stk else pushLit s cnt stk.

Fixpoint pushRunsLeft (xs : list (B2 * N)) (stk : list (B2 * N)) : list (B2 * N) :=
  match xs with
  | [] => stk
  | (s, n) :: rest => pushRunsLeft rest (pushRun s n stk)
  end.

Definition popOne (stk : list (B2 * N)) : option (B2 * list (B2 * N)) :=
  match stk with
  | [] => Some (BZ, [])
  | (ts, tc) :: rest =>
    if N.eqb tc 0 then None
    else if N.eqb tc 1 then Some (ts, rest)
    else Some (ts, (ts, tc - 1) :: rest)
  end.

Definition topSym (stk : list (B2 * N)) : B2 :=
  match stk with [] => BZ | (s, _) :: _ => s end.

Fixpoint evalSide (d : bool) (stk : list (B2 * N)) : side :=
  match stk with
  | [] => const S0
  | (s, c) :: rest =>
    if d then npow (b2Word s) c *> evalSide true rest
    else npow (rev (b2Word s)) c *> evalSide false rest
  end.

Definition evalEntryCfg (c : EntryCfg) : Q * tape :=
  let '(q, d, l, r) := c in
  dirCfg q d (evalSide false l) (evalSide true r).

Lemma evalSide_pushLit (d : bool) (s : B2) (cnt : N) (stk : list (B2 * N)) :
  evalSide d (pushLit s cnt stk) =
  (if d then npow (b2Word s) cnt *> evalSide true stk
   else npow (rev (b2Word s)) cnt *> evalSide false stk).
Proof.
  destruct stk as [| [ts tc] rest]; simpl.
  - destruct s, d; simpl; try reflexivity; rewrite npow_blank0; reflexivity.
  - destruct (b2_eqb ts s) eqn:Eeq.
    + apply b2_eqb_eq in Eeq. subst ts.
      destruct d; simpl; rewrite N.add_comm, npow_add, Str_app_assoc; reflexivity.
    + destruct d; reflexivity.
Qed.

Lemma popOne_sound (stk stk' : list (B2 * N)) (s : B2) (d : bool) :
  popOne stk = Some (s, stk') ->
  s = topSym stk /\
  evalSide d stk =
  (if d then b2Word s *> evalSide true stk'
   else rev (b2Word s) *> evalSide false stk').
Proof.
  destruct stk as [| [ts tc] rest]; simpl; intro H.
  - injection H as <- <-. split; [reflexivity |].
    destruct d; simpl; repeat rewrite <- const_unfold; reflexivity.
  - destruct (N.eqb tc 0) eqn:E0; [discriminate |].
    apply N.eqb_neq in E0.
    destruct (N.eqb tc 1) eqn:E1.
    + apply N.eqb_eq in E1. subst tc. injection H as <- <-.
      split; [reflexivity | destruct d; simpl; rewrite npow_1; reflexivity].
    + apply N.eqb_neq in E1. injection H as <- <-.
      split; [reflexivity |].
      assert (Htc : tc = (tc - 1) + 1) by lia.
      destruct d; simpl; rewrite Htc at 1; rewrite npow_succ_l, Str_app_assoc; reflexivity.
Qed.

Definition isStopEarly (q q' : Q) (d' : bool) (l r : list (B2 * N)) : bool :=
  if q_eqb q' q && d' && q_eqb q B && b2_eqb (topSym r) BY then
    match r, l with
    | [_], (s0, c0) :: (s1, aCnt) :: _ =>
      b2_eqb s0 BZ && N.eqb c0 1 && b2_eqb s1 BX && N.leb 2 aCnt
    | _, _ => false
    end
  else false.

Definition stepNormal (q : Q) (d : bool) (l r : list (B2 * N)) : option EntryCfg :=
  if d then
    match fastExit2 q true (topSym r) with
    | None => None
    | Some (s', q', d') =>
      if q_eqb q' q && d' && negb (isStopEarly q q' d' l r) then
        match r with
        | [] => None
        | (_, tc) :: rest => Some (q', true, pushLit s' tc l, rest)
        end
      else
        match popOne r with
        | None => None
        | Some (_, r') =>
          if d' then Some (q', true, pushLit s' 1 l, r')
          else Some (q', false, l, pushLit s' 1 r')
        end
    end
  else
    match fastExit2 q false (topSym l) with
    | None => None
    | Some (s', q', d') =>
      if q_eqb q' q && negb d' then
        match l with
        | [] => None
        | (_, tc) :: rest => Some (q', false, rest, pushLit s' tc r)
        end
      else
        match popOne l with
        | None => None
        | Some (_, l') =>
          if d' then Some (q', true, pushLit s' 1 l', r)
          else Some (q', false, l', pushLit s' 1 r)
        end
    end.

Lemma stepNormal_sound (q : Q) (d : bool) (l r : list (B2 * N)) (c' : EntryCfg) :
  stepNormal q d l r = Some c' ->
  evalEntryCfg (q, d, l, r) -->* evalEntryCfg c'.
Proof.
  unfold stepNormal. intro H.
  destruct d.
  - destruct (fastExit2 q true (topSym r)) as [[[s' q'] d'] | ] eqn:Efe; [| discriminate].
    pose proof (fastExit2_sound q true (topSym r) s' q' d' Efe) as Hex.
    destruct (q_eqb q' q && d' && negb (isStopEarly q q' d' l r)) eqn:Esw.
    + destruct r as [| [ts tc] rest]; [discriminate |].
      injection H as <-.
      rewrite !Bool.andb_true_iff, q_eqb_eq in Esw.
      destruct Esw as [[-> ->] _].
      pose proof (sweepWord_sound _ _ _ _ Hex tc (evalSide false l) (evalSide true rest)) as Hr.
      simpl in Hr. rewrite rev_npow in Hr.
      unfold evalEntryCfg. simpl. rewrite evalSide_pushLit. exact Hr.
    + destruct (popOne r) as [[ps r'] | ] eqn:Epop; [| discriminate].
      destruct (popOne_sound r r' ps true Epop) as [Hps HrEq]. subst ps.
      pose proof (Hex (evalSide false l) (evalSide true r')) as Hrun.
      destruct d'; injection H as <-; unfold evalEntryCfg; simpl in *;
        rewrite HrEq, evalSide_pushLit, npow_1; exact Hrun.
  - destruct (fastExit2 q false (topSym l)) as [[[s' q'] d'] | ] eqn:Efe; [| discriminate].
    pose proof (fastExit2_sound q false (topSym l) s' q' d' Efe) as Hex.
    destruct (q_eqb q' q && negb d') eqn:Esw.
    + destruct l as [| [ts tc] rest]; [discriminate |].
      injection H as <-.
      rewrite Bool.andb_true_iff, q_eqb_eq, Bool.negb_true_iff in Esw.
      destruct Esw as [-> ->].
      pose proof (sweepWord_sound _ _ _ _ Hex tc (evalSide false rest) (evalSide true r)) as Hr.
      simpl in Hr. rewrite rev_npow in Hr.
      unfold evalEntryCfg. simpl. rewrite evalSide_pushLit. exact Hr.
    + destruct (popOne l) as [[ps l'] | ] eqn:Epop; [| discriminate].
      destruct (popOne_sound l l' ps false Epop) as [Hps HlEq]. subst ps.
      pose proof (Hex (evalSide false l') (evalSide true r)) as Hrun.
      destruct d'; injection H as <-; unfold evalEntryCfg; simpl in *;
        rewrite HlEq, evalSide_pushLit, npow_1; exact Hrun.
Qed.

Definition transferRightCount (expSym : B2) (r : list (B2 * N)) : option N :=
  match r with
  | [] => Some 0
  | [(s, b)] => if b2_eqb s expSym then Some b else None
  | _ => None
  end.

Lemma transferRightCount_eval (expSym : B2) (r : list (B2 * N)) (b : N) :
  transferRightCount expSym r = Some b ->
  evalSide true r = npow (b2Word expSym) b *> const S0.
Proof.
  destruct r as [| [s c] [| ? ?]]; simpl; intro H.
  - injection H as <-. rewrite npow_0. reflexivity.
  - destruct (b2_eqb s expSym) eqn:Es; [| discriminate].
    apply b2_eqb_eq in Es. subst s. injection H as <-. reflexivity.
  - discriminate.
Qed.

Definition zOkD (tail : list (B2 * N)) : bool :=
  match tail with [] => true | (BZ, _) :: _ | (BX, _) :: _ => true | _ => false end.

Definition zOkB (tail : list (B2 * N)) : bool :=
  match tail with [] => true | (BZ, _) :: _ => true | _ => false end.

Definition transferDLBase (a : N) (tail : list (B2 * N)) : list (B2 * N) :=
  let rem := a - 2 * N.div2 a in
  if N.eqb rem 0 then tail else (BY, rem) :: tail.
Arguments transferDLBase _ _ : simpl never.

Definition transferBLBase (a : N) (tail : list (B2 * N)) : list (B2 * N) :=
  let rem := a - 2 * N.div2 a in
  if N.eqb rem 0 then tail else (BX, rem) :: tail.
Arguments transferBLBase _ _ : simpl never.

Definition transferDCfg (a b : N) (tail : list (B2 * N)) : EntryCfg :=
  (D, false, pushLit BZ 1 (transferDLBase a tail), [(BX, b + 3 * N.div2 a)]).

Definition transferBCfg (a b : N) (tail : list (B2 * N)) : EntryCfg :=
  (B, true, pushLit BX 1 (pushLit BZ 1 (transferBLBase a tail)), [(BY, b + 3 * N.div2 a)]).

Lemma transferDLBase_eval (a : N) (tail : list (B2 * N)) :
  npow (rev (b2Word BY)) a *> evalSide false tail =
  npow (rev (b2Word BY)) (2 * N.div2 a) *> evalSide false (transferDLBase a tail).
Proof.
  unfold transferDLBase.
  set (k := N.div2 a). set (rem := a - 2 * k).
  assert (Hk : 2 * k <= a) by (unfold k; apply N_div2_le).
  assert (Ha : a = 2 * k + rem) by (unfold rem; lia).
  rewrite Ha, npow_add, Str_app_assoc. f_equal.
  destruct (N.eqb rem 0) eqn:Er0.
  - apply N.eqb_eq in Er0. rewrite Er0, npow_0. reflexivity.
  - reflexivity.
Qed.

Lemma transferBLBase_eval (a : N) (tail : list (B2 * N)) :
  npow (rev (b2Word BX)) a *> evalSide false tail =
  npow (rev (b2Word BX)) (2 * N.div2 a) *> evalSide false (transferBLBase a tail).
Proof.
  unfold transferBLBase.
  set (k := N.div2 a). set (rem := a - 2 * k).
  assert (Hk : 2 * k <= a) by (unfold k; apply N_div2_le).
  assert (Ha : a = 2 * k + rem) by (unfold rem; lia).
  rewrite Ha, npow_add, Str_app_assoc. f_equal.
  destruct (N.eqb rem 0) eqn:Er0.
  - apply N.eqb_eq in Er0. rewrite Er0, npow_0. reflexivity.
  - reflexivity.
Qed.

Definition stepEntry (c : EntryCfg) : option EntryCfg :=
  let '(q, d, l, r) := c in
  if negb d && q_eqb q D then
    match l with
    | (s0, c0) :: (s1, a) :: tail =>
      if b2_eqb s0 BZ && N.eqb c0 1 && b2_eqb s1 BY && N.leb 2 a && zOkD tail then
        match transferRightCount BX r with
        | Some b => Some (transferDCfg a b tail)
        | None => stepNormal D false l r
        end
      else stepNormal D false l r
    | _ => stepNormal D false l r
    end
  else if d && q_eqb q B then
    match l with
    | (s0, c0) :: (s1, c1) :: (s2, a) :: tail =>
      if b2_eqb s0 BX && N.eqb c0 1 && b2_eqb s1 BZ && N.eqb c1 1 &&
         b2_eqb s2 BX && N.leb 2 a && zOkB tail then
        match transferRightCount BY r with
        | Some b => Some (transferBCfg a b tail)
        | None => stepNormal B true l r
        end
      else stepNormal B true l r
    | _ => stepNormal B true l r
    end
  else stepNormal q d l r.

Lemma stepEntry_sound (c c' : EntryCfg) :
  stepEntry c = Some c' ->
  evalEntryCfg c -->* evalEntryCfg c'.
Proof.
  destruct c as [[[q d] l] r]. unfold stepEntry. intro H.
  destruct (negb d && q_eqb q D) eqn:EcD.
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, q_eqb_eq in EcD.
    destruct EcD as [-> ->].
    destruct l as [| [s0 c0] [| [s1 a] tail]];
      try (exact (stepNormal_sound D false _ r c' H)).
    destruct (b2_eqb s0 BZ && N.eqb c0 1 && b2_eqb s1 BY && N.leb 2 a && zOkD tail) eqn:Econd;
      [| exact (stepNormal_sound D false _ r c' H)].
    rewrite !Bool.andb_true_iff, !b2_eqb_eq, N.eqb_eq in Econd.
    destruct Econd as [[[[-> ->] ->] _] _].
    destruct (transferRightCount BX r) as [b | ] eqn:Etr;
      [| exact (stepNormal_sound D false _ r c' H)].
    injection H as <-.
    unfold transferDCfg, evalEntryCfg, dirCfg. cbn [evalSide].
    rewrite (transferRightCount_eval BX r b Etr), evalSide_pushLit, !npow_1, transferDLBase_eval.
    exact (transferD_batch (N.div2 a) b (evalSide false (transferDLBase a tail))).
  - destruct (d && q_eqb q B) eqn:EcB;
      [| exact (stepNormal_sound q d l r c' H)].
    rewrite Bool.andb_true_iff, q_eqb_eq in EcB.
    destruct EcB as [-> ->].
    destruct l as [| [s0 c0] [| [s1 c1] [| [s2 a] tail]]];
      try (exact (stepNormal_sound B true _ r c' H)).
    destruct (b2_eqb s0 BX && N.eqb c0 1 && b2_eqb s1 BZ && N.eqb c1 1 &&
              b2_eqb s2 BX && N.leb 2 a && zOkB tail) eqn:Econd;
      [| exact (stepNormal_sound B true _ r c' H)].
    rewrite !Bool.andb_true_iff, !b2_eqb_eq, !N.eqb_eq in Econd.
    destruct Econd as [[[[[[-> ->] ->] ->] ->] _] _].
    destruct (transferRightCount BY r) as [b | ] eqn:Etr;
      [| exact (stepNormal_sound B true _ r c' H)].
    injection H as <-.
    unfold transferBCfg, evalEntryCfg, dirCfg. cbn [evalSide].
    rewrite (transferRightCount_eval BY r b Etr), !evalSide_pushLit, !npow_1, transferBLBase_eval.
    exact (transferB_batch (N.div2 a) b (evalSide false (transferBLBase a tail))).
Qed.

Definition stepEntryOpt (o : option EntryCfg) : option EntryCfg :=
  match o with Some c => stepEntry c | None => None end.

Definition uRuns : list (B2 * N) :=
  [(BX, 1); (BY, 1); (BZ, 1); (BX, 8); (BZ, 1); (BX, 5); (BY, 11); (BZ, 1)].
Definition pRuns : list (B2 * N) := [(BX, 8); (BY, 10); (BZ, 1)].
Definition vRuns : list (B2 * N) :=
  [(BX, 791761176); (BY, 9); (BZ, 1); (BX, 21); (BY, 41); (BZ, 1); (BX, 15); (BY, 93); (BZ, 1)].
Definition qRuns : list (B2 * N) :=
  [(BX, 36); (BY, 17); (BZ, 1); (BX, 91); (BY, 38); (BZ, 1); (BX, 15); (BY, 93); (BZ, 1)].
Definition wRuns : list (B2 * N) :=
  [(BX, 14); (BZ, 1); (BX, 5); (BZ, 1); (BX, 1)].

Fixpoint repListNat {X : Type} (n : nat) (xs : list X) : list X :=
  match n with O => [] | S n' => xs ++ repListNat n' xs end.

Definition e8L : list (B2 * N) :=
  pushRunsLeft (uRuns ++ repListNat 8%nat pRuns ++ vRuns ++ repListNat 8%nat qRuns ++ wRuns) [].

Definition entryMilestone8 : EntryCfg := (B, true, e8L, [(BY, 6)]).

Fixpoint runs_eqb (xs ys : list (B2 * N)) : bool :=
  match xs, ys with
  | [], [] => true
  | (s1, c1) :: r1, (s2, c2) :: r2 => b2_eqb s1 s2 && N.eqb c1 c2 && runs_eqb r1 r2
  | _, _ => false
  end.

Lemma runs_eqb_eq (xs ys : list (B2 * N)) : runs_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys.
  induction xs as [| [s1 c1] r1 IH]; intros [| [s2 c2] r2]; simpl.
  - split; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - rewrite !Bool.andb_true_iff, b2_eqb_eq, N.eqb_eq, IH.
    split; [intros [[-> ->] ->]; reflexivity | intro H; injection H as -> -> ->; auto].
Qed.

Definition entryCfg_eqb (c1 c2 : EntryCfg) : bool :=
  let '(q1, d1, l1, r1) := c1 in
  let '(q2, d2, l2, r2) := c2 in
  q_eqb q1 q2 && Bool.eqb d1 d2 && runs_eqb l1 l2 && runs_eqb r1 r2.

Lemma entryCfg_eqb_eq (c1 c2 : EntryCfg) : entryCfg_eqb c1 c2 = true <-> c1 = c2.
Proof.
  destruct c1 as [[[q1 d1] l1] r1], c2 as [[[q2 d2] l2] r2]; simpl.
  rewrite !Bool.andb_true_iff, q_eqb_eq, Bool.eqb_true_iff, !runs_eqb_eq.
  split; [intros [[[-> ->] ->] ->]; reflexivity | intro H; injection H as -> -> -> ->; auto].
Qed.

Lemma entry_run_ok :
  match Pos.iter stepEntryOpt (Some (A, false, [], [])) 166491%positive with
  | Some c => entryCfg_eqb c entryMilestone8
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma entry_to_c8 : c0 -->* evalEntryCfg entryMilestone8.
Proof.
  pose proof entry_run_ok as Hok.
  destruct (Pos.iter stepEntryOpt (Some (A, false, [], [])) 166491%positive) as [c | ] eqn:Eiter;
    [| discriminate].
  apply entryCfg_eqb_eq in Hok. subst c.
  exact (pos_iter_sound evalEntryCfg stepEntry stepEntry_sound 166491%positive
    (A, false, [], []) entryMilestone8 Eiter).
Qed.

(* ========================================================================== *)
(* Section 4: Dynamic Composite Vocabulary, Exit Tries, and Symbolic Return   *)
(* ========================================================================== *)

Inductive PosTrie (V : Type) : Type :=
| PTLeaf : PosTrie V
| PTNode : option V -> PosTrie V -> PosTrie V -> PosTrie V.
Arguments PTLeaf {V}.
Arguments PTNode {V} _ _ _.

Fixpoint pt_find {V : Type} (t : PosTrie V) (p : positive) : option V :=
  match t with
  | PTLeaf => None
  | PTNode v l r =>
    match p with xH => v | xO p' => pt_find l p' | xI p' => pt_find r p' end
  end.

Fixpoint pt_ins {V : Type} (t : PosTrie V) (p : positive) (val : V) : PosTrie V :=
  match t with
  | PTLeaf =>
    match p with
    | xH => PTNode (Some val) PTLeaf PTLeaf
    | xO p' => PTNode None (pt_ins PTLeaf p' val) PTLeaf
    | xI p' => PTNode None PTLeaf (pt_ins PTLeaf p' val)
    end
  | PTNode v l r =>
    match p with
    | xH => PTNode (Some val) l r
    | xO p' => PTNode v (pt_ins l p' val) r
    | xI p' => PTNode v l (pt_ins r p' val)
    end
  end.

Fixpoint pt_check {V : Type} (pred : positive -> V -> bool)
  (ctx : positive -> positive) (t : PosTrie V) : bool :=
  match t with
  | PTLeaf => true
  | PTNode v l r =>
    (match v with None => true | Some x => pred (ctx xH) x end) &&
    pt_check pred (fun q => ctx (xO q)) l &&
    pt_check pred (fun q => ctx (xI q)) r
  end.

Lemma pt_check_sound {V : Type} (pred : positive -> V -> bool) :
  forall (t : PosTrie V) (ctx : positive -> positive) (p : positive) (x : V),
    pt_check pred ctx t = true ->
    pt_find t p = Some x ->
    pred (ctx p) x = true.
Proof.
  induction t as [| v l IHl r IHr]; intros ctx p x Hc Hf; [discriminate |].
  simpl in Hc, Hf.
  rewrite !Bool.andb_true_iff in Hc. destruct Hc as [[Hv Hl] Hr].
  destruct p as [p' | p' | ].
  - exact (IHr (fun q => ctx (xI q)) p' x Hr Hf).
  - exact (IHl (fun q => ctx (xO q)) p' x Hl Hf).
  - rewrite Hf in Hv. exact Hv.
Qed.

Definition NTrie (V : Type) : Type := (option V * PosTrie V)%type.
Definition nt_empty {V : Type} : NTrie V := (None, PTLeaf).

Definition nt_find {V : Type} (t : NTrie V) (n : N) : option V :=
  match n with N0 => fst t | Npos p => pt_find (snd t) p end.

Definition nt_ins {V : Type} (t : NTrie V) (n : N) (x : V) : NTrie V :=
  match n with N0 => (Some x, snd t) | Npos p => (fst t, pt_ins (snd t) p x) end.

Definition nt_check {V : Type} (pred : N -> V -> bool) (t : NTrie V) : bool :=
  (match fst t with None => true | Some x => pred N0 x end) &&
  pt_check (fun p x => pred (Npos p) x) (fun q => q) (snd t).

Lemma nt_check_sound {V : Type} (pred : N -> V -> bool) (t : NTrie V) (n : N) (x : V) :
  nt_check pred t = true ->
  nt_find t n = Some x ->
  pred n x = true.
Proof.
  unfold nt_check, nt_find. rewrite Bool.andb_true_iff.
  intros [H0 Hp] Hf.
  destruct n as [| p].
  - rewrite Hf in H0. exact H0.
  - exact (pt_check_sound (fun p0 x0 => pred (Npos p0) x0) (snd t) (fun q => q) p x Hp Hf).
Qed.

Definition CompExit := (N * Q * bool)%type.

Record QRow : Type := mkQRow {
  qrA : option CompExit; qrB : option CompExit; qrC : option CompExit;
  qrD : option CompExit; qrE : option CompExit; qrF : option CompExit
}.

Definition emptyQRow : QRow := mkQRow None None None None None None.

Definition qrow_get (r : QRow) (q : Q) : option CompExit :=
  match q with
  | A => qrA r | B => qrB r | C => qrC r
  | D => qrD r | E => qrE r | F => qrF r
  end.

Definition qrow_set (r : QRow) (q : Q) (v : option CompExit) : QRow :=
  match q with
  | A => mkQRow v (qrB r) (qrC r) (qrD r) (qrE r) (qrF r)
  | B => mkQRow (qrA r) v (qrC r) (qrD r) (qrE r) (qrF r)
  | C => mkQRow (qrA r) (qrB r) v (qrD r) (qrE r) (qrF r)
  | D => mkQRow (qrA r) (qrB r) (qrC r) v (qrE r) (qrF r)
  | E => mkQRow (qrA r) (qrB r) (qrC r) (qrD r) v (qrF r)
  | F => mkQRow (qrA r) (qrB r) (qrC r) (qrD r) (qrE r) v
  end.

Definition opt_check {V : Type} (f : V -> bool) (o : option V) : bool :=
  match o with None => true | Some x => f x end.

Definition qrow_check (f : Q -> CompExit -> bool) (r : QRow) : bool :=
  opt_check (f A) (qrA r) && opt_check (f B) (qrB r) && opt_check (f C) (qrC r) &&
  opt_check (f D) (qrD r) && opt_check (f E) (qrE r) && opt_check (f F) (qrF r).

Lemma qrow_check_sound (f : Q -> CompExit -> bool) (r : QRow) (q : Q) (ex : CompExit) :
  qrow_check f r = true -> qrow_get r q = Some ex -> f q ex = true.
Proof.
  unfold qrow_check, qrow_get. rewrite !Bool.andb_true_iff.
  intros [[[[[HA HB] HC] HD] HE] HF] Hget.
  destruct q; rewrite Hget in *; simpl in *; assumption.
Qed.

Definition ExitRow := (QRow * QRow)%type.
Definition emptyExitRow : ExitRow := (emptyQRow, emptyQRow).
Definition ExitsTable := NTrie ExitRow.

Definition lookupExit (exits : ExitsTable) (wid : N) (q : Q) (d : bool) : option CompExit :=
  match nt_find exits wid with
  | None => None
  | Some (rf, rt) => if d then qrow_get rt q else qrow_get rf q
  end.

Definition insertExit (exits : ExitsTable) (wid : N) (q : Q) (d : bool) (ex : CompExit)
  : ExitsTable :=
  let '(rf, rt) := match nt_find exits wid with None => emptyExitRow | Some p => p end in
  let er' := if d then (rf, qrow_set rt q (Some ex)) else (qrow_set rf q (Some ex), rt) in
  nt_ins exits wid er'.

Inductive WordTrie : Type :=
| WTLeaf : WordTrie
| WTNode : option N -> WordTrie -> WordTrie -> WordTrie -> WordTrie -> WordTrie.

Fixpoint wt_find (t : WordTrie) (w : list B2) : option N :=
  match t with
  | WTLeaf => None
  | WTNode v t0 t1 t2 t3 =>
    match w with
    | [] => v
    | BZ :: w' => wt_find t0 w'
    | BY :: w' => wt_find t1 w'
    | BX :: w' => wt_find t2 w'
    | BW :: w' => wt_find t3 w'
    end
  end.

Fixpoint wt_ins (t : WordTrie) (w : list B2) (id : N) : WordTrie :=
  match t with
  | WTLeaf =>
    match w with
    | [] => WTNode (Some id) WTLeaf WTLeaf WTLeaf WTLeaf
    | BZ :: w' => WTNode None (wt_ins WTLeaf w' id) WTLeaf WTLeaf WTLeaf
    | BY :: w' => WTNode None WTLeaf (wt_ins WTLeaf w' id) WTLeaf WTLeaf
    | BX :: w' => WTNode None WTLeaf WTLeaf (wt_ins WTLeaf w' id) WTLeaf
    | BW :: w' => WTNode None WTLeaf WTLeaf WTLeaf (wt_ins WTLeaf w' id)
    end
  | WTNode v t0 t1 t2 t3 =>
    match w with
    | [] => WTNode (Some id) t0 t1 t2 t3
    | BZ :: w' => WTNode v (wt_ins t0 w' id) t1 t2 t3
    | BY :: w' => WTNode v t0 (wt_ins t1 w' id) t2 t3
    | BX :: w' => WTNode v t0 t1 (wt_ins t2 w' id) t3
    | BW :: w' => WTNode v t0 t1 t2 (wt_ins t3 w' id)
    end
  end.

Fixpoint expandB2Runs (xs : list (B2 * N)) : list B2 :=
  match xs with
  | [] => []
  | (s, n) :: rest => npow [s] n ++ expandB2Runs rest
  end.

Definition pWordB2 : list B2 := expandB2Runs pRuns.
Definition qWordB2 : list B2 := expandB2Runs qRuns.

Definition seedB2 (wid : N) : list B2 :=
  if N.eqb wid 0 then [BZ]
  else if N.eqb wid 1 then [BY]
  else if N.eqb wid 2 then [BX]
  else if N.eqb wid 3 then [BW]
  else if N.eqb wid 4 then pWordB2
  else if N.eqb wid 5 then qWordB2
  else [BZ].

Definition seedWord (wid : N) : list Sym := concatB2 (seedB2 wid).

Definition vocWord (voc : NTrie (list B2)) (wid : N) : list Sym :=
  match nt_find voc wid with
  | Some u => concatB2 u
  | None => [S0; S0]
  end.

Definition checkSeedVocab (voc : NTrie (list B2)) : bool :=
  match nt_find voc 0, nt_find voc 1, nt_find voc 2,
        nt_find voc 3, nt_find voc 4, nt_find voc 5 with
  | Some w0, Some w1, Some w2, Some w3, Some w4, Some w5 =>
    list_b2_eqb w0 [BZ] && list_b2_eqb w1 [BY] && list_b2_eqb w2 [BX] &&
    list_b2_eqb w3 [BW] && list_b2_eqb w4 pWordB2 && list_b2_eqb w5 qWordB2
  | _, _, _, _, _, _ => false
  end.

Lemma checkSeedVocab_le5 (voc : NTrie (list B2)) (wid : N) :
  checkSeedVocab voc = true ->
  wid <= 5 ->
  vocWord voc wid = seedWord wid.
Proof.
  unfold checkSeedVocab, vocWord, seedWord, seedB2.
  destruct (nt_find voc 0) as [w0 | ] eqn:E0; [| discriminate].
  destruct (nt_find voc 1) as [w1 | ] eqn:E1; [| discriminate].
  destruct (nt_find voc 2) as [w2 | ] eqn:E2; [| discriminate].
  destruct (nt_find voc 3) as [w3 | ] eqn:E3; [| discriminate].
  destruct (nt_find voc 4) as [w4 | ] eqn:E4; [| discriminate].
  destruct (nt_find voc 5) as [w5 | ] eqn:E5; [| discriminate].
  rewrite !Bool.andb_true_iff, !list_b2_eqb_eq.
  intros [[[[[-> ->] ->] ->] ->] ->] Hle.
  assert (Hcases : wid = 0 \/ wid = 1 \/ wid = 2 \/ wid = 3 \/ wid = 4 \/ wid = 5) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    rewrite ?E0, ?E1, ?E2, ?E3, ?E4, ?E5; reflexivity.
Qed.

Definition checkExitOne (voc : NTrie (list B2)) (wid : N) (q : Q) (d : bool)
  (ex : CompExit) : bool :=
  let '(wid', q', d') := ex in
  match nt_find voc wid, nt_find voc wid' with
  | Some u, Some v =>
    match runCompositeExit u q d with
    | Some (v_out, q_out, d_out) =>
      list_b2_eqb v_out v && q_eqb q_out q' && Bool.eqb d_out d'
    | None => false
    end
  | _, _ => false
  end.

Definition checkAllExits (voc : NTrie (list B2)) (exits : ExitsTable) : bool :=
  nt_check (fun wid '(rf, rt) =>
    qrow_check (fun q ex => checkExitOne voc wid q false ex) rf &&
    qrow_check (fun q ex => checkExitOne voc wid q true ex) rt) exits.

Definition ExitsSound (wOf : N -> list Sym) (exits : ExitsTable) : Prop :=
  forall wid q d wid' q' d',
    lookupExit exits wid q d = Some (wid', q', d') ->
    WordExit (wOf wid) q d (wOf wid') q' d'.

Lemma checkAllExits_sound (voc : NTrie (list B2)) (exits : ExitsTable) :
  checkAllExits voc exits = true ->
  ExitsSound (vocWord voc) exits.
Proof.
  intros Hchk wid q d wid' q' d' Hlu.
  unfold lookupExit in Hlu.
  destruct (nt_find exits wid) as [[rf rt] | ] eqn:Ef; [| discriminate].
  pose proof (nt_check_sound _ exits wid (rf, rt) Hchk Ef) as Hrow.
  simpl in Hrow. rewrite Bool.andb_true_iff in Hrow. destruct Hrow as [Hrf Hrt].
  assert (Hone : checkExitOne voc wid q d (wid', q', d') = true).
  { destruct d.
    - exact (qrow_check_sound _ rt q (wid', q', d') Hrt Hlu).
    - exact (qrow_check_sound _ rf q (wid', q', d') Hrf Hlu). }
  unfold checkExitOne, vocWord in Hone |- *.
  destruct (nt_find voc wid) as [u | ]; [| discriminate].
  destruct (nt_find voc wid') as [v | ]; [| discriminate].
  destruct (runCompositeExit u q d) as [[[v_out q_out] d_out] | ] eqn:Erc; [| discriminate].
  rewrite !Bool.andb_true_iff, list_b2_eqb_eq, q_eqb_eq, Bool.eqb_true_iff in Hone.
  destruct Hone as [[-> ->] ->].
  exact (runCompositeExit_sound u q d v q' d' Erc).
Qed.

(* ========================================================================== *)
(* Section 5: Affine RLE Stacks, 3-Step Inner Cycle, and Symbolic Replay      *)
(* ========================================================================== *)

Notation AffN := (N * N)%type.
Notation AffRun := (N * AffN)%type.
Notation AffCfg := (Q * bool * list AffRun * list AffRun)%type.

Definition aff_eval (k : N) (x : AffN) : N := fst x * k + snd x.
Definition aff_isZero (x : AffN) : bool := N.eqb (fst x) 0 && N.eqb (snd x) 0.
Definition aff_isOne (x : AffN) : bool := N.eqb (fst x) 0 && N.eqb (snd x) 1.
Definition aff_ge1 (x : AffN) : bool := N.leb 1 (snd x).
Definition aff_add (x y : AffN) : AffN := (fst x + fst y, snd x + snd y).
Definition aff_sub (x y : AffN) : option AffN :=
  if N.leb (fst y) (fst x) && N.leb (snd y) (snd x) then
    Some (fst x - fst y, snd x - snd y)
  else None.

Lemma aff_eval_zero (x : AffN) (k : N) : aff_isZero x = true -> aff_eval k x = 0.
Proof.
  unfold aff_isZero, aff_eval. rewrite Bool.andb_true_iff, !N.eqb_eq.
  intros [-> ->]. lia.
Qed.

Lemma aff_eval_one (x : AffN) (k : N) : aff_isOne x = true -> aff_eval k x = 1.
Proof.
  unfold aff_isOne, aff_eval. rewrite Bool.andb_true_iff, !N.eqb_eq.
  intros [-> ->]. lia.
Qed.

Lemma aff_eval_add (x y : AffN) (k : N) :
  aff_eval k (aff_add x y) = aff_eval k x + aff_eval k y.
Proof. unfold aff_add, aff_eval; simpl. lia. Qed.

Lemma aff_eval_sub (x y z : AffN) (k : N) :
  aff_sub x y = Some z -> aff_eval k x = aff_eval k y + aff_eval k z.
Proof.
  unfold aff_sub, aff_eval.
  destruct (N.leb (fst y) (fst x) && N.leb (snd y) (snd x)) eqn:Ele; [| discriminate].
  injection 1 as <-. simpl.
  rewrite Bool.andb_true_iff, !N.leb_le in Ele. destruct Ele as [Ha Hb].
  nia.
Qed.

Definition pushAff (wid : N) (cnt : AffN) (stk : list AffRun) : option (list AffRun) :=
  if aff_isZero cnt then Some stk
  else match stk with
  | [] => if N.eqb wid 0 then Some [] else if aff_ge1 cnt then Some [(wid, cnt)] else None
  | (tw, tc) :: rest =>
    if negb (aff_ge1 cnt) then None
    else if N.eqb tw wid then Some ((tw, aff_add tc cnt) :: rest)
    else Some ((wid, cnt) :: stk)
  end.

Definition popAff (cnt : AffN) (stk : list AffRun) : option (N * list AffRun) :=
  match stk with
  | [] => if aff_isOne cnt then Some (0, []) else None
  | (tw, tc) :: rest =>
    match aff_sub tc cnt with
    | None => None
    | Some rem =>
      if aff_isZero rem then Some (tw, rest)
      else if aff_ge1 rem then Some (tw, (tw, rem) :: rest)
      else None
    end
  end.

Fixpoint evalAffSide (d : bool) (wOf : N -> list Sym) (k : N) (stk : list AffRun) : side :=
  match stk with
  | [] => const S0
  | (w, c) :: rest =>
    if d then npow (wOf w) (aff_eval k c) *> evalAffSide true wOf k rest
    else npow (rev (wOf w)) (aff_eval k c) *> evalAffSide false wOf k rest
  end.

Definition evalAffCfg (wOf : N -> list Sym) (k : N) (c : AffCfg) : Q * tape :=
  let '(q, d, l, r) := c in
  dirCfg q d (evalAffSide false wOf k l) (evalAffSide true wOf k r).

Lemma pushAff_sound (wOf : N -> list Sym) (Hz0 : wOf 0 = [S0; S0])
  (wid : N) (cnt : AffN) (stk stk' : list AffRun) (d : bool) (k : N) :
  pushAff wid cnt stk = Some stk' ->
  evalAffSide d wOf k stk' =
  (if d then npow (wOf wid) (aff_eval k cnt) *> evalAffSide true wOf k stk
   else npow (rev (wOf wid)) (aff_eval k cnt) *> evalAffSide false wOf k stk).
Proof.
  unfold pushAff. intro H.
  destruct (aff_isZero cnt) eqn:Ez.
  - injection H as <-. rewrite (aff_eval_zero cnt k Ez), !npow_0.
    destruct d; reflexivity.
  - destruct stk as [| [tw tc] rest].
    + destruct (N.eqb wid 0) eqn:Ew0.
      * apply N.eqb_eq in Ew0. subst wid. injection H as <-.
        destruct d; simpl; rewrite Hz0; simpl; rewrite npow_blank0; reflexivity.
      * destruct (aff_ge1 cnt); [| discriminate].
        injection H as <-. destruct d; reflexivity.
    + destruct (negb (aff_ge1 cnt)); [discriminate |].
      destruct (N.eqb tw wid) eqn:Etw.
      * apply N.eqb_eq in Etw. subst tw. injection H as <-.
        destruct d; simpl;
          rewrite aff_eval_add, N.add_comm, npow_add, Str_app_assoc; reflexivity.
      * injection H as <-. destruct d; reflexivity.
Qed.

Lemma popAff_sound (wOf : N -> list Sym) (Hz0 : wOf 0 = [S0; S0])
  (cnt : AffN) (stk stk' : list AffRun) (wid : N) (d : bool) (k : N) :
  popAff cnt stk = Some (wid, stk') ->
  wid = (match stk with [] => 0 | (w, _) :: _ => w end) /\
  evalAffSide d wOf k stk =
  (if d then npow (wOf wid) (aff_eval k cnt) *> evalAffSide true wOf k stk'
   else npow (rev (wOf wid)) (aff_eval k cnt) *> evalAffSide false wOf k stk').
Proof.
  destruct stk as [| [tw tc] rest]; simpl; intro H.
  - destruct (aff_isOne cnt) eqn:E1; [| discriminate].
    injection H as <- <-. split; [reflexivity |].
    rewrite (aff_eval_one cnt k E1), Hz0, !npow_1.
    destruct d; simpl; repeat rewrite <- const_unfold; reflexivity.
  - destruct (aff_sub tc cnt) as [rem | ] eqn:Esub; [| discriminate].
    pose proof (aff_eval_sub tc cnt rem k Esub) as Hsum.
    destruct (aff_isZero rem) eqn:Ez.
    + injection H as <- <-. split; [reflexivity |].
      rewrite (aff_eval_zero rem k Ez), N.add_0_r in Hsum.
      rewrite Hsum. destruct d; reflexivity.
    + destruct (aff_ge1 rem); [| discriminate].
      injection H as <- <-. split; [reflexivity |].
      destruct d; simpl; rewrite Hsum, npow_add, Str_app_assoc; reflexivity.
Qed.

Lemma cycle3_one (ul0 ur0 ur1 u1 : list Sym) (q q2 : Q)
  (Hex1 : WordExit ur0 q true u1 q true)
  (Hex2 : WordExit ur1 q true ur0 q2 false)
  (Hex3 : WordExit u1 q2 false ul0 q true)
  (l_rest r_rest : side) :
  l_rest {{q}}> (ur0 *> ur1 *> r_rest) -->*
  (rev ul0 *> l_rest) {{q}}> (ur0 *> r_rest).
Proof.
  pose proof (Hex1 l_rest (ur1 *> r_rest)) as H1; simpl in H1.
  pose proof (Hex2 (rev u1 *> l_rest) r_rest) as H2; simpl in H2.
  pose proof (Hex3 l_rest (ur0 *> r_rest)) as H3; simpl in H3.
  exact (etrans H1 (etrans H2 H3)).
Qed.

Lemma cycle3_many (ul0 ur0 ur1 u1 : list Sym) (q q2 : Q)
  (Hex1 : WordExit ur0 q true u1 q true)
  (Hex2 : WordExit ur1 q true ur0 q2 false)
  (Hex3 : WordExit u1 q2 false ul0 q true)
  (m : N) :
  forall (l_rest r_rest : side),
    l_rest {{q}}> (ur0 *> npow ur1 m *> r_rest) -->*
    (npow (rev ul0) m *> l_rest) {{q}}> (ur0 *> r_rest).
Proof.
  induction m as [| m IHm] using N_peano_ind; intros l_rest r_rest.
  - rewrite !npow_0. apply evstep_refl.
  - rewrite npow_succ_l, Str_app_assoc.
    eapply etrans; [exact (cycle3_one ul0 ur0 ur1 u1 q q2 Hex1 Hex2 Hex3 l_rest (npow ur1 m *> r_rest)) |].
    eapply etrans; [exact (IHm (rev ul0 *> l_rest) r_rest) |].
    rewrite <- Str_app_assoc, <- npow_succ_r. apply evstep_refl.
Qed.

Definition tryCycle3 (exits : ExitsTable) (c : AffCfg) : option AffCfg :=
  let '(q, d, l, r) := c in
  if negb d then None else
  match l, r with
  | (wl0, (la, lb)) :: l_tail, (wr0, (r0a, r0b)) :: (wr1, (ra, rb)) :: r_tail =>
    if negb (N.eqb r0a 0 && N.eqb r0b 1 && N.leb 1 ra && N.leb 2 rb && N.leb 1 lb) then None
    else
      match lookupExit exits wr0 q true with
      | Some (w1, q1, true) =>
        if negb (q_eqb q1 q && negb (N.eqb w1 wl0)) then None else
        match lookupExit exits wr1 q true with
        | Some (w2, q2, false) =>
          if negb (N.eqb w2 wr0) then None else
          match lookupExit exits w1 q2 false with
          | Some (w3, q3, true) =>
            if negb (q_eqb q3 q && N.eqb w3 wl0) then None else
            Some (q, true, (wl0, (la + ra, lb + (rb - 1))) :: l_tail,
                  (wr0, (0, 1)) :: (wr1, (0, 1)) :: r_tail)
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
  | _, _ => None
  end.

Lemma tryCycle3_sound (wOf : N -> list Sym) (exits : ExitsTable)
  (Hexs : ExitsSound wOf exits) (k : N) (c c' : AffCfg) :
  tryCycle3 exits c = Some c' ->
  evalAffCfg wOf k c -->* evalAffCfg wOf k c'.
Proof.
  destruct c as [[[q d] l] r]. unfold tryCycle3. intro H.
  destruct d; [| discriminate]. simpl in H.
  destruct l as [| [wl0 [la lb]] l_tail]; [discriminate |].
  destruct r as [| [wr0 [r0a r0b]] [| [wr1 [ra rb]] r_tail]]; try discriminate.
  destruct (negb (N.eqb r0a 0 && N.eqb r0b 1 && N.leb 1 ra && N.leb 2 rb && N.leb 1 lb)) eqn:Eg;
    [discriminate |].
  apply Bool.negb_false_iff in Eg.
  rewrite !Bool.andb_true_iff, !N.eqb_eq, !N.leb_le in Eg.
  destruct Eg as [[[[-> ->] Hra] Hrb] Hlb].
  destruct (lookupExit exits wr0 q true) as [[[w1 q1] [|]] | ] eqn:E1; try discriminate.
  destruct (negb (q_eqb q1 q && negb (N.eqb w1 wl0))) eqn:Eg1; [discriminate |].
  apply Bool.negb_false_iff in Eg1. rewrite Bool.andb_true_iff, q_eqb_eq in Eg1.
  destruct Eg1 as [-> _].
  destruct (lookupExit exits wr1 q true) as [[[w2 q2] [|]] | ] eqn:E2; try discriminate.
  destruct (negb (N.eqb w2 wr0)) eqn:Eg2; [discriminate |].
  apply Bool.negb_false_iff in Eg2. apply N.eqb_eq in Eg2. subst w2.
  destruct (lookupExit exits w1 q2 false) as [[[w3 q3] [|]] | ] eqn:E3; try discriminate.
  destruct (negb (q_eqb q3 q && N.eqb w3 wl0)) eqn:Eg3; [discriminate |].
  apply Bool.negb_false_iff in Eg3. rewrite Bool.andb_true_iff, q_eqb_eq, N.eqb_eq in Eg3.
  destruct Eg3 as [-> ->].
  injection H as <-.
  unfold evalAffCfg, evalAffSide, aff_eval; fold evalAffSide. simpl.
  rewrite !npow_1.
  set (m := ra * k + (rb - 1)).
  replace (ra * k + rb) with (m + 1) by (unfold m; lia).
  rewrite npow_succ_r, Str_app_assoc.
  eapply etrans.
  { exact (cycle3_many (wOf wl0) (wOf wr0) (wOf wr1) (wOf w1) q q2
      (Hexs _ _ _ _ _ _ E1) (Hexs _ _ _ _ _ _ E2) (Hexs _ _ _ _ _ _ E3) m
      (npow (rev (wOf wl0)) (la * k + lb) *> evalAffSide false wOf k l_tail)
      (wOf wr1 *> evalAffSide true wOf k r_tail)). }
  rewrite <- Str_app_assoc, <- npow_add.
  replace (m + (la * k + lb)) with ((la + ra) * k + (lb + (rb - 1))) by (unfold m; lia).
  apply evstep_refl.
Qed.

Definition stepAffUnclipped (exits : ExitsTable) (c : AffCfg) : option AffCfg :=
  match tryCycle3 exits c with
  | Some c' => Some c'
  | None =>
    let '(q, d, l, r) := c in
    let src := if d then r else l in
    let wid := match src with [] => 0 | (w, _) :: _ => w end in
    match lookupExit exits wid q d with
    | None => None
    | Some (wid', q', d') =>
      let same := q_eqb q' q && Bool.eqb d' d in
      let cnt_opt :=
        if same then match src with [] => None | (_, full) :: _ => Some full end
        else Some (0, 1) in
      match cnt_opt with
      | None => None
      | Some cnt =>
        if d then
          match popAff cnt r with
          | None => None
          | Some (_, r') =>
            if d' then match pushAff wid' cnt l with Some l2 => Some (q', true, l2, r') | None => None end
            else match pushAff wid' cnt r' with Some r2 => Some (q', false, l, r2) | None => None end
          end
        else
          match popAff cnt l with
          | None => None
          | Some (_, l') =>
            if d' then match pushAff wid' cnt l' with Some l2 => Some (q', true, l2, r) | None => None end
            else match pushAff wid' cnt r with Some r2 => Some (q', false, l', r2) | None => None end
          end
      end
    end
  end.

Lemma stepAffUnclipped_sound (wOf : N -> list Sym) (Hz0 : wOf 0 = [S0; S0])
  (exits : ExitsTable) (Hexs : ExitsSound wOf exits) (k : N) (c c' : AffCfg) :
  stepAffUnclipped exits c = Some c' ->
  evalAffCfg wOf k c -->* evalAffCfg wOf k c'.
Proof.
  unfold stepAffUnclipped. intro H.
  destruct (tryCycle3 exits c) as [cc | ] eqn:Ecyc.
  - injection H as <-. exact (tryCycle3_sound wOf exits Hexs k c cc Ecyc).
  - destruct c as [[[q [|]] l] r]; cbv beta iota zeta in H.
    + destruct (lookupExit exits (match r with [] => 0 | (w, _) :: _ => w end) q true)
        as [[[wid' q'] d'] | ] eqn:Elu; [| discriminate].
      pose proof (Hexs _ _ _ _ _ _ Elu) as Hex.
      cbv beta iota zeta in H.
      destruct (q_eqb q' q && Bool.eqb d' true) eqn:Esame; cbv beta iota zeta in H.
      * rewrite Bool.andb_true_iff, q_eqb_eq, Bool.eqb_true_iff in Esame.
        destruct Esame as [-> ->].
        destruct r as [| [rw full] r_rest]; cbv beta iota zeta in H; [discriminate |].
        destruct (popAff full ((rw, full) :: r_rest)) as [[pw r'] | ] eqn:Epop; [| discriminate].
        destruct (pushAff wid' full l) as [l2 | ] eqn:Epush; [| discriminate].
        injection H as <-.
        destruct (popAff_sound wOf Hz0 full ((rw, full) :: r_rest) r' pw true k Epop) as [Hpw HrEq].
        pose proof (pushAff_sound wOf Hz0 wid' full l l2 false k Epush) as Hl2.
        simpl in Hpw, Hex. subst pw.
        pose proof (sweepWord_sound _ _ _ _ Hex (aff_eval k full)
          (evalAffSide false wOf k l) (evalAffSide true wOf k r')) as Hsw.
        unfold enterCfg, exitCfg in Hsw. rewrite rev_npow in Hsw.
        unfold evalAffCfg, dirCfg. rewrite HrEq, Hl2. exact Hsw.
      * destruct (popAff (0, 1) r) as [[pw r'] | ] eqn:Epop; [| discriminate].
        destruct (popAff_sound wOf Hz0 (0, 1) r r' pw true k Epop) as [Hpw HrEq].
        subst pw.
        replace (aff_eval k (0, 1)) with 1 in HrEq by (unfold aff_eval; simpl; lia).
        rewrite npow_1 in HrEq.
        pose proof (Hex (evalAffSide false wOf k l) (evalAffSide true wOf k r')) as Hrun.
        unfold enterCfg, exitCfg in Hrun.
        destruct d'.
        -- destruct (pushAff wid' (0, 1) l) as [l2 | ] eqn:Epush; [| discriminate].
           injection H as <-.
           pose proof (pushAff_sound wOf Hz0 wid' (0, 1) l l2 false k Epush) as Hl2.
           replace (aff_eval k (0, 1)) with 1 in Hl2 by (unfold aff_eval; simpl; lia).
           rewrite npow_1 in Hl2.
           unfold evalAffCfg, dirCfg; rewrite HrEq, Hl2; exact Hrun.
        -- destruct (pushAff wid' (0, 1) r') as [r2 | ] eqn:Epush; [| discriminate].
           injection H as <-.
           pose proof (pushAff_sound wOf Hz0 wid' (0, 1) r' r2 true k Epush) as Hr2.
           replace (aff_eval k (0, 1)) with 1 in Hr2 by (unfold aff_eval; simpl; lia).
           rewrite npow_1 in Hr2.
           unfold evalAffCfg, dirCfg; rewrite HrEq, Hr2; exact Hrun.
    + destruct (lookupExit exits (match l with [] => 0 | (w, _) :: _ => w end) q false)
        as [[[wid' q'] d'] | ] eqn:Elu; [| discriminate].
      pose proof (Hexs _ _ _ _ _ _ Elu) as Hex.
      cbv beta iota zeta in H.
      destruct (q_eqb q' q && Bool.eqb d' false) eqn:Esame; cbv beta iota zeta in H.
      * rewrite Bool.andb_true_iff, q_eqb_eq, Bool.eqb_true_iff in Esame.
        destruct Esame as [-> ->].
        destruct l as [| [lw full] l_rest]; cbv beta iota zeta in H; [discriminate |].
        destruct (popAff full ((lw, full) :: l_rest)) as [[pw l'] | ] eqn:Epop; [| discriminate].
        destruct (pushAff wid' full r) as [r2 | ] eqn:Epush; [| discriminate].
        injection H as <-.
        destruct (popAff_sound wOf Hz0 full ((lw, full) :: l_rest) l' pw false k Epop) as [Hpw HlEq].
        pose proof (pushAff_sound wOf Hz0 wid' full r r2 true k Epush) as Hr2.
        simpl in Hpw, Hex. subst pw.
        pose proof (sweepWord_sound _ _ _ _ Hex (aff_eval k full)
          (evalAffSide false wOf k l') (evalAffSide true wOf k r)) as Hsw.
        unfold enterCfg, exitCfg in Hsw. rewrite rev_npow in Hsw.
        unfold evalAffCfg, dirCfg. rewrite HlEq, Hr2. exact Hsw.
      * destruct (popAff (0, 1) l) as [[pw l'] | ] eqn:Epop; [| discriminate].
        destruct (popAff_sound wOf Hz0 (0, 1) l l' pw false k Epop) as [Hpw HlEq].
        subst pw.
        replace (aff_eval k (0, 1)) with 1 in HlEq by (unfold aff_eval; simpl; lia).
        rewrite npow_1 in HlEq.
        pose proof (Hex (evalAffSide false wOf k l') (evalAffSide true wOf k r)) as Hrun.
        unfold enterCfg, exitCfg in Hrun.
        destruct d'.
        -- destruct (pushAff wid' (0, 1) l') as [l2 | ] eqn:Epush; [| discriminate].
           injection H as <-.
           pose proof (pushAff_sound wOf Hz0 wid' (0, 1) l' l2 false k Epush) as Hl2.
           replace (aff_eval k (0, 1)) with 1 in Hl2 by (unfold aff_eval; simpl; lia).
           rewrite npow_1 in Hl2.
           unfold evalAffCfg, dirCfg; rewrite HlEq, Hl2; exact Hrun.
        -- destruct (pushAff wid' (0, 1) r) as [r2 | ] eqn:Epush; [| discriminate].
           injection H as <-.
           pose proof (pushAff_sound wOf Hz0 wid' (0, 1) r r2 true k Epush) as Hr2.
           replace (aff_eval k (0, 1)) with 1 in Hr2 by (unfold aff_eval; simpl; lia).
           rewrite npow_1 in Hr2.
           unfold evalAffCfg, dirCfg; rewrite HlEq, Hr2; exact Hrun.
Qed.

Notation stepAffOpt exits :=
  (fun x : option AffCfg => match x with Some y => stepAffUnclipped exits y | None => None end).

(* ========================================================================== *)
(* Section 6: Canonical Family, Bridges, Dynamic Builder, and Non-Halting     *)
(* ========================================================================== *)

Definition b2_to_wid (s : B2) : N :=
  match s with BZ => 0 | BY => 1 | BX => 2 | BW => 3 end.

Fixpoint pushAffConstRuns (xs : list (B2 * N)) (stk : list AffRun) : list AffRun :=
  match xs with
  | [] => stk
  | (s, n) :: rest =>
    match pushAff (b2_to_wid s) (0, n) stk with
    | Some stk' => pushAffConstRuns rest stk'
    | None => stk
    end
  end.

Definition iL : list AffRun :=
  let s1 := pushAffConstRuns uRuns [] in
  let s2 := match pushAff 4 (1, 8) s1 with Some s => s | None => s1 end in
  let s3 := pushAffConstRuns vRuns s2 in
  let s4 := match pushAff 5 (1, 8) s3 with Some s => s | None => s3 end in
  pushAffConstRuns wRuns s4.

Definition initReturnCfg : AffCfg := (B, true, iL, [(1, (0, 6))]).

Definition familyCfg (k : N) : Q * tape :=
  evalAffCfg seedWord k initReturnCfg.

(* Flattening helpers for Bridge 1 & Bridge 2 *)
Fixpoint flatEntryLeft (xs : list (B2 * N)) : list Sym :=
  match xs with
  | [] => []
  | (s, c) :: rest => npow (rev (b2Word s)) c ++ flatEntryLeft rest
  end.

Lemma evalSide_false_eq_flat (xs : list (B2 * N)) :
  evalSide false xs = flatEntryLeft xs *> const S0.
Proof.
  induction xs as [| [s c] rest IH]; simpl; [reflexivity | rewrite IH, Str_app_assoc; reflexivity].
Qed.

Lemma flatEntryLeft_app (xs ys : list (B2 * N)) :
  flatEntryLeft (xs ++ ys) = flatEntryLeft xs ++ flatEntryLeft ys.
Proof.
  induction xs as [| [s c] rest IH]; simpl; [reflexivity | rewrite IH, app_assoc; reflexivity].
Qed.

Fixpoint flatAffLeft (wOf : N -> list Sym) (k : N) (xs : list AffRun) : list Sym :=
  match xs with
  | [] => []
  | (w, c) :: rest => npow (rev (wOf w)) (aff_eval k c) ++ flatAffLeft wOf k rest
  end.

Lemma evalAffSide_false_eq_flat (wOf : N -> list Sym) (k : N) (xs : list AffRun) :
  evalAffSide false wOf k xs = flatAffLeft wOf k xs *> const S0.
Proof.
  induction xs as [| [w c] rest IH]; simpl; [reflexivity | rewrite IH, Str_app_assoc; reflexivity].
Qed.

Lemma flatAffLeft_app (wOf : N -> list Sym) (k : N) (xs ys : list AffRun) :
  flatAffLeft wOf k (xs ++ ys) = flatAffLeft wOf k xs ++ flatAffLeft wOf k ys.
Proof.
  induction xs as [| [w c] rest IH]; simpl; [reflexivity | rewrite IH, app_assoc; reflexivity].
Qed.

Fixpoint affRuns_eqb (xs ys : list AffRun) : bool :=
  match xs, ys with
  | [], [] => true
  | (w1, (a1, b1)) :: r1, (w2, (a2, b2)) :: r2 =>
    N.eqb w1 w2 && N.eqb a1 a2 && N.eqb b1 b2 && affRuns_eqb r1 r2
  | _, _ => false
  end.

Lemma affRuns_eqb_eq (xs ys : list AffRun) : affRuns_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys.
  induction xs as [| [w1 [a1 b1]] r1 IH]; intros [| [w2 [a2 b2]] r2]; simpl.
  - split; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - rewrite !Bool.andb_true_iff, !N.eqb_eq, IH.
    split; [intros [[[-> ->] ->] ->]; reflexivity | intro H; injection H as -> -> -> ->; auto].
Qed.

Fixpoint all_le5 (xs : list AffRun) : bool :=
  match xs with
  | [] => true
  | (w, _) :: rest => N.leb w 5 && all_le5 rest
  end.

Lemma evalAffSide_voc_seed (voc : NTrie (list B2)) (Hseed : checkSeedVocab voc = true)
  (d : bool) (k : N) :
  forall xs : list AffRun,
    all_le5 xs = true ->
    evalAffSide d (vocWord voc) k xs = evalAffSide d seedWord k xs.
Proof.
  destruct d;
    (induction xs as [| [w c] rest IH]; simpl; [reflexivity |
     rewrite Bool.andb_true_iff, N.leb_le; intros [Hw Hrest];
     rewrite (checkSeedVocab_le5 voc w Hseed Hw), (IH Hrest); reflexivity]).
Qed.

Fixpoint const_a0_ok (xs : list AffRun) : bool :=
  match xs with
  | [] => true
  | (_, (a, _)) :: rest => N.eqb a 0 && const_a0_ok rest
  end.

Lemma flatAffLeft_const (wOf : N -> list Sym) (k : N) :
  forall xs : list AffRun,
    const_a0_ok xs = true ->
    flatAffLeft wOf k xs = flatAffLeft wOf 0 xs.
Proof.
  induction xs as [| [w [a b]] rest IH]; simpl; [reflexivity |].
  rewrite Bool.andb_true_iff, N.eqb_eq. intros [-> Hrest].
  unfold aff_eval; simpl. rewrite (IH Hrest). reflexivity.
Qed.

Fixpoint const_seed_ok (xs : list AffRun) : bool :=
  match xs with
  | [] => true
  | (w, (a, _)) :: rest => N.leb w 5 && N.eqb a 0 && const_seed_ok rest
  end.

Lemma flatAffLeft_const_seed (voc : NTrie (list B2)) (Hseed : checkSeedVocab voc = true)
  (k1 k2 : N) :
  forall xs : list AffRun,
    const_seed_ok xs = true ->
    flatAffLeft (vocWord voc) k1 xs = flatAffLeft seedWord k2 xs.
Proof.
  induction xs as [| [w [a b]] rest IH]; simpl; [reflexivity |].
  rewrite !Bool.andb_true_iff, N.leb_le, N.eqb_eq. intros [[Hw ->] Hrest].
  rewrite (checkSeedVocab_le5 voc w Hseed Hw), (IH Hrest).
  unfold aff_eval; simpl. reflexivity.
Qed.

(* Bridge 1: evalEntryCfg entryMilestone8 = familyCfg 0 *)
Opaque npow.

Lemma e8L_decomp :
  runs_eqb e8L (firstn 85 e8L ++ [(BX, 791761176)] ++ skipn 86 e8L) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma iL_decomp :
  affRuns_eqb iL (firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL) ++
                  [(2, (0, 791761176)); (4, (1, 8))] ++ skipn 16 iL) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge1_head :
  list_sym_eqb (flatEntryLeft (firstn 85 e8L))
    (flatAffLeft seedWord 0 (firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL))) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bridge1_tail :
  list_sym_eqb (flatEntryLeft (skipn 86 e8L))
    (flatAffLeft seedWord 0 ([(4, (1, 8))] ++ skipn 16 iL)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma entryMilestone8_eq : evalEntryCfg entryMilestone8 = familyCfg 0.
Proof.
  assert (He8 : e8L = firstn 85 e8L ++ [(BX, 791761176)] ++ skipn 86 e8L) by
    (apply runs_eqb_eq, e8L_decomp).
  assert (Hi : iL = firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL) ++
                    [(2, (0, 791761176)); (4, (1, 8))] ++ skipn 16 iL) by
    (apply affRuns_eqb_eq, iL_decomp).
  assert (Hh : flatEntryLeft (firstn 85 e8L) =
               flatAffLeft seedWord 0 (firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL))) by
    (apply list_sym_eqb_eq, bridge1_head).
  assert (Ht : flatEntryLeft (skipn 86 e8L) =
               flatAffLeft seedWord 0 ([(4, (1, 8))] ++ skipn 16 iL)) by
    (apply list_sym_eqb_eq, bridge1_tail).
  unfold entryMilestone8, evalEntryCfg, familyCfg, initReturnCfg, evalAffCfg.
  apply (f_equal2 (dirCfg B true)); [| reflexivity].
  rewrite evalSide_false_eq_flat, evalAffSide_false_eq_flat.
  apply (f_equal (fun u => u *> const S0)).
  rewrite He8, Hi.
  change (firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL) ++
          [(2, (0, 791761176)); (4, (1, 8))] ++ skipn 16 iL) with
    ((firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL)) ++
     [(2, (0, 791761176))] ++
     ([(4, (1, 8))] ++ skipn 16 iL)).
  rewrite (flatEntryLeft_app (firstn 85 e8L)), (flatEntryLeft_app [(BX, 791761176)]).
  rewrite (flatAffLeft_app seedWord 0 (firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL))),
          (flatAffLeft_app seedWord 0 [(2, (0, 791761176))]).
  apply f_equal2; [exact Hh |].
  apply f_equal2; [| exact Ht].
  simpl flatEntryLeft. simpl flatAffLeft. rewrite !app_nil_r.
  apply f_equal2; [reflexivity | reflexivity].
Qed.

Lemma entry_to_family0 : c0 -->* familyCfg 0.
Proof. rewrite <- entryMilestone8_eq. exact entry_to_c8. Qed.

(* Untrusted dynamic builder + single-pass verified replay & Bridge 2 *)
Definition BuildState := (N * NTrie (list B2) * WordTrie * ExitsTable * AffCfg)%type.

Definition getOrBuildExit (nextId : N) (vocab : NTrie (list B2)) (wt : WordTrie) (exits : ExitsTable)
  (wid : N) (q : Q) (d : bool) : option (N * NTrie (list B2) * WordTrie * ExitsTable * CompExit) :=
  match lookupExit exits wid q d with
  | Some ex => Some (nextId, vocab, wt, exits, ex)
  | None =>
    match nt_find vocab wid with
    | None => None
    | Some u =>
      match runCompositeExit u q d with
      | None => None
      | Some (v, q', d') =>
        let '(nextId', vocab', wt', wid') :=
          match wt_find wt v with
          | Some id => (nextId, vocab, wt, id)
          | None => (nextId + 1, nt_ins vocab nextId v, wt_ins wt v nextId, nextId)
          end in
        let ex := (wid', q', d') in
        Some (nextId', vocab', wt', insertExit exits wid q d ex, ex)
      end
    end
  end.

Definition buildStep (st : option BuildState) : option BuildState :=
  match st with
  | None => None
  | Some (nid, voc, wt, exs, c) =>
    let '(q, d, l, r) := c in
    let '(nid1, voc1, wt1, exs1) :=
      if d then
        match l, r with
        | (wl0, _) :: _, (wr0, (r0a, r0b)) :: (wr1, (ra, rb)) :: _ =>
          if N.eqb r0a 0 && N.eqb r0b 1 && N.leb 1 ra && N.leb 2 rb then
            match getOrBuildExit nid voc wt exs wr0 q true with
            | Some (nA, vA, wA, eA, (w1, q1, true)) =>
              match getOrBuildExit nA vA wA eA wr1 q true with
              | Some (nB, vB, wB, eB, (_, q2, false)) =>
                match getOrBuildExit nB vB wB eB w1 q2 false with
                | Some (nC, vC, wC, eC, _) => (nC, vC, wC, eC)
                | None => (nB, vB, wB, eB)
                end
              | _ => (nA, vA, wA, eA)
              end
            | _ => (nid, voc, wt, exs)
            end
          else (nid, voc, wt, exs)
        | _, _ => (nid, voc, wt, exs)
        end
      else (nid, voc, wt, exs) in
    match tryCycle3 exs1 c with
    | Some c' => Some (nid1, voc1, wt1, exs1, c')
    | None =>
      let src := if d then r else l in
      let wid := match src with [] => 0 | (w, _) :: _ => w end in
      match getOrBuildExit nid1 voc1 wt1 exs1 wid q d with
      | None => None
      | Some (nid2, voc2, wt2, exs2, _) =>
        match stepAffUnclipped exs2 c with
        | Some c' => Some (nid2, voc2, wt2, exs2, c')
        | None => None
        end
      end
    end
  end.

Definition initBuildState : BuildState :=
  let seeds := [(0, [BZ]); (1, [BY]); (2, [BX]); (3, [BW]); (4, pWordB2); (5, qWordB2)] in
  let voc := fold_left (fun acc '(i, w) => nt_ins acc i w) seeds nt_empty in
  let wt := fold_left (fun acc '(i, w) => wt_ins acc w i) seeds WTLeaf in
  (6, voc, wt, nt_empty, initReturnCfg).

Definition qARev : list Sym := npow (rev (seedWord 2)) 32.
Definition pBRev : list Sym := rev (seedWord 0) ++ npow (rev (seedWord 1)) 5.
Definition pARev : list Sym := npow (rev (seedWord 1)) 5 ++ npow (rev (seedWord 2)) 8.

Definition checkFinalBridge (voc : NTrie (list B2)) (lf : list AffRun) : bool :=
  let wOf := vocWord voc in
  let pre := firstn 5 lf in
  let qb := firstn 9 (skipn 5 lf) in
  match skipn 14 lf with
  | (wq, (wqa, wqb)) :: (wx32, (wx32a, wx32b)) :: rest16 =>
    if negb (N.eqb wqa 1 && N.eqb wqb 8 && N.eqb wx32 2 &&
             N.eqb wx32a 0 && N.eqb wx32b 32) then false
    else
      let mid := firstn 8 rest16 in
      match skipn 8 rest16 with
      | (wxBig, (wxBiga, wxBigb)) :: (wx1, (wx1a, wx1b)) ::
        (wx2, (wx2a, wx2b)) :: (wp, (wpa, wpb)) :: rest28 =>
        if negb (N.eqb wxBig 2 && N.eqb wxBiga 0 && N.eqb wxBigb 791761144 &&
                 N.eqb wx1a 0 && N.eqb wx1b 1 && N.eqb wx2a 0 && N.eqb wx2b 1 &&
                 N.eqb wpa 1 && N.eqb wpb 6) then false
        else
          let pt := firstn 8 rest28 in
          let suf := skipn 8 rest28 in
          let qBRev := flatAffLeft wOf 0 qb in
          affRuns_eqb lf (pre ++ qb ++ [(wq, (1, 8)); (2, (0, 32))] ++ mid ++
                          [(2, (0, 791761144)); (wx1, (0, 1)); (wx2, (0, 1)); (wp, (1, 6))] ++
                          pt ++ suf) &&
          const_seed_ok pre && affRuns_eqb pre (firstn 5 iL) &&
          const_seed_ok mid && affRuns_eqb mid (firstn 8 (skipn 6 iL)) &&
          const_seed_ok suf && affRuns_eqb suf (skipn 16 iL) &&
          const_a0_ok qb && const_a0_ok pt &&
          list_sym_eqb (rev (wOf wq)) (qARev ++ qBRev) &&
          list_sym_eqb (rev (seedWord 5)) (qBRev ++ qARev) &&
          list_sym_eqb (rev (wOf wx1) ++ rev (wOf wx2)) (npow (rev (seedWord 2)) 32 ++ pBRev) &&
          list_sym_eqb (rev (wOf wp)) (pARev ++ pBRev) &&
          list_sym_eqb (rev (seedWord 4)) (pBRev ++ pARev) &&
          list_sym_eqb (flatAffLeft wOf 0 pt) (pARev ++ npow (rev (seedWord 4)) 2)
      | _ => false
      end
  | _ => false
  end.

Lemma aff_eval_0 (k b : N) : aff_eval k (0, b) = b.
Proof. unfold aff_eval; cbn [fst snd]. lia. Qed.

Lemma aff_eval_1 (k b : N) : aff_eval k (1, b) = k + b.
Proof. unfold aff_eval; cbn [fst snd]. lia. Qed.

Lemma q_chunk_lemma (x2 wq_r qB q5 : list Sym) (k : N) :
  wq_r = npow x2 32 ++ qB ->
  q5 = qB ++ npow x2 32 ->
  qB ++ (npow wq_r (k + 8) ++ (npow x2 32 ++ [])) = npow q5 (k + 1 + 8) ++ [].
Proof.
  intros -> ->. rewrite !app_nil_r.
  replace (k + 1 + 8) with ((k + 8) + 1) by lia.
  rewrite npow_rot, app_assoc, <- npow_succ_l. reflexivity.
Qed.

Lemma xp_chunk_lemma (x2 wx1_r wx2_r wp_r pt_f pA pB p4 : list Sym) (k : N) :
  wx1_r ++ wx2_r = npow x2 32 ++ pB ->
  wp_r = pA ++ pB ->
  p4 = pB ++ pA ->
  pt_f = pA ++ npow p4 2 ->
  (npow x2 791761144 ++ (wx1_r ++ (wx2_r ++ (npow wp_r (k + 6) ++ [])))) ++ pt_f =
  npow x2 791761176 ++ (npow p4 (k + 1 + 8) ++ []).
Proof.
  intros Hwx12 -> Hp4 ->. rewrite !app_nil_r.
  replace (npow x2 791761144 ++ (wx1_r ++ (wx2_r ++ npow (pA ++ pB) (k + 6))))
    with ((npow x2 791761144 ++ (wx1_r ++ wx2_r)) ++ npow (pA ++ pB) (k + 6))
    by (rewrite <- !app_assoc; reflexivity).
  rewrite Hwx12.
  replace (((npow x2 791761144 ++ (npow x2 32 ++ pB)) ++ npow (pA ++ pB) (k + 6)) ++ (pA ++ npow p4 2))
    with ((npow x2 791761144 ++ npow x2 32) ++ (pB ++ (npow (pA ++ pB) (k + 6) ++ pA) ++ npow p4 2))
    by (rewrite <- !app_assoc; reflexivity).
  rewrite <- npow_add. change (791761144 + 32) with 791761176.
  apply f_equal2; [reflexivity |].
  rewrite npow_rot.
  replace (pB ++ (pA ++ npow (pB ++ pA) (k + 6)) ++ npow p4 2)
    with (((pB ++ pA) ++ npow (pB ++ pA) (k + 6)) ++ npow p4 2)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite <- Hp4, <- npow_succ_l, <- npow_add.
  apply f_equal2; [reflexivity | lia].
Qed.

Lemma bridge2_stitch {X : Type}
  (a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 : list X) :
  a1 = b1 ->
  a2 ++ a3 = b2 ->
  a4 = b3 ->
  a5 ++ a6 = b4 ->
  a7 = b5 ->
  a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 = b1 ++ b2 ++ b3 ++ b4 ++ b5.
Proof. intros -> <- -> <- ->. rewrite <- !app_assoc. reflexivity. Qed.

Lemma final_bridge_sound (voc : NTrie (list B2)) (lf : list AffRun) (k : N) :
  checkSeedVocab voc = true ->
  checkFinalBridge voc lf = true ->
  evalAffCfg (vocWord voc) k (B, true, lf, [(1, (0, 6))]) = familyCfg (k + 1).
Proof.
  intros Hseed Hbr.
  unfold checkFinalBridge in Hbr.
  set (wOf := vocWord voc) in *.
  set (pre := firstn 5 lf) in *.
  set (qb := firstn 9 (skipn 5 lf)) in *.
  destruct (skipn 14 lf) as [| [wq [wqa wqb]] [| [wx32 [wx32a wx32b]] rest16]]; try discriminate.
  destruct (negb (N.eqb wqa 1 && N.eqb wqb 8 && N.eqb wx32 2 &&
                  N.eqb wx32a 0 && N.eqb wx32b 32)) eqn:Eg1; [discriminate |].
  set (mid := firstn 8 rest16) in *.
  destruct (skipn 8 rest16) as
    [| [wxBig [wxBiga wxBigb]] [| [wx1 [wx1a wx1b]]
    [| [wx2 [wx2a wx2b]] [| [wp [wpa wpb]] rest28]]]]; try discriminate.
  destruct (negb (N.eqb wxBig 2 && N.eqb wxBiga 0 && N.eqb wxBigb 791761144 &&
                  N.eqb wx1a 0 && N.eqb wx1b 1 && N.eqb wx2a 0 && N.eqb wx2b 1 &&
                  N.eqb wpa 1 && N.eqb wpb 6)) eqn:Eg2; [discriminate |].
  set (pt := firstn 8 rest28) in *.
  set (suf := skipn 8 rest28) in *.
  set (qBRev := flatAffLeft wOf 0 qb) in *.
  rewrite !Bool.andb_true_iff, !affRuns_eqb_eq, !list_sym_eqb_eq in Hbr.
  destruct Hbr as [[[[[[[[[[[[[[Hlf HpreC] HpreEq] HmidC] HmidEq] HsufC] HsufEq]
    HqbC] HptC] Hwq] Hq5] Hwx12] Hwp] Hp4] Hpt].
  assert (Hi : iL = firstn 5 iL ++ [(5, (1, 8))] ++ firstn 8 (skipn 6 iL) ++
                    [(2, (0, 791761176)); (4, (1, 8))] ++ skipn 16 iL) by
    (apply affRuns_eqb_eq, iL_decomp).
  assert (Hw1 : wOf 1 = seedWord 1) by (apply checkSeedVocab_le5; [exact Hseed | clear; lia]).
  assert (Hw2 : wOf 2 = seedWord 2) by (apply checkSeedVocab_le5; [exact Hseed | clear; lia]).
  unfold familyCfg, initReturnCfg, evalAffCfg.
  apply (f_equal2 (dirCfg B true)); [| simpl; rewrite Hw1, !aff_eval_0; reflexivity].
  rewrite !evalAffSide_false_eq_flat.
  apply (f_equal (fun u => u *> const S0)).
  rewrite Hlf, Hi.
  repeat rewrite flatAffLeft_app.
  assert (Hpre : flatAffLeft wOf k pre = flatAffLeft seedWord (k + 1) (firstn 5 iL)).
  { rewrite <- HpreEq. exact (flatAffLeft_const_seed voc Hseed k (k + 1) pre HpreC). }
  assert (Hmid : flatAffLeft wOf k mid = flatAffLeft seedWord (k + 1) (firstn 8 (skipn 6 iL))).
  { rewrite <- HmidEq. exact (flatAffLeft_const_seed voc Hseed k (k + 1) mid HmidC). }
  assert (Hsuf : flatAffLeft wOf k suf = flatAffLeft seedWord (k + 1) (skipn 16 iL)).
  { rewrite <- HsufEq. exact (flatAffLeft_const_seed voc Hseed k (k + 1) suf HsufC). }
  assert (HqChunk : flatAffLeft wOf k qb ++ flatAffLeft wOf k [(wq, (1, 8)); (2, (0, 32))] =
                    flatAffLeft seedWord (k + 1) [(5, (1, 8))]).
  { rewrite (flatAffLeft_const wOf k qb HqbC). fold qBRev.
    simpl flatAffLeft. rewrite !aff_eval_1, !aff_eval_0, Hw2.
    exact (q_chunk_lemma (rev (seedWord 2)) (rev (wOf wq)) qBRev (rev (seedWord 5)) k Hwq Hq5). }
  assert (HxpChunk :
    flatAffLeft wOf k [(2, (0, 791761144)); (wx1, (0, 1)); (wx2, (0, 1)); (wp, (1, 6))] ++
    flatAffLeft wOf k pt =
    flatAffLeft seedWord (k + 1) [(2, (0, 791761176)); (4, (1, 8))]).
  { rewrite (flatAffLeft_const wOf k pt HptC).
    simpl flatAffLeft. rewrite !aff_eval_0, !aff_eval_1, !npow_1, Hw2.
    exact (xp_chunk_lemma (rev (seedWord 2)) (rev (wOf wx1)) (rev (wOf wx2)) (rev (wOf wp))
      (flatAffLeft wOf 0 pt) pARev pBRev (rev (seedWord 4)) k Hwx12 Hwp Hp4 Hpt). }
  exact (bridge2_stitch _ _ _ _ _ _ _ _ _ _ _ _ Hpre HqChunk Hmid HxpChunk Hsuf).
Qed.

Lemma step_BY_progress (l r : side) :
  l {{B}}> ([S0; S1] *> r) -->+ (rev [S1; S0] *> l) {{B}}> r.
Proof.
  eapply progress_step; [eapply step_right; reflexivity |].
  apply progress_base; eapply step_right; reflexivity.
Qed.

Lemma init_all_le5 : all_le5 iL = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition checkReplayEnd (voc : NTrie (list B2)) (o : option AffCfg) : bool :=
  match o with
  | None => false
  | Some (qp, dp, lp, rp) =>
    if q_eqb qp B && dp then
      match rp with
      | [(wr, (ra, rb))] =>
        if N.eqb wr 1 && N.eqb ra 0 && N.eqb rb 7 then
          match pushAff 2 (0, 1) lp with
          | Some lf => checkFinalBridge voc lf
          | None => false
          end
        else false
      | _ => false
      end
    else false
  end.

Definition checkBuildAndReplay (p : positive) (o : option BuildState) : bool :=
  match o with
  | None => false
  | Some (_, voc, _, exs, _) =>
    checkSeedVocab voc &&
    checkAllExits voc exs &&
    checkReplayEnd voc (Pos.iter (stepAffOpt exs) (Some initReturnCfg) p)
  end.

Lemma return_all_ok :
  checkBuildAndReplay 9508%positive (Pos.iter buildStep (Some initBuildState) 9508%positive) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Opaque iL pWordB2 qWordB2 initBuildState buildStep checkFinalBridge.

Lemma family_step_gen (p : positive) (o : option BuildState) (k : N) :
  checkBuildAndReplay p o = true -> familyCfg k -->+ familyCfg (k + 1).
Proof.
  intro Hok.
  destruct o as [[[[[nid voc] wt] exs] c_end] | ]; [| discriminate Hok].
  cbn [checkBuildAndReplay] in Hok.
  rewrite !Bool.andb_true_iff in Hok. destruct Hok as [[Hseed Hexs] Hrep].
  destruct (Pos.iter (stepAffOpt exs) (Some initReturnCfg) p)
    as [[[[qp dp] lp] rp] | ] eqn:Eiter; [| discriminate Hrep].
  cbn [checkReplayEnd] in Hrep.
  destruct (q_eqb qp B && dp) eqn:Eqd; [| discriminate Hrep].
  rewrite Bool.andb_true_iff, q_eqb_eq in Eqd. destruct Eqd as [-> ->].
  destruct rp as [| [wr [ra rb]] [| ? ?]]; try discriminate Hrep.
  destruct (N.eqb wr 1 && N.eqb ra 0 && N.eqb rb 7) eqn:Erp; [| discriminate Hrep].
  rewrite !Bool.andb_true_iff, !N.eqb_eq in Erp. destruct Erp as [[-> ->] ->].
  destruct (pushAff 2 (0, 1) lp) as [lf | ] eqn:Epush; [| discriminate Hrep].
  assert (Hz0 : vocWord voc 0 = [S0; S0]) by
    (apply checkSeedVocab_le5; [exact Hseed | clear; lia]).
  pose proof (checkAllExits_sound voc exs Hexs) as HsoundExs.
  pose proof (pos_iter_sound (evalAffCfg (vocWord voc) k) (stepAffUnclipped exs)
    (stepAffUnclipped_sound (vocWord voc) Hz0 exs HsoundExs k)
    p initReturnCfg (B, true, lp, [(1, (0, 7))]) Eiter) as Hpre.
  assert (HinitEq : evalAffCfg (vocWord voc) k initReturnCfg = familyCfg k).
  { unfold familyCfg, initReturnCfg, evalAffCfg.
    apply (f_equal2 (dirCfg B true)).
    - exact (evalAffSide_voc_seed voc Hseed false k iL init_all_le5).
    - exact (evalAffSide_voc_seed voc Hseed true k [(1, (0, 6))] (eq_refl true)). }
  destruct HinitEq.
  eapply ep_trans; [exact Hpre |].
  destruct (final_bridge_sound voc lf k Hseed Hrep).
  pose proof (pushAff_sound (vocWord voc) Hz0 2 (0, 1) lp lf false k Epush) as Hlf.
  assert (Hw1 : vocWord voc 1 = [S0; S1]) by
    (rewrite (checkSeedVocab_le5 voc 1 Hseed); [reflexivity | clear; lia]).
  assert (Hw2 : vocWord voc 2 = [S1; S0]) by
    (rewrite (checkSeedVocab_le5 voc 2 Hseed); [reflexivity | clear; lia]).
  unfold evalAffCfg, dirCfg. cbn [evalAffSide].
  rewrite Hlf, Hw1, Hw2, !aff_eval_0.
  change 7 with (6 + 1).
  rewrite npow_1, npow_succ_l, Str_app_assoc.
  apply step_BY_progress.
Qed.

Lemma family_step (k : N) : familyCfg k -->+ familyCfg (k + 1).
Proof. exact (family_step_gen 9508%positive _ k return_all_ok). Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact entry_to_family0.
  - apply (progress_nonhalt_simple tm N familyCfg 0%N).
    intro k. exists (k + 1)%N. exact (family_step k).
Qed.
