(* 1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA--- never halts.
   Skelet 1-like Class 2: a ternary counter on phase defects (a left word counting to 81,
   a chain of K digit blocks, and a right region of fossils and two growing blocks X and Y).
   Outer shape adapted from verify/SBCv6.v, Module TM21 (macro rules on a digit list, one
   invariant, a closure lemma); the verified accelerated simulator follows the idea of
   verify/Sk1like_TC_v1.v. Structure of the proof:
   - a symbolic run-length simulator whose run lengths are linear forms c + sum v_i x_i over N,
     sound for every valuation of the x_i and of abstract tape sides (sstep_spec, reach_spec);
   - the 18 single-block runs of the chain with every gap symbolic, and the chain visit
     (Lemmas C and C') by induction on the block list (visit3_spec, cb_spec, vis_spec);
   - the left word: its 81 episodes, the last one being the left record (lw_ep);
   - Lemma T: the visits of one record interval as a computation on block labels, for every
     chain length (interval): exit phase c_K + 2 for (3^(K+1)-5)/2 visits, then c_K;
   - the right region: a verified symbolic executor for interval programs with 4-cycle jumps
     (exec_spec, jump_lemma), and the six interval programs, u = 1 + 8 t (int_r5 .. int_r4);
   - the regrouping after the record visit (regroup) and the six record-exit episodes;
   - Lemma S for the six classes (S_r5 .. S_r4), the invariant Inv and its closure (inv_step);
   - the base case: c0 -->* record exit 28 (2,629,088,227,408 machine steps, 18,571,896
     simulator steps in 38 native_compute pieces), then into the invariant (class r5, e = 2,
     u = 1).
   Informal proof: the accompanying write-up.
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context *)

From BusyCoq Require Import Individual62.
Require Import Lia ZifyNat String List Arith NArith ZArith.
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope nat_scope.

(* ===================================================================== *)
(* A symbolic run-length simulator.                                      *)
(* The tape is cut into alternating runs.  A run is a first symbol and a *)
(* length; a length is a linear form c + sum v_i x_i over N.  A side is  *)
(* a list of runs (nearest the head first) followed by either the blank  *)
(* stream or an abstract side.  The simulator crosses a whole run in one *)
(* step when the head state is in one of the two sweep cycles.           *)
(* ===================================================================== *)

Definition sneg (s : Sym) : Sym := match s with S0 => S1 | S1 => S0 end.
Definition seqb (a b : Sym) : bool :=
  match a, b with S0, S0 | S1, S1 => true | _, _ => false end.

Record lf := LF { lc : N; lv : list N }.

Fixpoint dot (vs nu : list N) : N :=
  match vs, nu with
  | v :: vs', x :: nu' => (v * x + dot vs' nu')%N
  | _, _ => 0%N
  end.

Definition ev (nu : list N) (a : lf) : nat := N.to_nat (lc a + dot (lv a) nu).

Fixpoint zadd (a b : list N) : list N :=
  match a, b with
  | x :: a', y :: b' => (x + y)%N :: zadd a' b'
  | [], _ => b
  | _, [] => a
  end.

Definition lf_add (a b : lf) : lf := LF (lc a + lc b) (zadd (lv a) (lv b)).
Definition lf_S (a : lf) : lf := LF (N.succ (lc a)) (lv a).
Definition lf_one : lf := LF 1 [].
Definition allz (vs : list N) : bool := forallb (fun v => N.eqb v 0) vs.
Definition all4 (vs : list N) : bool := forallb (fun v => N.eqb (N.modulo v 4) 0) vs.
Definition is_zero (a : lf) : bool := andb (N.eqb (lc a) 0) (allz (lv a)).
Definition is_one (a : lf) : bool := andb (N.eqb (lc a) 1) (allz (lv a)).
Definition posb (a : lf) : bool := negb (N.eqb (lc a) 0).

Inductive tl_ := T0 | TV (k : nat).
Definition run : Type := (Sym * lf)%type.
Definition sd : Type := (list run * tl_)%type.

Fixpoint alt (b : Sym) (n : nat) : list Sym :=
  match n with O => [] | S n' => b :: alt (sneg b) n' end.

Definition ev_tl (sg : nat -> side) (t : tl_) : side :=
  match t with T0 => const S0 | TV k => sg k end.

Fixpoint ev_runs (nu : list N) (rs : list run) (s : side) : side :=
  match rs with
  | [] => s
  | (b, n) :: rs' => alt b (ev nu n) *> ev_runs nu rs' s
  end.

Definition ev_sd nu sg (s : sd) : side := ev_runs nu (fst s) (ev_tl sg (snd s)).

Fixpoint pop_runs (rs : list run) (t : tl_) : option (Sym * sd) :=
  match rs with
  | (b, n) :: rs' =>
      if is_zero n then pop_runs rs' t
      else if posb n then
        Some (b, ((if is_one n then rs' else (sneg b, LF (N.pred (lc n)) (lv n)) :: rs'), t))
      else None
  | [] => match t with T0 => Some (S0, ([], T0)) | TV _ => None end
  end.

Definition pop (s : sd) : option (Sym * sd) := pop_runs (fst s) (snd s).

Definition push (w : Sym) (s : sd) : sd :=
  match s with
  | ((b0, n0) :: rs, t) =>
      if seqb w b0 then ((w, lf_one) :: (b0, n0) :: rs, t)
      else ((w, lf_S n0) :: rs, t)
  | ([], t) => ([(w, lf_one)], t)
  end.

(* the symbol that would continue the alternation after a run (c, n) *)
Definition afterb (c : Sym) (n : lf) : Sym := if N.eqb (N.modulo (lc n) 2) 0 then c else sneg c.

Definition push_run (c : Sym) (n : lf) (s : sd) : sd :=
  match s with
  | ((b0, n0) :: rs, t) =>
      if seqb (afterb c n) b0 then ((c, lf_add n n0) :: rs, t)
      else ((c, n) :: (b0, n0) :: rs, t)
  | ([], t) => ([(c, n)], t)
  end.

(* the two sweep cycles *)
Definition cR_st (i : nat) : Q :=
  match i mod 4 with 0 => B | 1 => C | 2 => A | _ => B end.
Definition cR_bt (i : nat) : Sym :=
  match i mod 4 with 0 => S0 | 1 => S1 | 2 => S0 | _ => S1 end.
Definition cR_idx (q : Q) (b : Sym) : option nat :=
  match q, b with
  | B, S0 => Some 0 | C, S1 => Some 1 | A, S0 => Some 2 | B, S1 => Some 3
  | _, _ => None
  end.
Definition cL_st (i : nat) : Q :=
  match i mod 4 with 0 => D | 1 => D | 2 => E | _ => C end.
Definition cL_bt (i : nat) : Sym :=
  match i mod 4 with 0 => S1 | 1 => S0 | 2 => S1 | _ => S0 end.
Definition cL_idx (q : Q) (b : Sym) : option nat :=
  match q, b with
  | D, S1 => Some 0 | D, S0 => Some 1 | E, S1 => Some 2 | C, S0 => Some 3
  | _, _ => None
  end.

(* the last symbol of a run (c, n) *)
Definition lastb (c : Sym) (n : lf) : Sym := if N.eqb (N.modulo (lc n) 2) 0 then sneg c else c.

Inductive cfg := Rc (q : Q) (l r : sd) | Lc (q : Q) (l r : sd).

Definition ev_cfg nu sg (c : cfg) : Q * tape :=
  match c with
  | Rc q l r => (ev_sd nu sg l) {{q}}> (ev_sd nu sg r)
  | Lc q l r => (ev_sd nu sg l) <{{q}} (ev_sd nu sg r)
  end.

Definition single (c : cfg) : option cfg :=
  match c with
  | Rc q l r =>
    match pop r with
    | Some (s, r') =>
      match tm (q, s) with
      | Some (w, R, q') => Some (Rc q' (push w l) r')
      | Some (w, L, q') => Some (Lc q' l (push w r'))
      | None => None
      end
    | None => None
    end
  | Lc q l r =>
    match pop l with
    | Some (s, l') =>
      match tm (q, s) with
      | Some (w, R, q') => Some (Rc q' (push w l') r)
      | Some (w, L, q') => Some (Lc q' l' (push w r))
      | None => None
      end
    | None => None
    end
  end.

Definition tag (o : option cfg) : option (cfg * bool) :=
  match o with Some c => Some (c, true) | None => None end.

Definition sstep (c : cfg) : option (cfg * bool) :=
  match c with
  | Rc q l ((b, n) :: rs, t) =>
      if is_zero n then Some (Rc q l (rs, t), false) else
      match cR_idx q b with
      | Some i =>
          if all4 (lv n) then
            Some (Rc (cR_st (i + N.to_nat (N.modulo (lc n) 4))) (push_run (sneg (lastb b n)) n l) (rs, t), posb n)
          else tag (single c)
      | None => tag (single c)
      end
  | Lc q ((b, n) :: ls, t) r =>
      if is_zero n then Some (Lc q (ls, t) r, false) else
      match cL_idx q b with
      | Some i =>
          if all4 (lv n) then
            Some (Lc (cL_st (i + N.to_nat (N.modulo (lc n) 4))) (ls, t) (push_run (sneg (lastb b n)) n r), posb n)
          else tag (single c)
      | None => tag (single c)
      end
  | _ => tag (single c)
  end.

(* run exactly p steps; the flag says whether at least one TM step was made *)
Fixpoint runp (p : positive) (c : cfg) : option (cfg * bool) :=
  match p with
  | xH => sstep c
  | xO p' =>
      match runp p' c with
      | Some (c1, b1) => match runp p' c1 with Some (c2, b2) => Some (c2, orb b1 b2) | None => None end
      | None => None
      end
  | xI p' =>
      match sstep c with
      | Some (c0, b0) =>
          match runp p' c0 with
          | Some (c1, b1) => match runp p' c1 with Some (c2, b2) => Some (c2, orb b0 (orb b1 b2)) | None => None end
          | None => None
          end
      | None => None
      end
  end.

(* ===================================================================== *)
(* Soundness                                                             *)
(* ===================================================================== *)

Lemma sneg_neq a b : seqb a b = false -> b = sneg a.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma seqb_eq a b : seqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma sneg_sneg a : sneg (sneg a) = a.
Proof. destruct a; reflexivity. Qed.

Lemma dot_zadd a b nu : dot (zadd a b) nu = (dot a nu + dot b nu)%N.
Proof.
  revert b nu. induction a as [|x a IH]; intros [|y b] [|z nu]; cbn; try lia.
  rewrite IH, N.mul_add_distr_r. lia.
Qed.

Lemma ev_add nu a b : ev nu (lf_add a b) = ev nu a + ev nu b.
Proof. unfold ev, lf_add; cbn. rewrite dot_zadd. lia. Qed.

Lemma ev_S nu a : ev nu (lf_S a) = S (ev nu a).
Proof. unfold ev, lf_S; cbn. lia. Qed.

Lemma allz_dot vs nu : allz vs = true -> dot vs nu = 0%N.
Proof.
  unfold allz in *. revert nu. induction vs as [|v vs IH]; intros [|x nu] H; cbn [dot forallb] in *; try reflexivity.
  apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. subst. rewrite IH by exact H2. lia.
Qed.

Lemma all4_dot vs nu : all4 vs = true -> exists k, dot vs nu = (4 * k)%N.
Proof.
  unfold all4 in *. revert nu. induction vs as [|v vs IH]; intros [|x nu] H; cbn [dot forallb] in *; try (exists 0%N; lia).
  apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1.
  destruct (IH nu H2) as [k Hk].
  apply N.Div0.mod_divides in H1 as [j Hj].
  exists (j * x + k)%N. rewrite Hk, Hj. lia.
Qed.

Lemma ev_zero nu a : is_zero a = true -> ev nu a = 0.
Proof.
  unfold is_zero, ev. intros H. apply andb_prop in H as [H1 H2].
  apply N.eqb_eq in H1. rewrite H1, (allz_dot _ _ H2). reflexivity.
Qed.

Lemma ev_one nu a : is_one a = true -> ev nu a = 1.
Proof.
  unfold is_one, ev. intros H. apply andb_prop in H as [H1 H2].
  apply N.eqb_eq in H1. rewrite H1, (allz_dot _ _ H2). reflexivity.
Qed.

Lemma ev_pos nu a : posb a = true -> ev nu a = S (ev nu (LF (N.pred (lc a)) (lv a))).
Proof.
  unfold posb, ev. cbn. intros H. apply Bool.negb_true_iff, N.eqb_neq in H. lia.
Qed.

Lemma ev_mod4 nu a : all4 (lv a) = true -> exists k, ev nu a = N.to_nat (lc a) + 4 * k.
Proof.
  intros H. destruct (all4_dot _ nu H) as [k Hk]. unfold ev. rewrite Hk.
  exists (N.to_nat k). lia.
Qed.

Lemma ev_runs_app nu rs1 rs2 s : ev_runs nu (rs1 ++ rs2) s = ev_runs nu rs1 (ev_runs nu rs2 s).
Proof. induction rs1 as [|[b n] rs1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma pop_runs_spec nu sg rs t b s' :
  pop_runs rs t = Some (b, s') -> ev_runs nu rs (ev_tl sg t) = b >> ev_sd nu sg s'.
Proof.
  revert b s'. induction rs as [|[b0 n] rs IH]; intros b s' H; cbn in H.
  - destruct t; [|discriminate]. inversion H; subst. cbn. apply const_unfold.
  - destruct (is_zero n) eqn:Ez.
    + cbn. rewrite (ev_zero nu n Ez). cbn. apply IH, H.
    + destruct (posb n) eqn:Ep; [|discriminate].
      inversion H; subst; clear H. cbn.
      destruct (is_one n) eqn:Eo.
      * rewrite (ev_one nu n Eo). reflexivity.
      * rewrite (ev_pos nu n Ep). reflexivity.
Qed.

Lemma pop_spec nu sg s b s' : pop s = Some (b, s') -> ev_sd nu sg s = b >> ev_sd nu sg s'.
Proof. destruct s as [rs t]. apply pop_runs_spec. Qed.

Lemma push_spec nu sg w s : ev_sd nu sg (push w s) = w >> ev_sd nu sg s.
Proof.
  destruct s as [[|[b0 n0] rs] t]; cbn; [reflexivity|].
  destruct (seqb w b0) eqn:E; cbn; [reflexivity|].
  rewrite ev_S. cbn. rewrite <-(sneg_neq _ _ E). reflexivity.
Qed.

Definition afterb_nat (c : Sym) (n : nat) : Sym := if Nat.eqb (n mod 2) 0 then c else sneg c.

Lemma afterb_nat_S c m : afterb_nat c (S m) = afterb_nat (sneg c) m.
Proof.
  unfold afterb_nat.
  destruct (Nat.eqb_spec (S m mod 2) 0), (Nat.eqb_spec (m mod 2) 0); try lia;
    [symmetry; apply sneg_sneg | reflexivity].
Qed.

Lemma alt_add c m k : alt c (m + k) = alt c m ++ alt (afterb_nat c m) k.
Proof.
  revert c. induction m as [|m IH]; intros c; [reflexivity|].
  change (S m + k) with (S (m + k)). cbn [alt app].
  rewrite IH, afterb_nat_S. reflexivity.
Qed.

Lemma afterb_ev nu c n : all4 (lv n) = true -> afterb c n = afterb_nat c (ev nu n).
Proof.
  intros H. destruct (ev_mod4 nu n H) as [k Hk]. rewrite Hk. unfold afterb, afterb_nat.
  destruct (N.eqb_spec (lc n mod 2) 0), (Nat.eqb_spec ((N.to_nat (lc n) + 4 * k) mod 2) 0);
    try reflexivity; exfalso; lia.
Qed.

Lemma push_run_spec nu sg c n s :
  all4 (lv n) = true -> ev_sd nu sg (push_run c n s) = alt c (ev nu n) *> ev_sd nu sg s.
Proof.
  intros H4. destruct s as [[|[b0 n0] rs] t]; cbn; [reflexivity|].
  destruct (seqb (afterb c n) b0) eqn:E; cbn.
  - rewrite ev_add, alt_add, Str_app_assoc. apply seqb_eq in E.
    rewrite <-(afterb_ev nu c n H4), E. reflexivity.
  - reflexivity.
Qed.

Definition lastb_nat (c : Sym) (m : nat) : Sym := if Nat.eqb (m mod 2) 0 then sneg c else c.

Lemma lastb_ev nu c n : all4 (lv n) = true -> lastb c n = lastb_nat c (ev nu n).
Proof.
  intros H. destruct (ev_mod4 nu n H) as [k Hk]. rewrite Hk. unfold lastb, lastb_nat.
  destruct (N.eqb_spec (lc n mod 2) 0), (Nat.eqb_spec ((N.to_nat (lc n) + 4 * k) mod 2) 0);
    try reflexivity; exfalso; lia.
Qed.

Lemma rev_alt b m (l : side) :
  alt (sneg (lastb_nat b (S m))) (S m) *> l = alt (sneg (lastb_nat (sneg b) m)) m *> (sneg b >> l).
Proof.
  rewrite <-Nat.add_1_r, alt_add, Str_app_assoc. cbn [alt Str_app].
  unfold lastb_nat, afterb_nat.
  destruct (Nat.eqb_spec ((m + 1) mod 2) 0), (Nat.eqb_spec (m mod 2) 0); try lia;
    destruct b; reflexivity.
Qed.

Lemma cR_cases i : (i mod 4 = 0 /\ S i mod 4 = 1) \/ (i mod 4 = 1 /\ S i mod 4 = 2) \/
                   (i mod 4 = 2 /\ S i mod 4 = 3) \/ (i mod 4 = 3 /\ S i mod 4 = 0).
Proof. lia. Qed.

Lemma cR_tm i : tm (cR_st i, cR_bt i) = Some (sneg (cR_bt i), R, cR_st (S i)).
Proof.
  unfold cR_st, cR_bt. destruct (cR_cases i) as [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]];
    rewrite H1, H2; reflexivity.
Qed.

Lemma cR_bt_S i : cR_bt (S i) = sneg (cR_bt i).
Proof.
  unfold cR_bt. destruct (cR_cases i) as [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]];
    rewrite H1, H2; reflexivity.
Qed.

Lemma cL_tm i : tm (cL_st i, cL_bt i) = Some (sneg (cL_bt i), L, cL_st (S i)).
Proof.
  unfold cL_st, cL_bt. destruct (cR_cases i) as [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]];
    rewrite H1, H2; reflexivity.
Qed.

Lemma cL_bt_S i : cL_bt (S i) = sneg (cL_bt i).
Proof.
  unfold cL_bt. destruct (cR_cases i) as [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]];
    rewrite H1, H2; reflexivity.
Qed.

Lemma accR_step i l X :
  (l {{cR_st i}}> (cR_bt i >> X)) --> ((sneg (cR_bt i) >> l) {{cR_st (S i)}}> X).
Proof. exact (step_right (cR_tm i)). Qed.

Lemma accL_step i r X :
  ((cL_bt i >> X) <{{cL_st i}} r) --> (X <{{cL_st (S i)}} (sneg (cL_bt i) >> r)).
Proof. exact (step_left (cL_tm i)). Qed.

Lemma accR m : forall i l r,
  (l {{cR_st i}}> (alt (cR_bt i) m *> r)) -->*
  ((alt (sneg (lastb_nat (cR_bt i) m)) m *> l) {{cR_st (i + m)}}> r).
Proof.
  induction m as [|m IH]; intros i l r.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_step; [cbn [alt Str_app]; apply accR_step|].
    pose proof (IH (S i) (sneg (cR_bt i) >> l) r) as H. rewrite cR_bt_S in H.
    rewrite rev_alt, Nat.add_succ_r. exact H.
Qed.

Lemma accR_S m i l r :
  (l {{cR_st i}}> (alt (cR_bt i) (S m) *> r)) -->+
  ((alt (sneg (lastb_nat (cR_bt i) (S m))) (S m) *> l) {{cR_st (i + S m)}}> r).
Proof.
  eapply progress_intro; [cbn [alt Str_app]; apply accR_step|].
  pose proof (accR m (S i) (sneg (cR_bt i) >> l) r) as H. rewrite cR_bt_S in H.
  rewrite rev_alt, Nat.add_succ_r. exact H.
Qed.

Lemma accL m : forall i l r,
  ((alt (cL_bt i) m *> l) <{{cL_st i}} r) -->*
  (l <{{cL_st (i + m)}} (alt (sneg (lastb_nat (cL_bt i) m)) m *> r)).
Proof.
  induction m as [|m IH]; intros i l r.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_step; [cbn [alt Str_app]; apply accL_step|].
    pose proof (IH (S i) l (sneg (cL_bt i) >> r)) as H. rewrite cL_bt_S in H.
    rewrite rev_alt, Nat.add_succ_r. exact H.
Qed.

Lemma accL_S m i l r :
  ((alt (cL_bt i) (S m) *> l) <{{cL_st i}} r) -->+
  (l <{{cL_st (i + S m)}} (alt (sneg (lastb_nat (cL_bt i) (S m))) (S m) *> r)).
Proof.
  eapply progress_intro; [cbn [alt Str_app]; apply accL_step|].
  pose proof (accL m (S i) l (sneg (cL_bt i) >> r)) as H. rewrite cL_bt_S in H.
  rewrite rev_alt, Nat.add_succ_r. exact H.
Qed.

Lemma single_spec nu sg c c' : single c = Some c' -> ev_cfg nu sg c --> ev_cfg nu sg c'.
Proof.
  destruct c as [q l r|q l r]; cbn [single].
  - destruct (pop r) as [[s r']|] eqn:Ep; [|discriminate].
    pose proof (pop_spec nu sg r s r' Ep) as Hr.
    destruct (tm (q, s)) as [[[w [|]] q']|] eqn:Et; intros H; inversion H; subst; clear H;
      cbn [ev_cfg]; rewrite Hr, ?push_spec.
    + exact (step_left Et).
    + exact (step_right Et).
  - destruct (pop l) as [[s l']|] eqn:Ep; [|discriminate].
    pose proof (pop_spec nu sg l s l' Ep) as Hl.
    destruct (tm (q, s)) as [[[w [|]] q']|] eqn:Et; intros H; inversion H; subst; clear H;
      cbn [ev_cfg]; rewrite Hl, ?push_spec.
    + exact (step_left Et).
    + exact (step_right Et).
Qed.

Definition Rel (b : bool) (c c' : Q * tape) : Prop := if b then c -->+ c' else c -->* c'.

Lemma Rel_trans b1 b2 c c' c'' : Rel b1 c c' -> Rel b2 c' c'' -> Rel (orb b1 b2) c c''.
Proof.
  destruct b1, b2; cbn; intros H1 H2.
  - eapply progress_trans; eauto.
  - eapply progress_evstep_trans; eauto.
  - eapply evstep_progress_trans; eauto.
  - eapply evstep_trans; eauto.
Qed.

Lemma tag_spec nu sg c o c' b : o = single c -> tag o = Some (c', b) -> Rel b (ev_cfg nu sg c) (ev_cfg nu sg c').
Proof.
  intros -> H. unfold tag in H. destruct (single c) eqn:E; [|discriminate].
  inversion H; subst. cbn. apply progress_base. apply single_spec, E.
Qed.

Lemma cR_idx_spec q b i : cR_idx q b = Some i -> q = cR_st i /\ b = cR_bt i.
Proof. destruct q, b; cbn; intros H; inversion H; subst; split; reflexivity. Qed.

Lemma cL_idx_spec q b i : cL_idx q b = Some i -> q = cL_st i /\ b = cL_bt i.
Proof. destruct q, b; cbn; intros H; inversion H; subst; split; reflexivity. Qed.

Lemma cR_st_mod i k : cR_st (i + N.to_nat (N.modulo k 4)) = cR_st (i + N.to_nat k).
Proof.
  unfold cR_st. rewrite N2Nat.inj_mod by discriminate. change (N.to_nat 4) with 4.
  rewrite Nat.Div0.add_mod_idemp_r. reflexivity.
Qed.

Lemma cL_st_mod i k : cL_st (i + N.to_nat (N.modulo k 4)) = cL_st (i + N.to_nat k).
Proof.
  unfold cL_st. rewrite N2Nat.inj_mod by discriminate. change (N.to_nat 4) with 4.
  rewrite Nat.Div0.add_mod_idemp_r. reflexivity.
Qed.

Lemma cR_st_add4 i a k : cR_st (i + (a + 4 * k)) = cR_st (i + a).
Proof. unfold cR_st. replace ((i + (a + 4 * k)) mod 4) with ((i + a) mod 4) by lia. reflexivity. Qed.

Lemma cL_st_add4 i a k : cL_st (i + (a + 4 * k)) = cL_st (i + a).
Proof. unfold cL_st. replace ((i + (a + 4 * k)) mod 4) with ((i + a) mod 4) by lia. reflexivity. Qed.

Lemma sstep_spec nu sg c c' b : sstep c = Some (c', b) -> Rel b (ev_cfg nu sg c) (ev_cfg nu sg c').
Proof.
  intros H.
  destruct c as [q l [[|[b0 n] rs] t]|q [[|[b0 n] ls] t] r];
    try (eapply tag_spec; [reflexivity | exact H]).
  - cbn [sstep] in H.
    destruct (is_zero n) eqn:Ez.
    + inversion H; subst. cbn. unfold ev_sd. cbn [fst snd ev_runs]. rewrite (ev_zero nu n Ez). cbn. apply evstep_refl.
    + destruct (cR_idx q b0) as [i|] eqn:Ei; [|eapply tag_spec; [reflexivity|exact H]].
      destruct (all4 (lv n)) eqn:E4; [|eapply tag_spec; [reflexivity|exact H]].
      inversion H; subst; clear H.
      destruct (cR_idx_spec _ _ _ Ei) as [-> ->].
      cbn [ev_cfg]. rewrite push_run_spec by exact E4. unfold ev_sd at 2. cbn [fst snd ev_runs].
      rewrite (lastb_ev nu _ _ E4), cR_st_mod.
      destruct (ev_mod4 nu n E4) as [k Hk].
      replace (cR_st (i + N.to_nat (lc n))) with (cR_st (i + ev nu n)) by (rewrite Hk; apply cR_st_add4).
      unfold posb. destruct (N.eqb_spec (lc n) 0) as [Hz|Hz]; cbn.
      * apply accR.
      * destruct (ev nu n) as [|m] eqn:Em; [lia|]. apply accR_S.
  - cbn [sstep] in H.
    destruct (is_zero n) eqn:Ez.
    + inversion H; subst. cbn. unfold ev_sd. cbn [fst snd ev_runs]. rewrite (ev_zero nu n Ez). cbn. apply evstep_refl.
    + destruct (cL_idx q b0) as [i|] eqn:Ei; [|eapply tag_spec; [reflexivity|exact H]].
      destruct (all4 (lv n)) eqn:E4; [|eapply tag_spec; [reflexivity|exact H]].
      inversion H; subst; clear H.
      destruct (cL_idx_spec _ _ _ Ei) as [-> ->].
      cbn [ev_cfg]. rewrite push_run_spec by exact E4. unfold ev_sd at 1. cbn [fst snd ev_runs].
      rewrite (lastb_ev nu _ _ E4), cL_st_mod.
      destruct (ev_mod4 nu n E4) as [k Hk].
      replace (cL_st (i + N.to_nat (lc n))) with (cL_st (i + ev nu n)) by (rewrite Hk; apply cL_st_add4).
      unfold posb. destruct (N.eqb_spec (lc n) 0) as [Hz|Hz]; cbn.
      * apply accL.
      * destruct (ev nu n) as [|m] eqn:Em; [lia|]. apply accL_S.
Qed.

Lemma runp_spec nu sg p : forall c c' b, runp p c = Some (c', b) -> Rel b (ev_cfg nu sg c) (ev_cfg nu sg c').
Proof.
  induction p as [p IH|p IH|]; intros c c' b H; cbn [runp] in H.
  - destruct (sstep c) as [[c0 b0]|] eqn:E0; [|discriminate].
    destruct (runp p c0) as [[c1 b1]|] eqn:E1; [|discriminate].
    destruct (runp p c1) as [[c2 b2]|] eqn:E2; [|discriminate].
    inversion H; subst.
    eapply Rel_trans; [apply (sstep_spec nu sg _ _ _ E0)|].
    eapply Rel_trans; [apply (IH _ _ _ E1)|apply (IH _ _ _ E2)].
  - destruct (runp p c) as [[c1 b1]|] eqn:E1; [|discriminate].
    destruct (runp p c1) as [[c2 b2]|] eqn:E2; [|discriminate].
    inversion H; subst.
    eapply Rel_trans; [apply (IH _ _ _ E1)|apply (IH _ _ _ E2)].
  - apply sstep_spec, H.
Qed.

(* ===================================================================== *)
(* Running to a target configuration                                     *)
(* ===================================================================== *)

Fixpoint strip0 (vs : list N) : list N :=
  match vs with
  | [] => []
  | v :: vs' => match strip0 vs' with [] => if N.eqb v 0 then [] else [v] | w => v :: w end
  end.

Fixpoint listN_eqb (a b : list N) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => andb (N.eqb x y) (listN_eqb a' b')
  | _, _ => false
  end.

Definition lf_eqb (a b : lf) : bool := andb (N.eqb (lc a) (lc b)) (listN_eqb (strip0 (lv a)) (strip0 (lv b))).

Definition runs_eqb (a b : list run) : bool :=
  (fix f (a b : list run) := match a, b with
   | [], [] => true
   | (x, n) :: a', (y, m) :: b' => andb (andb (seqb x y) (lf_eqb n m)) (f a' b')
   | _, _ => false end) a b.

Definition tl_eqb (a b : tl_) : bool :=
  match a, b with T0, T0 => true | TV i, TV j => Nat.eqb i j | _, _ => false end.

Definition sd_eqb (a b : sd) : bool := andb (runs_eqb (fst a) (fst b)) (tl_eqb (snd a) (snd b)).

Definition q_eqb (a b : Q) : bool :=
  match a, b with A, A | B, B | C, C | D, D | E, E | F, F => true | _, _ => false end.

Definition cfg_eqb (a b : cfg) : bool :=
  match a, b with
  | Rc q l r, Rc q' l' r' => andb (q_eqb q q') (andb (sd_eqb l l') (sd_eqb r r'))
  | Lc q l r, Lc q' l' r' => andb (q_eqb q q') (andb (sd_eqb l l') (sd_eqb r r'))
  | _, _ => false
  end.

Lemma dot_strip0 vs nu : dot (strip0 vs) nu = dot vs nu.
Proof.
  revert nu. induction vs as [|v vs IH]; intros nu; [reflexivity|].
  cbn [strip0]. destruct (strip0 vs) as [|w ws] eqn:E.
  - destruct (N.eqb_spec v 0) as [->|Hv]; destruct nu as [|x nu]; cbn [dot]; try reflexivity.
    + rewrite <-IH. cbn. lia.
    + rewrite <-IH. cbn. lia.
  - destruct nu as [|x nu]; cbn [dot]; [reflexivity|]. rewrite <-IH. reflexivity.
Qed.

Lemma listN_eqb_eq a b : listN_eqb a b = true -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. subst. f_equal. apply IH, H2.
Qed.

Lemma lf_eqb_ev nu a b : lf_eqb a b = true -> ev nu a = ev nu b.
Proof.
  unfold lf_eqb, ev. intros H. apply andb_prop in H as [H1 H2].
  apply N.eqb_eq in H1. apply listN_eqb_eq in H2.
  rewrite H1, <-(dot_strip0 (lv a)), <-(dot_strip0 (lv b)), H2. reflexivity.
Qed.

Lemma runs_eqb_ev nu a b s : runs_eqb a b = true -> ev_runs nu a s = ev_runs nu b s.
Proof.
  revert b. induction a as [|[x n] a IH]; intros [|[y m] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
  apply seqb_eq in H1. subst. cbn. rewrite (lf_eqb_ev nu _ _ H2), (IH _ H3). reflexivity.
Qed.

Lemma sd_eqb_ev nu sg a b : sd_eqb a b = true -> ev_sd nu sg a = ev_sd nu sg b.
Proof.
  destruct a as [ra ta], b as [rb tb]. unfold sd_eqb, ev_sd; cbn [fst snd]. intros H.
  apply andb_prop in H as [H1 H2].
  assert (ta = tb) as ->.
  { destruct ta, tb; cbn in H2; try discriminate; [reflexivity|]. apply Nat.eqb_eq in H2. subst. reflexivity. }
  apply runs_eqb_ev, H1.
Qed.

Lemma q_eqb_eq a b : q_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma cfg_eqb_ev nu sg a b : cfg_eqb a b = true -> ev_cfg nu sg a = ev_cfg nu sg b.
Proof.
  destruct a as [q l r|q l r], b as [q' l' r'|q' l' r']; cbn [cfg_eqb]; intros H; try discriminate;
  apply andb_prop in H as [H1 H]; apply andb_prop in H as [H2 H3];
  apply q_eqb_eq in H1; subst; cbn [ev_cfg];
  rewrite (sd_eqb_ev nu sg _ _ H2), (sd_eqb_ev nu sg _ _ H3); reflexivity.
Qed.

Definition rstep (tgt : cfg) (st : cfg * bool * bool) : cfg * bool * bool :=
  let '(c, pr, dn) := st in
  if dn then st else
  match sstep c with
  | Some (c', b) => (c', orb pr b, cfg_eqb c' tgt)
  | None => st
  end.

(* reach fuel c tgt = true: c reaches tgt in at most fuel simulator steps, at least one machine step *)
Definition reach (fuel : positive) (c tgt : cfg) : bool :=
  let '(c', pr, dn) := Pos.iter (rstep tgt) (c, false, false) fuel in andb pr dn.

Lemma reach_spec fuel c tgt : reach fuel c tgt = true ->
  forall nu sg, ev_cfg nu sg c -->+ ev_cfg nu sg tgt.
Proof.
  intros H nu sg. unfold reach in H.
  pose (Inv := fun st : cfg * bool * bool => let '(c', pr, dn) := st in
    Rel pr (ev_cfg nu sg c) (ev_cfg nu sg c') /\ (dn = true -> cfg_eqb c' tgt = true)).
  assert (HI : Inv (Pos.iter (rstep tgt) (c, false, false) fuel)).
  { apply Pos.iter_invariant.
    - intros [[c1 pr] dn] [HR Hd]. unfold rstep.
      destruct dn; [split; assumption|].
      destruct (sstep c1) as [[c2 b]|] eqn:Es; [|split; assumption].
      split; [|intros E; exact E].
      apply (Rel_trans _ _ _ _ _ HR (sstep_spec nu sg _ _ _ Es)).
    - split; [apply evstep_refl | discriminate]. }
  destruct (Pos.iter (rstep tgt) (c, false, false) fuel) as [[c' pr] dn].
  destruct HI as [HR Hd]. apply andb_prop in H as [-> ->].
  rewrite <-(cfg_eqb_ev nu sg _ _ (Hd eq_refl)). exact HR.
Qed.

Definition cn (n : N) : lf := LF n [].

(* ===================================================================== *)
(* Blocks of the chain.                                                  *)
(* ===================================================================== *)

Fixpoint mkruns (b : Sym) (ns : list lf) : list run :=
  match ns with [] => [] | n :: ns' => (b, n) :: mkruns (lastb b n) ns' end.

(* gap variables of an m = 3 block: t = 4 + 4 x0, s = 4 + 4 x1, a = 1 + 4 x2, lp = 2 + 4 x3 *)
Definition vt c := LF c [4;0;0;0]%N.
Definition vs c := LF c [0;4;0;0]%N.
Definition va c := LF c [0;0;4;0]%N.
Definition vl c := LF c [0;0;0;4]%N.

Inductive lab := U0 | U1 | U2 | W0 | W1 | D0 | D1 | D2.

Definition lens (s : lab) : list lf :=
  match s with
  | U0 => [cn 3; vt 4; vs 4; va 1; vl 2]
  | U1 => [cn 3; vt 4; vs 4; va 2; vl 1]
  | U2 => [cn 3; vt 4; vs 4; va 3; vl 0]
  | W0 => [cn 3; vt 1; vs 6; va 4; vl 0]
  | W1 => [cn 3; vt 2; vs 5; va 4; vl 0]
  | D0 => [cn 3; vt 3; vs 4; va 4; vl 0]
  | D1 => [cn 2; vt 4; vs 4; va 4; vl 0]
  | D2 => [cn 1; vt 5; vs 4; va 4; vl 0]
  end%N.
Definition blk (s : lab) : list run := mkruns S0 (lens s).

(* a full block after the head has passed it leftward (now on the right of the head) *)
Definition rlens (s : lab) : list lf :=
  match s with
  | D0 => [vl 0; va 4; vs 4; vt 3; cn 3]
  | _  => [vl 0; va 3; vs 4; vt 4; cn 3]
  end%N.
Definition rblk (s : lab) : list run := mkruns S0 (rlens s).

(* block 1 (m = 1), concrete *)
Inductive lab1 := P0 | P1 | PD0 | PD1 | PD2.
Definition lens1 (s : lab1) : list lf :=
  match s with
  | P0 => [cn 3; cn 1; cn 3] | P1 => [cn 3; cn 2; cn 2] | PD0 => [cn 3; cn 3; cn 1]
  | PD1 => [cn 2; cn 4; cn 1] | PD2 => [cn 1; cn 5; cn 1]
  end%N.
Definition blk1 (s : lab1) : list run := mkruns S0 (lens1 s).
Definition rblk1 : list run := mkruns S1 [cn 1; cn 3; cn 3]%N.

(* exit phase: true = c + 2 (state A at the cut), false = c (state B) *)
Definition stp (p : bool) : Q := if p then A else B.

Definition turn (s : lab) : option (lab * bool) :=
  match s with
  | U0 => Some (U1, true) | U1 => Some (U2, true) | W0 => Some (W1, true) | W1 => Some (D0, true)
  | D1 => Some (D0, false) | D2 => Some (D1, false) | _ => None
  end.
Definition reset (s : lab) (p : bool) : option (lab * bool) :=
  match s, p with
  | U2, true => Some (U0, true) | U2, false => Some (W0, true) | D0, false => Some (D2, false)
  | _, _ => None
  end.
Definition turn1 (s : lab1) : option (lab1 * bool) :=
  match s with
  | P0 => Some (P1, true) | P1 => Some (PD0, true) | PD1 => Some (PD0, false) | PD2 => Some (PD1, false)
  | PD0 => None
  end.

Definition sg2 (L R : side) : nat -> side := fun k => match k with O => L | _ => R end.

Lemma reach_LR fuel q q' l l' nu L R :
  reach fuel (Lc q (l, TV 0) ([], TV 1)) (Rc q' (l', TV 0) ([], TV 1)) = true ->
  ev_runs nu l L <{{q}} R -->+ ev_runs nu l' L {{q'}}> R.
Proof. intros H. exact (reach_spec _ _ _ H nu (sg2 L R)). Qed.

Lemma reach_LL fuel q q' l r' nu L R :
  reach fuel (Lc q (l, TV 0) ([], TV 1)) (Lc q' ([], TV 0) (r', TV 1)) = true ->
  ev_runs nu l L <{{q}} R -->+ L <{{q'}} ev_runs nu r' R.
Proof. intros H. exact (reach_spec _ _ _ H nu (sg2 L R)). Qed.

Lemma reach_RR fuel q q' r l' nu L R :
  reach fuel (Rc q ([], TV 0) (r, TV 1)) (Rc q' (l', TV 0) ([], TV 1)) = true ->
  L {{q}}> ev_runs nu r R -->+ ev_runs nu l' L {{q'}}> R.
Proof. intros H. exact (reach_spec _ _ _ H nu (sg2 L R)). Qed.

Lemma blk_turn s s' p nu L R : turn s = Some (s', p) ->
  ev_runs nu (blk s) L <{{D}} R -->+ ev_runs nu (blk s') L {{stp p}}> R.
Proof.
  intros H. destruct s; cbn in H; inversion H; subst; clear H; cbn [stp];
    apply (reach_LR 100); vm_compute; reflexivity.
Qed.

Lemma blk_pass s nu L R : turn s = None ->
  ev_runs nu (blk s) L <{{D}} R -->+ L <{{D}} ev_runs nu (rblk s) R.
Proof.
  intros H. destruct s; cbn in H; inversion H; apply (reach_LL 100); vm_compute; reflexivity.
Qed.

Lemma blk_reset s p s' p' nu L R : reset s p = Some (s', p') ->
  L {{stp p}}> ev_runs nu (rblk s) R -->+ ev_runs nu (blk s') L {{stp p'}}> R.
Proof.
  intros H. destruct s, p; cbn in H; inversion H; subst; clear H; cbn [stp];
    apply (reach_RR 100); vm_compute; reflexivity.
Qed.

Lemma blk1_turn s s' p L R : turn1 s = Some (s', p) ->
  ev_runs [] (blk1 s) L <{{D}} R -->+ ev_runs [] (blk1 s') L {{stp p}}> R.
Proof.
  intros H. destruct s; cbn in H; inversion H; subst; clear H; cbn [stp];
    apply (reach_LR 100); vm_compute; reflexivity.
Qed.

Lemma blk1_pass L R : ev_runs [] (blk1 PD0) L <{{D}} R -->+ L <{{E}} ev_runs [] rblk1 R.
Proof. refine (reach_LL 100 D E (blk1 PD0) rblk1 [] L R _). vm_compute. reflexivity. Qed.

Lemma blk1_back L R : L {{B}}> ev_runs [] rblk1 R -->+ ev_runs [] (blk1 PD2) L {{B}}> R.
Proof. refine (reach_RR 100 B B rblk1 (blk1 PD2) [] L R _). vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* The left word: a 4-digit ternary counter (episodes 0..79), and the    *)
(* left record (episode 80).                                             *)
(* ===================================================================== *)

Definition dgr (v : nat) : list run :=
  match v with
  | O => [(S0, cn 1); (S0, cn 5)]
  | S O => [(S0, cn 2); (S1, cn 4)]
  | _ => [(S0, cn 3); (S0, cn 3)]
  end%N.

Definition lw (i : nat) : list run :=
  if Nat.ltb i 81 then
    [(S1, cn 3); (S1, cn 4)] ++ dgr (i mod 3) ++ dgr (i / 3 mod 3) ++ dgr (i / 9 mod 3) ++ dgr (i / 27 mod 3)
      ++ [(S0, cn 2)]
  else [(S0, cn 6); (S1, cn 4)] ++ dgr 0 ++ dgr 0 ++ dgr 0 ++ dgr 0 ++ [(S0, cn 2)].

Definition LWs (i : nat) : side := ev_runs [] (lw i) (const S0).

Lemma reach_T0 fuel q q' l l' (Y : side) :
  reach fuel (Lc q (l, T0) ([], TV 0)) (Rc q' (l', T0) ([], TV 0)) = true ->
  ev_runs [] l (const S0) <{{q}} Y -->+ ev_runs [] l' (const S0) {{q'}}> Y.
Proof. intros H. exact (reach_spec _ _ _ H [] (fun _ => Y)). Qed.

Definition lw_ok (i : nat) : bool := reach 1000 (Lc E (lw i, T0) ([], TV 0)) (Rc B (lw (S i), T0) ([], TV 0)).

Lemma lw_all : forallb lw_ok (seq 0 81) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lw_ok_spec i Y : lw_ok i = true ->
  ev_runs [] (lw i) (const S0) <{{E}} Y -->+ ev_runs [] (lw (S i)) (const S0) {{B}}> Y.
Proof. exact (reach_T0 1000 E B (lw i) (lw (S i)) Y). Qed.

Lemma lw_ok_lt i : i < 81 -> lw_ok i = true.
Proof. intros Hi. pose proof lw_all as H. rewrite forallb_forall in H. apply H, in_seq. lia. Qed.

Lemma lw_ep i Y : i < 81 -> LWs i <{{E}} Y -->+ LWs (S i) {{B}}> Y.
Proof. intros Hi. apply lw_ok_spec, lw_ok_lt, Hi. Qed.

(* ===================================================================== *)
(* The chain: m = 3 blocks (nearest the head first), then block 1, then  *)
(* the left word.                                                        *)
(* ===================================================================== *)

Fixpoint chs (ls : list lab) (nus : list (list N)) (L : side) : side :=
  match ls, nus with
  | s :: ls', nu :: nus' => ev_runs nu (blk s) (chs ls' nus' L)
  | _, _ => L
  end.

Fixpoint rchs (ls : list lab) (nus : list (list N)) (R : side) : side :=
  match ls, nus with
  | s :: ls', nu :: nus' => rchs ls' nus' (ev_runs nu (rblk s) R)
  | _, _ => R
  end.

Fixpoint visit3 (ls : list lab) : option (list lab * bool) :=
  match ls with
  | [] => None
  | s :: ls' =>
    match turn s with
    | Some (s', p) => Some (s' :: ls', p)
    | None =>
      match visit3 ls' with
      | Some (ls'', p') => match reset s p' with Some (s'', p'') => Some (s'' :: ls'', p'') | None => None end
      | None => None
      end
    end
  end.

Fixpoint cb (ls : list lab) (p : bool) : option (list lab * bool) :=
  match ls with
  | [] => Some ([], p)
  | s :: ls' =>
    match cb ls' p with
    | Some (ls'', p') => match reset s p' with Some (s'', p'') => Some (s'' :: ls'', p'') | None => None end
    | None => None
    end
  end.

Definition fullb (s : lab) : bool := match turn s with None => true | Some _ => false end.

Lemma visit3_spec ls : forall ls' p nus L R, visit3 ls = Some (ls', p) -> length ls = length nus ->
  chs ls nus L <{{D}} R -->+ chs ls' nus L {{stp p}}> R.
Proof.
  induction ls as [|s ls IH]; intros ls' p nus L R H Hl; [discriminate|].
  destruct nus as [|nu nus]; [discriminate|]. cbn in Hl. injection Hl as Hl.
  cbn [visit3] in H.
  destruct (turn s) as [[s1 p1]|] eqn:Et.
  - inversion H; subst. cbn [chs]. apply blk_turn, Et.
  - destruct (visit3 ls) as [[ls1 p1]|] eqn:Ev; [|discriminate].
    destruct (reset s p1) as [[s2 p2]|] eqn:Er; [|discriminate].
    inversion H; subst; clear H. cbn [chs].
    eapply progress_trans; [apply blk_pass, Et|].
    eapply progress_trans; [apply (IH _ _ _ _ _ eq_refl Hl)|].
    apply blk_reset, Er.
Qed.

Lemma pass_spec ls : forall nus L R, forallb fullb ls = true -> length ls = length nus ->
  chs ls nus L <{{D}} R -->* L <{{D}} rchs ls nus R.
Proof.
  induction ls as [|s ls IH]; intros nus L R H Hl.
  - destruct nus; [apply evstep_refl | discriminate].
  - destruct nus as [|nu nus]; [discriminate|]. cbn in Hl. injection Hl as Hl.
    cbn [forallb] in H. apply andb_prop in H as [H1 H2].
    cbn [chs rchs].
    eapply evstep_trans; [apply progress_evstep, blk_pass|].
    + unfold fullb in H1. destruct (turn s); [discriminate | reflexivity].
    + apply IH; assumption.
Qed.

Lemma cb_spec ls : forall p ls' p' nus L R, cb ls p = Some (ls', p') -> length ls = length nus ->
  L {{stp p}}> rchs ls nus R -->* chs ls' nus L {{stp p'}}> R.
Proof.
  induction ls as [|s ls IH]; intros p ls' p' nus L R H Hl.
  - destruct nus; [|discriminate]. inversion H; subst. apply evstep_refl.
  - destruct nus as [|nu nus]; [discriminate|]. cbn in Hl. injection Hl as Hl.
    cbn [cb] in H.
    destruct (cb ls p) as [[ls1 p1]|] eqn:Ec; [|discriminate].
    destruct (reset s p1) as [[s2 p2]|] eqn:Er; [|discriminate].
    inversion H; subst; clear H. cbn [chs rchs].
    eapply evstep_trans; [apply (IH _ _ _ _ _ _ Ec Hl)|].
    apply progress_evstep, blk_reset, Er.
Qed.

Lemma visit3_len ls : forall ls' p, visit3 ls = Some (ls', p) -> length ls' = length ls.
Proof.
  induction ls as [|s ls IH]; intros ls' p H; [discriminate|]. cbn in H.
  destruct (turn s) as [[s1 p1]|]; [inversion H; reflexivity|].
  destruct (visit3 ls) as [[ls1 p1]|] eqn:E; [|discriminate].
  destruct (reset s p1) as [[s2 p2]|]; [|discriminate].
  inversion H; subst. cbn. rewrite (IH _ _ eq_refl). reflexivity.
Qed.

Lemma cb_len ls : forall p ls' p', cb ls p = Some (ls', p') -> length ls' = length ls.
Proof.
  induction ls as [|s ls IH]; intros p ls' p' H; cbn in H; [inversion H; reflexivity|].
  destruct (cb ls p) as [[ls1 p1]|] eqn:E; [|discriminate].
  destruct (reset s p1) as [[s2 p2]|]; [|discriminate].
  inversion H; subst. cbn. rewrite (IH _ _ _ E). reflexivity.
Qed.

(* ===================================================================== *)
(* One visit of the whole chain (Lemma C, C', and the left episodes).   *)
(* ===================================================================== *)

Definition vst : Type := (list lab * lab1 * nat)%type.

Definition lab1_eqb (a b : lab1) : bool :=
  match a, b with P0, P0 | P1, P1 | PD0, PD0 | PD1, PD1 | PD2, PD2 => true | _, _ => false end.

Definition vis (st : vst) : option (vst * bool) :=
  let '(ls, b, i) := st in
  match visit3 ls with
  | Some (ls', p) => Some ((ls', b, i), p)
  | None =>
    if forallb fullb ls then
      match turn1 b with
      | Some (b', p1) => match cb ls p1 with Some (ls', p) => Some ((ls', b', i), p) | None => None end
      | None =>
        if andb (lab1_eqb b PD0) (Nat.ltb i 80) then
          match cb ls false with Some (ls', p) => Some ((ls', PD2, S i), p) | None => None end
        else None
      end
    else None
  end.

Definition b1s (b : lab1) (X : side) : side := ev_runs [] (blk1 b) X.

Definition Gc (st : vst) (nus : list (list N)) (R : side) : Q * tape :=
  let '(ls, b, i) := st in chs ls nus (b1s b (LWs i)) <{{D}} R.
Definition Gx (st : vst) (nus : list (list N)) (p : bool) (R : side) : Q * tape :=
  let '(ls, b, i) := st in chs ls nus (b1s b (LWs i)) {{stp p}}> R.

Definition vlen (st : vst) : nat := let '(ls, _, _) := st in length ls.

Lemma lab1_eqb_eq a b : lab1_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma vis_spec st st' p nus R : vis st = Some (st', p) -> vlen st = length nus ->
  Gc st nus R -->+ Gx st' nus p R /\ vlen st' = vlen st.
Proof.
  destruct st as [[ls b] i]. cbn [vis vlen]. intros H Hl.
  destruct (visit3 ls) as [[ls1 p1]|] eqn:Ev.
  - inversion H; subst; clear H. cbn [Gc Gx vlen]. split.
    + apply visit3_spec; assumption.
    + apply (visit3_len _ _ _ Ev).
  - destruct (forallb fullb ls) eqn:Ef; [|discriminate].
    destruct (turn1 b) as [[b1 p1]|] eqn:Et.
    + destruct (cb ls p1) as [[ls1 p2]|] eqn:Ec; [|discriminate].
      inversion H; subst; clear H. cbn [Gc Gx vlen]. split; [|apply (cb_len _ _ _ _ Ec)].
      eapply evstep_progress_trans; [apply pass_spec; assumption|].
      unfold b1s at 1. eapply progress_evstep_trans; [apply blk1_turn, Et|].
      apply cb_spec; assumption.
    + destruct (andb (lab1_eqb b PD0) (Nat.ltb i 80)) eqn:Eb; [|discriminate].
      apply andb_prop in Eb as [Eb Ei]. apply lab1_eqb_eq in Eb. subst b. apply Nat.ltb_lt in Ei.
      destruct (cb ls false) as [[ls1 p2]|] eqn:Ec; [|discriminate].
      inversion H; subst; clear H. cbn [Gc Gx vlen]. split; [|apply (cb_len _ _ _ _ Ec)].
      eapply evstep_progress_trans; [apply pass_spec; assumption|].
      unfold b1s at 1. eapply progress_trans; [apply blk1_pass|].
      eapply progress_trans; [apply lw_ep; lia|].
      eapply progress_evstep_trans; [apply blk1_back|].
      apply (cb_spec _ false); assumption.
Qed.

(* ===================================================================== *)
(* Right-region episodes, abstractly.                                    *)
(* ===================================================================== *)

Definition Ep (p : bool) (R R' : side) : Prop := forall l, l {{stp p}}> R -->* l <{{D}} R'.

Fixpoint EpSeq (ps : list bool) (R R' : side) : Prop :=
  match ps with
  | [] => R = R'
  | p :: ps' => exists R1, Ep p R R1 /\ EpSeq ps' R1 R'
  end.

Fixpoint runv (n : nat) (st : vst) : option (vst * list bool) :=
  match n with
  | O => Some (st, [])
  | S n' =>
    match vis st with
    | Some (st1, p) => match runv n' st1 with Some (st2, ps) => Some (st2, p :: ps) | None => None end
    | None => None
    end
  end.

Lemma runv_spec n : forall st st' ps nus R R', runv n st = Some (st', ps) -> vlen st = length nus ->
  EpSeq ps R R' -> Gc st nus R -->* Gc st' nus R'.
Proof.
  induction n as [|n IH]; intros st st' ps nus R R' H Hl HE.
  - cbn in H. inversion H; subst. cbn in HE. subst. apply evstep_refl.
  - cbn [runv] in H.
    destruct (vis st) as [[st1 p]|] eqn:Ev; [|discriminate].
    destruct (runv n st1) as [[st2 ps2]|] eqn:Er; [|discriminate].
    inversion H; subst; clear H.
    destruct HE as [R1 [HE1 HE2]].
    destruct (vis_spec _ _ _ nus R Ev Hl) as [H1 H2].
    eapply evstep_trans; [apply progress_evstep, H1|].
    eapply evstep_trans; [|apply (IH st1 st' ps2 nus R1 R' Er); [congruence | exact HE2]].
    destruct st1 as [[ls1 b1] i1]. cbn [Gx Gc]. apply HE1.
Qed.

(* ===================================================================== *)
(* Lemma T: the visits of one record interval, as a computation on block *)
(* labels.                                                               *)
(* ===================================================================== *)

Lemma runv_add a : forall b st st1 ps1 st2 ps2,
  runv a st = Some (st1, ps1) -> runv b st1 = Some (st2, ps2) -> runv (a + b) st = Some (st2, ps1 ++ ps2).
Proof.
  induction a as [|a IH]; intros b st st1 ps1 st2 ps2 H1 H2.
  - cbn in H1. inversion H1; subst. exact H2.
  - change (S a + b) with (S (a + b)). cbn [runv] in H1 |- *. destruct (vis st) as [[st0 p]|]; [|discriminate].
    destruct (runv a st0) as [[st3 ps3]|] eqn:E; [|discriminate].
    inversion H1; subst. rewrite (IH _ _ _ _ _ _ E H2). reflexivity.
Qed.

Lemma runv_one st st' p : vis st = Some (st', p) -> runv 1 st = Some (st', [p]).
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Lemma vis3 ls ls' p b i : visit3 ls = Some (ls', p) -> vis (ls, b, i) = Some ((ls', b, i), p).
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Lemma repeat_add {X} (x : X) n m : repeat x (n + m) = repeat x n ++ repeat x m.
Proof. induction n; cbn in *; congruence. Qed.

Lemma repeat_snoc {X} (x : X) n l : repeat x n ++ x :: l = repeat x (S n) ++ l.
Proof. induction n; cbn in *; congruence. Qed.

Lemma pow3_pos j : 1 <= 3 ^ j.
Proof. induction j; cbn; lia. Qed.

Lemma visit3_U2 j X X' : visit3 X = Some (X', true) -> visit3 (repeat U2 j ++ X) = Some (repeat U0 j ++ X', true).
Proof. intros H. induction j as [|j IH]; cbn; [exact H|]. rewrite IH. reflexivity. Qed.

Lemma cb_U2 j X p X' : cb X p = Some (X', true) -> cb (repeat U2 j ++ X) p = Some (repeat U0 j ++ X', true).
Proof. intros H. induction j as [|j IH]; cbn; [exact H|]. rewrite IH. reflexivity. Qed.

Lemma visit3_full ls : forallb fullb ls = true -> visit3 ls = None.
Proof.
  induction ls as [|s ls IH]; cbn; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. unfold fullb in H1.
  destruct (turn s); [discriminate|]. rewrite IH by exact H2. reflexivity.
Qed.

Lemma fullb_U2 j : forallb fullb (repeat U2 j) = true.
Proof. induction j; cbn; auto. Qed.

Lemma fullb_D0 j : forallb fullb (repeat D0 j) = true.
Proof. induction j; cbn; auto. Qed.

Lemma fullb_app a b : forallb fullb a = true -> forallb fullb b = true -> forallb fullb (a ++ b) = true.
Proof. intros. rewrite forallb_app. apply andb_true_intro. auto. Qed.

Lemma rep_app {X} (x : X) a b : repeat x a ++ repeat x b = repeat x (a + b).
Proof. symmetry. apply repeat_add. Qed.

(* CU: the j blocks nearest the head count from all U0 to all U2 *)
Lemma CU j : forall rest b i,
  runv (3 ^ j - 1) (repeat U0 j ++ rest, b, i) = Some ((repeat U2 j ++ rest, b, i), repeat true (3 ^ j - 1)).
Proof.
  induction j as [|j IH]; intros rest b i; [reflexivity|].
  pose proof (pow3_pos j) as Hp.
  rewrite <-(repeat_snoc U0 j rest), <-(repeat_snoc U2 j rest).
  pose proof (IH (U0 :: rest) b i) as H1.
  assert (H2 : runv 1 (repeat U2 j ++ U0 :: rest, b, i) = Some ((repeat U0 j ++ U1 :: rest, b, i), repeat true 1))
    by (apply runv_one, vis3, visit3_U2; reflexivity).
  pose proof (IH (U1 :: rest) b i) as H3.
  assert (H4 : runv 1 (repeat U2 j ++ U1 :: rest, b, i) = Some ((repeat U0 j ++ U2 :: rest, b, i), repeat true 1))
    by (apply runv_one, vis3, visit3_U2; reflexivity).
  pose proof (IH (U2 :: rest) b i) as H5.
  pose proof (runv_add _ _ _ _ _ _ _ H4 H5) as H45.
  pose proof (runv_add _ _ _ _ _ _ _ H3 H45) as H35.
  pose proof (runv_add _ _ _ _ _ _ _ H2 H35) as H25.
  pose proof (runv_add _ _ _ _ _ _ _ H1 H25) as H.
  rewrite !rep_app in H.
  replace (3 ^ S j - 1) with ((3 ^ j - 1) + (1 + ((3 ^ j - 1) + (1 + (3 ^ j - 1))))) by (cbn; lia).
  exact H.
Qed.

(* CW: a suffix W0 U0^j counts to D0 U2^j *)
Lemma CW j : forall rest b i,
  runv (3 ^ S j - 1) (repeat U0 j ++ W0 :: rest, b, i) =
    Some ((repeat U2 j ++ D0 :: rest, b, i), repeat true (3 ^ S j - 1)).
Proof.
  intros rest b i. pose proof (pow3_pos j) as Hp.
  pose proof (CU j (W0 :: rest) b i) as H1.
  assert (H2 : runv 1 (repeat U2 j ++ W0 :: rest, b, i) = Some ((repeat U0 j ++ W1 :: rest, b, i), repeat true 1))
    by (apply runv_one, vis3, visit3_U2; reflexivity).
  pose proof (CU j (W1 :: rest) b i) as H3.
  assert (H4 : runv 1 (repeat U2 j ++ W1 :: rest, b, i) = Some ((repeat U0 j ++ D0 :: rest, b, i), repeat true 1))
    by (apply runv_one, vis3, visit3_U2; reflexivity).
  pose proof (CU j (D0 :: rest) b i) as H5.
  pose proof (runv_add _ _ _ _ _ _ _ H4 H5) as H45.
  pose proof (runv_add _ _ _ _ _ _ _ H3 H45) as H35.
  pose proof (runv_add _ _ _ _ _ _ _ H2 H35) as H25.
  pose proof (runv_add _ _ _ _ _ _ _ H1 H25) as H.
  rewrite !rep_app in H.
  replace (3 ^ S j - 1) with ((3 ^ j - 1) + (1 + ((3 ^ j - 1) + (1 + (3 ^ j - 1))))) by (cbn; lia).
  exact H.
Qed.

Fixpoint tc (j : nat) : nat :=
  match j with
  | O => 0
  | S O => 2
  | S j' => 3 ^ j + tc j'
  end.

Lemma tc_closed j : 2 * tc (S j) + 5 = 3 ^ S (S j).
Proof.
  induction j as [|j IH]; [reflexivity|].
  change (tc (S (S j))) with (3 ^ S (S j) + tc (S j)). cbn [Nat.pow] in *. lia.
Qed.

(* S3: from U0^j W0 d (d a D block that is not full) to all D *)
Lemma S3 j : forall d d' rest b i, turn d = Some (d', false) ->
  runv (tc (S j) + 1) (repeat U0 j ++ W0 :: d :: rest, b, i) =
    Some ((D2 :: repeat D1 j ++ d' :: rest, b, i), repeat true (tc (S j)) ++ [false]).
Proof.
  induction j as [|j IH]; intros d d' rest b i Hd.
  - pose proof (CW 0 (d :: rest) b i) as H1.
    assert (H2 : runv 1 (repeat U2 0 ++ D0 :: d :: rest, b, i) = Some ((D2 :: d' :: rest, b, i), [false]))
      by (apply runv_one, vis3; cbn; rewrite Hd; reflexivity).
    exact (runv_add _ _ _ _ _ _ _ H1 H2).
  - pose proof (pow3_pos (S (S j))) as Hp.
    pose proof (CW (S j) (d :: rest) b i) as H1.
    assert (H2 : runv 1 (repeat U2 (S j) ++ D0 :: d :: rest, b, i) =
                 Some ((repeat U0 j ++ W0 :: D2 :: d' :: rest, b, i), repeat true 1)).
    { apply runv_one, vis3. rewrite <-repeat_snoc. apply visit3_U2. cbn. rewrite Hd. reflexivity. }
    pose proof (IH D2 D1 (d' :: rest) b i eq_refl) as H3.
    pose proof (runv_add _ _ _ _ _ _ _ H2 H3) as H23.
    pose proof (runv_add _ _ _ _ _ _ _ H1 H23) as H.
    rewrite repeat_snoc, app_assoc, rep_app, app_assoc, rep_app in H.
    change (tc (S (S j))) with (3 ^ S (S j) + tc (S j)).
    replace (3 ^ S (S j) + tc (S j) + 1) with ((3 ^ S (S j) - 1) + (1 + (tc (S j) + 1))) by lia.
    replace (3 ^ S (S j) + tc (S j)) with (3 ^ S (S j) - 1 + 1 + tc (S j)) by lia.
    exact H.
Qed.

(* ---- all-D words count like a plain ternary counter, every exit at phase c ---- *)

Definition isD (s : lab) : bool := match s with D0 | D1 | D2 => true | _ => false end.
Definition dv (s : lab) : nat := match s with D1 => 1 | D0 => 2 | _ => 0 end.
Fixpoint dval (ls : list lab) : nat := match ls with [] => 0 | s :: ls' => dv s + 3 * dval ls' end.
Definition dv1 (b : lab1) : nat := match b with PD1 => 1 | PD0 => 2 | _ => 0 end.
Definition isD1 (b : lab1) : bool := match b with PD0 | PD1 | PD2 => true | _ => false end.

Lemma dval_lt ls : forallb isD ls = true -> dval ls < 3 ^ length ls.
Proof.
  induction ls as [|s ls IH]; cbn; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. specialize (IH H2). destruct s; cbn in *; try discriminate; lia.
Qed.

Lemma dval_max ls : forallb isD ls = true -> dval ls + 1 = 3 ^ length ls -> ls = repeat D0 (length ls).
Proof.
  induction ls as [|s ls IH]; cbn; intros H E; [reflexivity|].
  apply andb_prop in H as [H1 H2]. pose proof (dval_lt ls H2).
  destruct s; cbn in *; try discriminate; try lia. f_equal. apply IH; [exact H2 | lia].
Qed.

Lemma visit3_D ls : forallb isD ls = true -> dval ls + 1 < 3 ^ length ls ->
  exists ls', visit3 ls = Some (ls', false) /\ forallb isD ls' = true /\ dval ls' = dval ls + 1 /\
    length ls' = length ls.
Proof.
  induction ls as [|s ls IH]; cbn; intros H E; [lia|].
  apply andb_prop in H as [H1 H2]. pose proof (dval_lt ls H2).
  destruct s; cbn in H1; try discriminate.
  - assert (E' : dval ls + 1 < 3 ^ length ls) by (cbn in E; lia).
    destruct (IH H2 E') as [ls' [E1 [E2 [E3 E4]]]]. cbn. rewrite E1. cbn.
    exists (D2 :: ls'). cbn. rewrite E2, E3, E4. repeat split; lia.
  - exists (D0 :: ls). cbn. rewrite H2. repeat split; lia.
  - exists (D1 :: ls). cbn. rewrite H2. repeat split; lia.
Qed.

Lemma cb_D0 j : cb (repeat D0 j) false = Some (repeat D2 j, false).
Proof. induction j as [|j IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma isD_D2 j : forallb isD (repeat D2 j) = true.
Proof. induction j; cbn; auto. Qed.

Lemma dval_D2 j : dval (repeat D2 j) = 0.
Proof. induction j; cbn; lia. Qed.

Lemma dval_D1 j : 2 * dval (repeat D1 j) + 1 = 3 ^ j.
Proof. induction j; cbn in *; lia. Qed.

Lemma isD_D1 j : forallb isD (repeat D1 j) = true.
Proof. induction j; cbn; auto. Qed.

Lemma vis_b1 ls b b' p1 ls' p i : forallb fullb ls = true -> turn1 b = Some (b', p1) -> cb ls p1 = Some (ls', p) ->
  vis (ls, b, i) = Some ((ls', b', i), p).
Proof. intros H1 H2 H3. cbn. rewrite (visit3_full _ H1), H1, H2, H3. reflexivity. Qed.

Lemma vis_co ls ls' p i : forallb fullb ls = true -> i < 80 -> cb ls false = Some (ls', p) ->
  vis (ls, PD0, i) = Some ((ls', PD2, S i), p).
Proof.
  intros H1 H2 H3. cbv beta iota zeta delta [vis]. rewrite (visit3_full _ H1), H1. apply Nat.ltb_lt in H2.
  cbv beta iota delta [turn1 lab1_eqb andb]. rewrite H2, H3. reflexivity.
Qed.

Lemma allD n : forall ls b i, forallb isD ls = true -> isD1 b = true ->
  dval ls + 3 ^ length ls * dv1 b + n + 1 = 3 ^ S (length ls) ->
  runv n (ls, b, i) = Some ((repeat D0 (length ls), PD0, i), repeat false n).
Proof.
  induction n as [|n IH]; intros ls b i H1 H2 E; pose proof (dval_lt ls H1) as Hl; cbn [Nat.pow] in E.
  - assert (Eb : b = PD0) by (destruct b; cbn in *; try discriminate; try reflexivity; lia).
    subst b. cbn [dv1] in E. rewrite <-(dval_max ls H1) by lia. reflexivity.
  - destruct (Nat.lt_ge_cases (dval ls + 1) (3 ^ length ls)) as [Hlt|Hge].
    + destruct (visit3_D ls H1 Hlt) as [ls' [E1 [E2 [E3 E4]]]].
      cbn [runv]. rewrite (vis3 _ _ _ b i E1).
      rewrite (IH ls' b i E2 H2) by (rewrite E3, E4; cbn [Nat.pow]; lia). rewrite E4. reflexivity.
    + assert (Hd : dval ls + 1 = 3 ^ length ls) by lia.
      pose proof (dval_max ls H1 Hd) as Hr. remember (length ls) as m eqn:Em. subst ls.
      destruct b; cbn in H2; try discriminate; cbn [dv1] in E; [lia| |].
      * cbn [runv]. rewrite (vis_b1 _ PD1 PD0 false _ _ i (fullb_D0 m) eq_refl (cb_D0 m)).
        rewrite (IH (repeat D2 m) PD0 i (isD_D2 m) eq_refl) by (rewrite dval_D2, repeat_length; cbn; lia).
        rewrite repeat_length. reflexivity.
      * cbn [runv]. rewrite (vis_b1 _ PD2 PD1 false _ _ i (fullb_D0 m) eq_refl (cb_D0 m)).
        rewrite (IH (repeat D2 m) PD1 i (isD_D2 m) eq_refl) by (rewrite dval_D2, repeat_length; cbn; lia).
        rewrite repeat_length. reflexivity.
Qed.

Lemma cyc m i : i < 80 ->
  runv (3 ^ S m) (repeat D0 m, PD0, i) = Some ((repeat D0 m, PD0, S i), repeat false (3 ^ S m)).
Proof.
  intros Hi. pose proof (pow3_pos (S m)) as Hp.
  replace (3 ^ S m) with (1 + (3 ^ S m - 1)) by lia. rewrite repeat_add.
  eapply runv_add; [apply runv_one, (vis_co _ _ _ _ (fullb_D0 m) Hi (cb_D0 m))|].
  pose proof (allD (3 ^ S m - 1) (repeat D2 m) PD2 (S i) (isD_D2 m) eq_refl) as A.
  rewrite dval_D2, repeat_length in A. apply A. cbn [dv1]. lia.
Qed.

Lemma cycs c : forall m i, i + c <= 80 ->
  runv (c * 3 ^ S m) (repeat D0 m, PD0, i) = Some ((repeat D0 m, PD0, i + c), repeat false (c * 3 ^ S m)).
Proof.
  induction c as [|c IH]; intros m i Hi; [rewrite Nat.add_0_r; reflexivity|].
  change (S c * 3 ^ S m) with (3 ^ S m + c * 3 ^ S m).
  rewrite repeat_add. eapply runv_add; [apply cyc; lia|].
  replace (i + S c) with (S i + c) by lia. apply IH. lia.
Qed.

Lemma rep_app_cons {X} (x : X) a b l : repeat x a ++ (repeat x b ++ l) = repeat x (a + b) ++ l.
Proof. rewrite app_assoc, rep_app. reflexivity. Qed.

Lemma odd_pow3 j : exists k, 3 ^ j = 2 * k + 1.
Proof. induction j as [|j [k Hk]]; [exists 0; reflexivity|]. exists (3 * k + 1). cbn [Nat.pow]. lia. Qed.

Lemma half9 j : 2 * ((9 * 3 ^ j + 1) / 2) = 9 * 3 ^ j + 1.
Proof.
  destruct (odd_pow3 j) as [k Hk]. rewrite Hk.
  replace (9 * (2 * k + 1) + 1) with ((9 * k + 5) * 2) by lia. rewrite Nat.div_mul by lia. lia.
Qed.

(* Lemma T: one whole interval of visits, m = K - 1 blocks with m = 3 *)
Lemma interval m : 2 <= m ->
  exists T, 2 * T + 5 = 3 ^ S (S m) /\
  runv (81 * 3 ^ S m - 1) (repeat U0 m, P0, 0) =
    Some ((repeat D0 m, PD0, 80), repeat true T ++ repeat false (81 * 3 ^ S m - 1 - T)).
Proof.
  intros Hm. destruct m as [|[|m]]; [lia|lia|].
  pose proof (half9 (S m)) as Hh.
  set (y := 3 ^ S m) in *.
  assert (Hy : 1 <= y) by apply pow3_pos.
  assert (E3 : 3 ^ S (S m) = 3 * y) by reflexivity.
  assert (E9 : 3 ^ S (S (S m)) = 9 * y) by (cbn [Nat.pow]; unfold y; cbn [Nat.pow]; lia).
  pose proof (tc_closed m) as Etc. rewrite E3 in Etc.
  (* phase 1: block 1 plays the role of W *)
  assert (H1 : runv (3 ^ S (S (S m)) - 1) (repeat U0 (S (S m)), P0, 0) =
               Some ((repeat U2 (S (S m)), PD0, 0), repeat true (3 ^ S (S (S m)) - 1))).
  { pose proof (CU (S (S m)) [] P0 0) as A1. rewrite !app_nil_r in A1.
    assert (A2 : runv 1 (repeat U2 (S (S m)), P0, 0) = Some ((repeat U0 (S (S m)), P1, 0), repeat true 1)).
    { apply runv_one, (vis_b1 _ _ _ true); [apply fullb_U2 | reflexivity |].
      pose proof (cb_U2 (S (S m)) [] true [] eq_refl) as C. rewrite !app_nil_r in C. exact C. }
    pose proof (CU (S (S m)) [] P1 0) as A3. rewrite !app_nil_r in A3.
    assert (A4 : runv 1 (repeat U2 (S (S m)), P1, 0) = Some ((repeat U0 (S (S m)), PD0, 0), repeat true 1)).
    { apply runv_one, (vis_b1 _ _ _ true); [apply fullb_U2 | reflexivity |].
      pose proof (cb_U2 (S (S m)) [] true [] eq_refl) as C. rewrite !app_nil_r in C. exact C. }
    pose proof (CU (S (S m)) [] PD0 0) as A5. rewrite !app_nil_r in A5.
    pose proof (runv_add _ _ _ _ _ _ _ A4 A5) as A45.
    pose proof (runv_add _ _ _ _ _ _ _ A3 A45) as A35.
    pose proof (runv_add _ _ _ _ _ _ _ A2 A35) as A25.
    pose proof (runv_add _ _ _ _ _ _ _ A1 A25) as A.
    rewrite !rep_app in A. rewrite E3 in A. rewrite E9.
    replace (9 * y - 1) with (3 * y - 1 + (1 + (3 * y - 1 + (1 + (3 * y - 1))))) by lia. exact A. }
  (* carry-out 1 *)
  assert (H2 : runv 1 (repeat U2 (S (S m)), PD0, 0) = Some ((repeat U0 (S m) ++ [W0], PD2, 1), repeat true 1)).
  { apply runv_one, vis_co; [apply fullb_U2 | lia |].
    rewrite <-(app_nil_r (repeat U2 (S (S m)))), <-(repeat_snoc U2 (S m) []). apply cb_U2. reflexivity. }
  (* W-suffix of length S (S m) then the turn of block 1 *)
  pose proof (CW (S m) [] PD2 1) as H3.
  assert (H4 : runv 1 (repeat U2 (S m) ++ [D0], PD2, 1) = Some ((repeat U0 m ++ [W0; D2], PD1, 1), repeat true 1)).
  { apply runv_one, (vis_b1 _ _ _ false).
    - apply fullb_app; [apply fullb_U2 | reflexivity].
    - reflexivity.
    - rewrite <-(repeat_snoc U2 m [D0]). apply cb_U2. reflexivity. }
  pose proof (S3 m D2 D1 [] PD1 1 eq_refl) as H5.
  rewrite repeat_snoc, app_nil_r in H5.
  (* all-D counting up to the second carry-out *)
  assert (H6 : runv ((9 * y + 1) / 2) (D2 :: repeat D1 (S m), PD1, 1) =
               Some ((repeat D0 (S (S m)), PD0, 1), repeat false ((9 * y + 1) / 2))).
  { pose proof (dval_D1 (S m)) as Ed. fold y in Ed.
    pose proof (allD ((9 * y + 1) / 2) (D2 :: repeat D1 (S m)) PD1 1 ltac:(cbn; apply isD_D1) eq_refl) as A.
    cbn [length dval dv dv1] in A. rewrite repeat_length in A. apply A.
    rewrite E3, E9. lia. }
  (* 79 more carry-outs in the all-D regime *)
  pose proof (cycs 79 (S (S m)) 1 ltac:(lia)) as H7. rewrite E9 in H7.
  pose proof (runv_add _ _ _ _ _ _ _ H6 H7) as H67.
  pose proof (runv_add _ _ _ _ _ _ _ H5 H67) as H57.
  pose proof (runv_add _ _ _ _ _ _ _ H4 H57) as H47.
  pose proof (runv_add _ _ _ _ _ _ _ H3 H47) as H37.
  pose proof (runv_add _ _ _ _ _ _ _ H2 H37) as H27.
  pose proof (runv_add _ _ _ _ _ _ _ H1 H27) as H.
  rewrite rep_app, <-app_assoc in H. change [false] with (repeat false 1) in H.
  rewrite rep_app, !rep_app_cons in H. rewrite E3, E9 in H.
  assert (E27 : 3 ^ S (S (S (S m))) = 27 * y) by (unfold y; cbn [Nat.pow]; lia).
  exists (9 * y - 1 + 1 + (3 * y - 1) + 1 + tc (S m)). split; [rewrite E27; lia|].
  rewrite E9.
  replace (81 * (9 * y) - 1)
    with (9 * y - 1 + (1 + (3 * y - 1 + (1 + (tc (S m) + 1 + ((9 * y + 1) / 2 + 79 * (9 * y)))))))
    by lia.
  rewrite H.
  replace (9 * y - 1 + (1 + (3 * y - 1 + (1 + (tc (S m) + 1 + ((9 * y + 1) / 2 + 79 * (9 * y))))))
           - (9 * y - 1 + 1 + (3 * y - 1) + 1 + tc (S m)))
    with (1 + ((9 * y + 1) / 2 + 79 * (9 * y))) by lia.
  reflexivity.
Qed.

(* the chain side of one interval, on the machine *)
Lemma interval_tm m nus R R' : 2 <= m -> length nus = m ->
  (forall T, 2 * T + 5 = 3 ^ S (S m) -> EpSeq (repeat true T ++ repeat false (81 * 3 ^ S m - 1 - T)) R R') ->
  Gc (repeat U0 m, P0, 0) nus R -->* Gc (repeat D0 m, PD0, 80) nus R'.
Proof.
  intros Hm Hl HE. destruct (interval m Hm) as [T [ET Hr]].
  apply (runv_spec _ _ _ _ _ _ _ Hr); [cbn; rewrite repeat_length; auto | apply HE, ET].
Qed.

(* the record visit: carry-out at all D0, left episode 80 (the left record), carry back to all D2 *)
Lemma record_visit m nus R : length nus = m ->
  Gc (repeat D0 m, PD0, 80) nus R -->+ chs (repeat D2 m) nus (b1s PD2 (LWs 81)) {{B}}> R.
Proof.
  intros Hl. cbn [Gc].
  eapply evstep_progress_trans; [apply pass_spec; [apply fullb_D0 | rewrite repeat_length; auto]|].
  unfold b1s. eapply progress_trans; [apply blk1_pass|].
  eapply progress_trans; [apply lw_ep; lia|].
  eapply progress_evstep_trans; [apply blk1_back|].
  apply (cb_spec _ false _ false); [apply cb_D0 | rewrite repeat_length; auto].
Qed.

(* ===================================================================== *)
(* The right region: a verified symbolic executor for interval programs. *)
(* ===================================================================== *)

(* run the simulator until it is stuck (or out of fuel) *)
Fixpoint urun (p : positive) (c : cfg) : cfg * bool :=
  match p with
  | xH => match sstep c with Some (c', _) => (c', false) | None => (c, true) end
  | xO p' => let '(c1, s1) := urun p' c in if s1 then (c1, true) else urun p' c1
  | xI p' =>
    match sstep c with
    | Some (c0, _) => let '(c1, s1) := urun p' c0 in if s1 then (c1, true) else urun p' c1
    | None => (c, true)
    end
  end.

Lemma sstep_ev nu sg c c' b : sstep c = Some (c', b) -> ev_cfg nu sg c -->* ev_cfg nu sg c'.
Proof.
  intros E. pose proof (sstep_spec nu sg _ _ _ E) as H. destruct b; cbn in H; [apply progress_evstep|]; exact H.
Qed.

Lemma urun_spec p : forall c nu sg, ev_cfg nu sg c -->* ev_cfg nu sg (fst (urun p c)).
Proof.
  induction p as [p IH|p IH|]; intros c nu sg; cbn [urun].
  - destruct (sstep c) as [[c0 b]|] eqn:E; [|apply evstep_refl].
    pose proof (sstep_ev nu sg _ _ _ E) as H0.
    pose proof (IH c0 nu sg) as H1. destruct (urun p c0) as [c1 s1]. cbn [fst] in H1.
    destruct s1; cbn [fst].
    + eapply evstep_trans; eassumption.
    + eapply evstep_trans; [eassumption|]. eapply evstep_trans; [exact H1|]. apply IH.
  - pose proof (IH c nu sg) as H1. destruct (urun p c) as [c1 s1]. cbn [fst] in H1.
    destruct s1; cbn [fst]; [exact H1|]. eapply evstep_trans; [exact H1|]. apply IH.
  - destruct (sstep c) as [[c0 b]|] eqn:E; cbn [fst]; [|apply evstep_refl].
    exact (sstep_ev nu sg _ _ _ E).
Qed.

Definition tgtD (c : cfg) : option (list run) :=
  match c with
  | Lc D ([], TV O) (rr, T0) => Some rr
  | _ => None
  end.

Lemma tgtD_spec c rr : tgtD c = Some rr -> c = Lc D ([], TV 0) (rr, T0).
Proof.
  unfold tgtD. destruct c as [q l r|q [l t] [r t']]; [discriminate|].
  destruct q; try discriminate. destruct l; try discriminate.
  destruct t as [|[|k]]; try discriminate. destruct t'; try discriminate.
  intros H; inversion H; subst; reflexivity.
Qed.

Definition evR (nu : list N) (rr : list run) : side := ev_runs nu rr (const S0).

(* one episode of the right region, entered at phase p, the chain side abstract *)
Definition ep_run (p : bool) (rr : list run) : option (list run) :=
  tgtD (fst (urun 50000 (Rc (stp p) ([], TV 0) (rr, T0)))).

Lemma ep_run_spec p rr rr' : ep_run p rr = Some rr' -> forall nu, Ep p (evR nu rr) (evR nu rr').
Proof.
  unfold ep_run. intros H nu l.
  pose proof (urun_spec 50000 (Rc (stp p) ([], TV 0) (rr, T0)) nu (fun _ => l)) as U.
  destruct (urun 50000 (Rc (stp p) ([], TV 0) (rr, T0))) as [c s]. cbn [fst] in H, U.
  apply tgtD_spec in H. subst c. exact U.
Qed.

Fixpoint eps (ps : list bool) (rr : list run) : option (list run) :=
  match ps with
  | [] => Some rr
  | p :: ps' => match ep_run p rr with Some rr' => eps ps' rr' | None => None end
  end.

Lemma eps_spec ps : forall rr rr', eps ps rr = Some rr' -> forall nu, EpSeq ps (evR nu rr) (evR nu rr').
Proof.
  induction ps as [|p ps IH]; intros rr rr' H nu; cbn in H.
  - inversion H; reflexivity.
  - destruct (ep_run p rr) as [r1|] eqn:E; [|discriminate].
    exists (evR nu r1). split; [apply (ep_run_spec _ _ _ E) | apply (IH _ _ H)].
Qed.

Lemma EpSeq_app a : forall b R R1 R2, EpSeq a R R1 -> EpSeq b R1 R2 -> EpSeq (a ++ b) R R2.
Proof.
  induction a as [|p a IH]; intros b R R1 R2 H1 H2; cbn in *.
  - subst. exact H2.
  - destruct H1 as [R3 [H3 H4]]. exists R3. split; [exact H3 | apply (IH _ _ _ _ H4 H2)].
Qed.

(* ---- linear-form algebra ---- *)

Definition evN (nu : list N) (a : lf) : N := (lc a + dot (lv a) nu)%N.

Lemma dot_zadd2 v : forall a b, dot v (zadd a b) = (dot v a + dot v b)%N.
Proof.
  induction v as [|x v IH]; intros [|y a] [|z b]; cbn; try lia.
  rewrite IH. lia.
Qed.

Definition vscale (k : N) (w : list N) : list N := map (N.mul k) w.

Lemma dot_vscale v : forall k w, dot v (vscale k w) = (k * dot v w)%N.
Proof. unfold vscale. induction v as [|x v IH]; intros k [|y w]; cbn; try lia. rewrite IH. lia. Qed.

Lemma ev_runs_dot nu nu' T X : (forall v, dot v nu = dot v nu') -> ev_runs nu T X = ev_runs nu' T X.
Proof.
  intros H. induction T as [|[b a] T IH]; cbn; [reflexivity|]. unfold ev. rewrite H, IH. reflexivity.
Qed.

Definition subst_lf (w : list N) (a : lf) : lf := LF (lc a + dot (lv a) w) (lv a).
Definition subst_runs (w : list N) (T : list run) : list run := map (fun r => (fst r, subst_lf w (snd r))) T.

Lemma ev_runs_subst nu w T X : ev_runs nu (subst_runs w T) X = ev_runs (zadd nu w) T X.
Proof.
  unfold subst_runs. induction T as [|[b a] T IH]; cbn; [reflexivity|]. rewrite IH. unfold ev, subst_lf. cbn.
  rewrite dot_zadd2. f_equal. f_equal. lia.
Qed.

Definition lf_scale (k : N) (a : lf) : lf := LF (k * lc a) (map (N.mul k) (lv a)).

Lemma dot_scale_l vs : forall k nu, dot (map (N.mul k) vs) nu = (k * dot vs nu)%N.
Proof. induction vs as [|x vs IH]; intros k [|y nu]; cbn; try lia. rewrite IH. lia. Qed.

Lemma evN_add nu a b : evN nu (lf_add a b) = (evN nu a + evN nu b)%N.
Proof. unfold evN, lf_add. cbn. rewrite dot_zadd. lia. Qed.

Lemma evN_scale nu k a : evN nu (lf_scale k a) = (k * evN nu a)%N.
Proof. unfold evN, lf_scale. cbn. rewrite dot_scale_l. lia. Qed.

Fixpoint comp_aux (vs : list N) (sg : list lf) : lf :=
  match vs, sg with
  | v :: vs', s :: sg' => lf_add (lf_scale v s) (comp_aux vs' sg')
  | _, _ => LF 0 []
  end.
Definition compose_lf (sg : list lf) (a : lf) : lf := lf_add (LF (lc a) []) (comp_aux (lv a) sg).
Definition comp_runs (sg : list lf) (T : list run) : list run := map (fun r => (fst r, compose_lf sg (snd r))) T.

Lemma evN_comp_aux nu vs : forall sg, evN nu (comp_aux vs sg) = dot vs (map (evN nu) sg).
Proof.
  induction vs as [|v vs IH]; intros [|s sg]; cbn [comp_aux map dot]; try reflexivity.
  rewrite evN_add, evN_scale, IH. lia.
Qed.

Lemma evN_compose nu sg a : evN nu (compose_lf sg a) = evN (map (evN nu) sg) a.
Proof. unfold compose_lf. rewrite evN_add, evN_comp_aux. unfold evN at 1 3. cbn. lia. Qed.

Lemma ev_runs_comp nu sg T X : ev_runs nu (comp_runs sg T) X = ev_runs (map (evN nu) sg) T X.
Proof.
  unfold comp_runs. induction T as [|[b a] T IH]; cbn; [reflexivity|]. rewrite IH. unfold ev.
  change (lc (compose_lf sg a) + dot (lv (compose_lf sg a)) nu)%N with (evN nu (compose_lf sg a)).
  rewrite evN_compose. reflexivity.
Qed.

(* ---- the 4-cycle jump (Lemma J) ---- *)

Lemma jump_lemma T p dec inc :
  (forall nu, EpSeq [p; p; p; p] (evR nu (subst_runs dec T)) (evR nu (subst_runs inc T))) ->
  forall k nu, EpSeq (repeat p (4 * k)) (evR (zadd nu (vscale (N.of_nat k) dec)) T)
                                        (evR (zadd nu (vscale (N.of_nat k) inc)) T).
Proof.
  intros Hc k. induction k as [|k IH]; intros nu.
  - cbn [repeat Nat.mul EpSeq]. unfold evR. apply ev_runs_dot. intros v.
    rewrite !dot_zadd2, !dot_vscale. lia.
  - replace (4 * S k) with (4 + 4 * k) by lia. rewrite repeat_add.
    apply (EpSeq_app _ _ _ (evR (zadd (zadd nu inc) (vscale (N.of_nat k) dec)) T)).
    + specialize (Hc (zadd nu (vscale (N.of_nat k) dec))). unfold evR in *.
      rewrite !ev_runs_subst in Hc.
      replace (ev_runs (zadd nu (vscale (N.of_nat (S k)) dec)) T (const S0))
        with (ev_runs (zadd (zadd nu (vscale (N.of_nat k) dec)) dec) T (const S0))
        by (apply ev_runs_dot; intros v; rewrite !dot_zadd2, !dot_vscale; lia).
      replace (ev_runs (zadd (zadd nu inc) (vscale (N.of_nat k) dec)) T (const S0))
        with (ev_runs (zadd (zadd nu (vscale (N.of_nat k) dec)) inc) T (const S0))
        by (apply ev_runs_dot; intros v; rewrite !dot_zadd2; lia).
      exact Hc.
    + specialize (IH (zadd nu inc)). unfold evR in *.
      replace (ev_runs (zadd nu (vscale (N.of_nat (S k)) inc)) T (const S0))
        with (ev_runs (zadd (zadd nu inc) (vscale (N.of_nat k) inc)) T (const S0))
        by (apply ev_runs_dot; intros v; rewrite !dot_zadd2, !dot_vscale; lia).
      replace (ev_runs (zadd (zadd nu inc) (vscale (N.of_nat k) dec)) T (const S0))
        with (ev_runs (zadd (zadd nu inc) (vscale (N.of_nat k) dec)) T (const S0)) by reflexivity.
      exact IH.
Qed.

(* ---- building a jump from the actual configuration ---- *)

Definition uvar (i : nat) (c : N) : lf := LF c (repeat 0%N i ++ [4%N]).

Fixpoint zsub (a b : list N) : list N :=
  match a, b with
  | x :: a', y :: b' => (x - y)%N :: zsub a' b'
  | _, [] => a
  | [], _ => []
  end.

Fixpoint mk_jump (i : nat) (rr rr4 : list run) (c : lf) : option (list run * list N * list N * list lf) :=
  match rr, rr4 with
  | [], [] => Some ([], [], [], [])
  | (b, a) :: rr', (b4, a4) :: rr4' =>
    if negb (seqb b b4) then None else
    if negb (listN_eqb (strip0 (lv a)) (strip0 (lv a4))) then None else
    match mk_jump (S i) rr' rr4' c with
    | None => None
    | Some (T, dec, inc, sg) =>
      let d := (Z.of_N (lc a4) - Z.of_N (lc a))%Z in
      if negb (Z.eqb (Z.modulo d 4) 0) then None else
      let q := Z.div d 4 in
      if andb (allz (lv a)) (Z.eqb q 0) then
        Some ((b, a) :: T, 0%N :: dec, 0%N :: inc, LF 0 [] :: sg)
      else if Z.ltb q 0 then
        let dn := Z.to_N (- q) in
        let M := (lc a - 4 * dn * lc c)%N in
        let s := LF 0 (map (fun x => x / 4)%N (zsub (lv a) (map (N.mul (4 * dn)) (lv c)))) in
        Some ((b, uvar i M) :: T, dn :: dec, 0%N :: inc, s :: sg)
      else
        let s := LF 0 (map (fun x => x / 4)%N (lv a)) in
        Some ((b, uvar i (lc a)) :: T, 0%N :: dec, Z.to_N q :: inc, s :: sg)
    end
  | _, _ => None
  end.

Fixpoint mapadd (c : lf) (sg : list lf) (w : list N) : list lf :=
  match sg, w with
  | s :: sg', x :: w' => lf_add s (lf_scale x c) :: mapadd c sg' w'
  | _, _ => []
  end.

Lemma mapadd_ev nu c sg : forall w, length sg = length w ->
  map (evN nu) (mapadd c sg w) = zadd (map (evN nu) sg) (vscale (evN nu c) w).
Proof.
  induction sg as [|s sg IH]; intros [|x w] Hl; cbn in Hl; try discriminate; [reflexivity|].
  cbn [mapadd map vscale zadd]. injection Hl as Hl. rewrite (IH w Hl). unfold vscale.
  f_equal. rewrite evN_add, evN_scale. lia.
Qed.

Definition cyc4 (p : bool) : list bool := [p; p; p; p].

Definition jump_run (p : bool) (c : lf) (rr : list run) : option (list run) :=
  match eps (cyc4 p) rr with
  | None => None
  | Some rr4 =>
    match mk_jump 0 rr rr4 c with
    | None => None
    | Some (T, dec, inc, sg) =>
      if andb (Nat.eqb (length sg) (length dec)) (Nat.eqb (length sg) (length inc)) then
        match eps (cyc4 p) (subst_runs dec T) with
        | None => None
        | Some X =>
          if andb (runs_eqb X (subst_runs inc T)) (runs_eqb rr (comp_runs (mapadd c sg dec) T))
          then Some (comp_runs (mapadd c sg inc) T) else None
        end
      else None
    end
  end.

Lemma jump_run_spec p c rr rr' : jump_run p c rr = Some rr' ->
  forall nu, EpSeq (repeat p (4 * ev nu c)) (evR nu rr) (evR nu rr').
Proof.
  unfold jump_run. intros H nu.
  destruct (eps (cyc4 p) rr) as [rr4|]; [|discriminate].
  destruct (mk_jump 0 rr rr4 c) as [[[[T dec] inc] sg]|]; [|discriminate].
  destruct (andb (Nat.eqb (length sg) (length dec)) (Nat.eqb (length sg) (length inc))) eqn:El; [|discriminate].
  apply andb_prop in El as [El1 El2]. apply Nat.eqb_eq in El1, El2.
  destruct (eps (cyc4 p) (subst_runs dec T)) as [X|] eqn:EX; [|discriminate].
  destruct (andb (runs_eqb X (subst_runs inc T)) (runs_eqb rr (comp_runs (mapadd c sg dec) T))) eqn:Ec;
    [|discriminate].
  apply andb_prop in Ec as [Ec1 Ec2]. inversion H; subst rr'; clear H.
  assert (Hc : forall nu', EpSeq [p; p; p; p] (evR nu' (subst_runs dec T)) (evR nu' (subst_runs inc T))).
  { intros nu'. pose proof (eps_spec _ _ _ EX nu') as HX. unfold evR in *.
    rewrite <-(runs_eqb_ev nu' _ _ (const S0) Ec1). exact HX. }
  pose proof (jump_lemma T p dec inc Hc (ev nu c) (map (evN nu) sg)) as J.
  unfold ev in J at 2 3. rewrite N2Nat.id in J.
  unfold evR in *. rewrite (runs_eqb_ev nu _ _ (const S0) Ec2), !ev_runs_comp, !mapadd_ev by assumption.
  exact J.
Qed.

(* ---- programs: single episodes and jumps ---- *)

Inductive instr := ISingle (p : bool) | IJump (p : bool) (c : lf).

Definition seg : Type := (bool * lf)%type.

Fixpoint segs_ev (nu : list N) (ss : list seg) : list bool :=
  match ss with [] => [] | (p, n) :: ss' => repeat p (ev nu n) ++ segs_ev nu ss' end.

Fixpoint exec (prog : list instr) (rr : list run) : option (list run * list seg) :=
  match prog with
  | [] => Some (rr, [])
  | ISingle p :: prog' =>
    match ep_run p rr with
    | Some rr1 => match exec prog' rr1 with Some (rr2, ss) => Some (rr2, (p, cn 1) :: ss) | None => None end
    | None => None
    end
  | IJump p c :: prog' =>
    match jump_run p c rr with
    | Some rr1 => match exec prog' rr1 with Some (rr2, ss) => Some (rr2, (p, lf_scale 4 c) :: ss) | None => None end
    | None => None
    end
  end.

Lemma ev_scale4 nu c : ev nu (lf_scale 4 c) = 4 * ev nu c.
Proof. unfold ev. change (lc (lf_scale 4 c) + dot (lv (lf_scale 4 c)) nu)%N with (evN nu (lf_scale 4 c)).
  rewrite evN_scale. unfold evN. lia. Qed.

Lemma exec_spec prog : forall rr rr' ss, exec prog rr = Some (rr', ss) ->
  forall nu, EpSeq (segs_ev nu ss) (evR nu rr) (evR nu rr').
Proof.
  induction prog as [|[p|p c] prog IH]; intros rr rr' ss H nu; cbn [exec] in H.
  - inversion H; subst. reflexivity.
  - destruct (ep_run p rr) as [rr1|] eqn:E1; [|discriminate].
    destruct (exec prog rr1) as [[rr2 ss2]|] eqn:E2; [|discriminate].
    inversion H; subst; clear H. cbn [segs_ev].
    replace (ev nu (cn 1)) with 1 by reflexivity. cbn [repeat app].
    exists (evR nu rr1). split; [apply (ep_run_spec _ _ _ E1) | apply (IH _ _ _ E2)].
  - destruct (jump_run p c rr) as [rr1|] eqn:E1; [|discriminate].
    destruct (exec prog rr1) as [[rr2 ss2]|] eqn:E2; [|discriminate].
    inversion H; subst; clear H. cbn [segs_ev]. rewrite ev_scale4.
    apply (EpSeq_app _ _ _ (evR nu rr1)); [apply (jump_run_spec _ _ _ _ E1) | apply (IH _ _ _ E2)].
Qed.

(* the phase sequence of a program: all c_K + 2 episodes first, then all c_K episodes *)
Fixpoint sum_ph (p : bool) (ss : list seg) : lf :=
  match ss with
  | [] => LF 0 []
  | (q, n) :: ss' => if Bool.eqb p q then lf_add n (sum_ph p ss') else sum_ph p ss'
  end.
Fixpoint split_ok (seen_false : bool) (ss : list seg) : bool :=
  match ss with
  | [] => true
  | (true, _) :: ss' => andb (negb seen_false) (split_ok false ss')
  | (false, _) :: ss' => split_ok true ss'
  end.

Lemma ev_lf_add nu a b : ev nu (lf_add a b) = ev nu a + ev nu b.
Proof. apply ev_add. Qed.

Lemma split_false ss nu : split_ok true ss = true -> segs_ev nu ss = repeat false (ev nu (sum_ph false ss)).
Proof.
  induction ss as [|[q n] ss IH]; intros H; [reflexivity|].
  destruct q; cbn in H; [discriminate|]. cbn [segs_ev sum_ph Bool.eqb]. rewrite ev_lf_add, repeat_add, IH by exact H.
  reflexivity.
Qed.

Lemma sum_false_true ss : split_ok true ss = true -> sum_ph true ss = LF 0 [] \/ True.
Proof. auto. Qed.

Lemma split_spec ss nu : split_ok false ss = true ->
  segs_ev nu ss = repeat true (ev nu (sum_ph true ss)) ++ repeat false (ev nu (sum_ph false ss)).
Proof.
  induction ss as [|[q n] ss IH]; intros H; [reflexivity|].
  destruct q.
  - cbn in H. cbn [segs_ev sum_ph Bool.eqb]. rewrite ev_lf_add, repeat_add, IH by exact H. rewrite app_assoc. reflexivity.
  - cbn in H. cbn [segs_ev sum_ph Bool.eqb]. rewrite split_false by exact H.
    assert (Et : ev nu (sum_ph true ((false, n) :: ss)) = 0).
    { clear IH. cbn [sum_ph Bool.eqb]. revert H. induction ss as [|[q m] ss IH2]; intros H; [reflexivity|].
      destruct q; cbn in H; [discriminate|]. cbn [sum_ph Bool.eqb]. apply IH2, H. }
    cbn [sum_ph Bool.eqb] in Et. rewrite Et. cbn [repeat app]. rewrite ev_lf_add, repeat_add. reflexivity.
Qed.

Definition prog_check (prog : list instr) (rs re : list run) (T F : lf) : bool :=
  match exec prog rs with
  | Some (re', ss) =>
    andb (andb (runs_eqb re' re) (split_ok false ss)) (andb (lf_eqb (sum_ph true ss) T) (lf_eqb (sum_ph false ss) F))
  | None => false
  end.

Lemma prog_check_spec prog rs re T F : prog_check prog rs re T F = true ->
  forall nu, EpSeq (repeat true (ev nu T) ++ repeat false (ev nu F)) (evR nu rs) (evR nu re).
Proof.
  unfold prog_check. intros H nu.
  destruct (exec prog rs) as [[re' ss]|] eqn:E; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H2 as [H2 H4].
  pose proof (exec_spec _ _ _ _ E nu) as HE. rewrite (split_spec _ _ H3) in HE.
  rewrite (lf_eqb_ev nu _ _ H2), (lf_eqb_ev nu _ _ H4) in HE.
  unfold evR in *. rewrite <-(runs_eqb_ev nu _ _ (const S0) H1). exact HE.
Qed.

(* ===================================================================== *)
(* The six interval programs (Appendix B of the write-up), u = 1 + 8 t.   *)
(* ===================================================================== *)

Definition tl1 (c a : N) : lf := LF c [a].
Definition Rs_r5 : list run := mkruns S0 [tl1 224492 1796256; tl1 673559 5388768; cn 8; tl1 9836 78732; tl1 1942069 15536448]%N.
Definition prog_r5 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 817 6561)] ++ repeat (ISingle true) 6 ++ repeat (ISingle false) 13 ++ [IJump false (tl1 43462 347733)] ++ repeat (ISingle false) 7.
Definition Rs_r0 : list run := mkruns S0 [tl1 74804 598752; tl1 224495 1796256; tl1 673560 5388768; tl1 2020752 16166304; cn 4; tl1 521610 4172796; cn 1]%N.
Definition prog_r0 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 817 6561)] ++ repeat (ISingle true) 6 ++ repeat (ISingle false) 9 ++ [IJump false (tl1 43463 347733)] ++ repeat (ISingle false) 7.
Definition Rs_r1 : list run := mkruns S0 [tl1 2020748 16166304; cn 7; tl1 551120 4408992; tl1 1564809 12518388; cn 2]%N.
Definition prog_r1 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 2457 19683)] ++ repeat (ISingle true) 7 ++ repeat (ISingle false) 5 ++ [IJump false (tl1 130398 1043199)] ++ repeat (ISingle false) 4.
Definition Rs_r2 : list run := mkruns S0 [tl1 8276 66528; tl1 24911 199584; tl1 74808 598752; tl1 224496 1796256; tl1 673559 5388768; tl1 2020751 16166304; cn 8; tl1 29514 236196; tl1 5826224 46609344; cn 2]%N.
Definition prog_r2 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 817 6561)] ++ repeat (ISingle true) 6 ++ repeat (ISingle false) 8 ++ [IJump false (tl1 43464 347733)] ++ repeat (ISingle false) 4.
Definition Rs_r3 : list run := mkruns S0 [tl1 224492 1796256; tl1 673559 5388768; tl1 2020752 16166304; tl1 6062328 48498912; cn 4; tl1 1564810 12518388]%N.
Definition prog_r3 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 2457 19683)] ++ repeat (ISingle true) 7 ++ repeat (ISingle false) 9 ++ [IJump false (tl1 130397 1043199)] ++ repeat (ISingle false) 4.
Definition Rs_r4 : list run := mkruns S0 [tl1 74804 598752; tl1 224495 1796256; tl1 673560 5388768; tl1 2020752 16166304; tl1 6062327 48498912; cn 7; tl1 1653368 13226976; tl1 4694422 37555164; cn 1]%N.
Definition prog_r4 : list instr := repeat (ISingle true) 4 ++ [IJump true (tl1 2457 19683)] ++ repeat (ISingle true) 7 ++ repeat (ISingle false) 6 ++ [IJump false (tl1 130397 1043199)] ++ repeat (ISingle false) 7.
Definition Re_r5 : list run := [(S0, tl1 224492 1796256); (S1, tl1 673560 5388768); (S0, tl1 2020752 16166304); (S1, cn 4); (S0, tl1 521602 4172796)]%N.
Lemma int_r5 : prog_check prog_r5 Rs_r5 Re_r5 (tl1 3278 26244) (tl1 173868 1390932) = true.
Proof. vm_compute. reflexivity. Qed.
Definition Re_r0 : list run := [(S0, tl1 74804 598752); (S1, tl1 224496 1796256); (S0, tl1 673560 5388768); (S1, tl1 2020751 16166304); (S1, cn 7); (S1, tl1 551120 4408992); (S0, tl1 1564798 12518388); (S1, cn 1)]%N.
Lemma int_r0 : prog_check prog_r0 Rs_r0 Re_r0 (tl1 3278 26244) (tl1 173868 1390932) = true.
Proof. vm_compute. reflexivity. Qed.
Definition Re_r1 : list run := [(S0, tl1 2020748 16166304); (S1, cn 8); (S0, tl1 29521 236196); (S0, tl1 5826161 46609344); (S0, cn 2)]%N.
Lemma int_r1 : prog_check prog_r1 Rs_r1 Re_r1 (tl1 9839 78732) (tl1 521601 4172796) = true.
Proof. vm_compute. reflexivity. Qed.
Definition Re_r2 : list run := [(S0, tl1 8276 66528); (S1, tl1 24912 199584); (S0, tl1 74808 598752); (S1, tl1 224495 1796256); (S1, tl1 673559 5388768); (S1, tl1 2020752 16166304); (S0, tl1 6062328 48498912); (S1, cn 3); (S1, tl1 1564801 12518388); (S1, cn 1)]%N.
Lemma int_r2 : prog_check prog_r2 Rs_r2 Re_r2 (tl1 3278 26244) (tl1 173868 1390932) = true.
Proof. vm_compute. reflexivity. Qed.
Definition Re_r3 : list run := [(S0, tl1 224492 1796256); (S1, tl1 673560 5388768); (S0, tl1 2020752 16166304); (S1, tl1 6062327 48498912); (S1, cn 7); (S1, tl1 1653368 13226976); (S0, tl1 4694397 37555164); (S0, cn 2)]%N.
Lemma int_r3 : prog_check prog_r3 Rs_r3 Re_r3 (tl1 9839 78732) (tl1 521601 4172796) = true.
Proof. vm_compute. reflexivity. Qed.
Definition Re_r4 : list run := [(S0, tl1 74804 598752); (S1, tl1 224496 1796256); (S0, tl1 673560 5388768); (S1, tl1 2020751 16166304); (S1, tl1 6062327 48498912); (S1, cn 7); (S1, tl1 88573 708588); (S1, tl1 17478488 139828032); (S0, cn 2)]%N.
Lemma int_r4 : prog_check prog_r4 Rs_r4 Re_r4 (tl1 9839 78732) (tl1 521601 4172796) = true.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* The regrouping after the record visit (write-up 6.2): the chain in D2 *)
(* is the same tape as a chain in U0 grouped one defect later.          *)
(* ===================================================================== *)

Definition rtop (qs : list (list N)) (z : N) : N :=
  match qs with [] => z | q :: _ => nth 0 q 0%N end.

Fixpoint rshift (qs : list (list N)) (z : N) : list (list N) :=
  match qs with
  | [] => []
  | q :: qs' => [nth 1 q 0; nth 2 q 0; nth 3 q 0; rtop qs' z]%N :: rshift qs' z
  end.

Lemma shift_len qs z : length (rshift qs z) = length qs.
Proof. induction qs; cbn; congruence. Qed.

Lemma dot4 (a b c d : N) q :
  dot [a; b; c; d] q = (a * nth 0 q 0 + b * nth 1 q 0 + c * nth 2 q 0 + d * nth 3 q 0)%N.
Proof. destruct q as [|x0 [|x1 [|x2 [|x3 q]]]]; cbn; lia. Qed.

Lemma alt_split b m k : Nat.eqb (m mod 2) 0 = true -> alt b (m + k) = alt b m ++ alt b k.
Proof.
  intros H. rewrite alt_add. unfold afterb_nat. rewrite H. reflexivity.
Qed.

Lemma ev_q nu c a : ev nu (LF c a) = N.to_nat (c + dot a nu).
Proof. reflexivity. Qed.

Lemma regroup qs : forall z X X',
  X = alt S0 1 *> (alt S0 (2 + 4 * N.to_nat z) *> X') ->
  chs (repeat D2 (length qs)) qs X =
    alt S0 1 *> (alt S0 (2 + 4 * N.to_nat (rtop qs z)) *> chs (repeat U0 (length qs)) (rshift qs z) X').
Proof.
  induction qs as [|q qs IH]; intros z X X' HX; [exact HX|].
  cbn [length repeat chs rshift rtop]. rewrite (IH z X X' HX).
  set (Y := chs (repeat U0 (length qs)) (rshift qs z) X').
  change (blk D2) with [(S0, cn 1); (S0, vt 5); (S0, vs 4); (S1, va 4); (S0, vl 0)]%N.
  change (blk U0) with [(S0, cn 3); (S0, vt 4); (S1, vs 4); (S0, va 1); (S0, vl 2)]%N.
  cbn [ev_runs]. unfold ev, vt, vs, va, vl, cn. cbn [lc lv]. rewrite !dot4. cbn [nth dot].
  set (xt := nth 0 q 0%N). set (xs := nth 1 q 0%N). set (xa := nth 2 q 0%N). set (xI := nth 3 q 0%N).
  set (tz := rtop qs z).
  assert (E1 : alt S0 (N.to_nat (5 + (4 * xt + 0 * xs + 0 * xa + 0 * xI))) = alt S0 (2 + 4 * N.to_nat xt) ++ alt S0 3).
  { replace (N.to_nat (5 + (4 * xt + 0 * xs + 0 * xa + 0 * xI))) with ((2 + 4 * N.to_nat xt) + 3) by lia.
    apply alt_split. apply Nat.eqb_eq. replace (2 + 4 * N.to_nat xt) with (2 + N.to_nat xt * 2 * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (E2 : alt S0 (N.to_nat (1 + (0 * xs + 0 * xa + 4 * xI + 0 * tz))) = alt S0 (N.to_nat (0 + (0 * xt + 0 * xs + 0 * xa + 4 * xI))) ++ alt S0 1).
  { replace (N.to_nat (1 + (0 * xs + 0 * xa + 4 * xI + 0 * tz))) with (N.to_nat (0 + (0 * xt + 0 * xs + 0 * xa + 4 * xI)) + 1) by lia.
    apply alt_split. apply Nat.eqb_eq. replace (N.to_nat (0 + (0 * xt + 0 * xs + 0 * xa + 4 * xI))) with (0 + N.to_nat xI * 2 * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  rewrite E1, E2, !Str_app_assoc. cbn [alt Str_app app].
  replace (N.to_nat (2 + (0 * xs + 0 * xa + 0 * xI + 4 * tz))) with (2 + 4 * N.to_nat tz) by lia.
  replace (N.to_nat (4 + (4 * xs + 0 * xa + 0 * xI + 0 * tz))) with (N.to_nat (4 + (0 * xt + 4 * xs + 0 * xa + 0 * xI))) by lia.
  replace (N.to_nat (4 + (0 * xs + 4 * xa + 0 * xI + 0 * tz))) with (N.to_nat (4 + (0 * xt + 0 * xs + 4 * xa + 0 * xI))) by lia.
  reflexivity.
Qed.

(* block 1 and the left word after the left record, regrouped *)
Lemma regroup_b1 : b1s PD2 (LWs 81) = alt S0 1 *> (alt S0 (2 + 4 * N.to_nat 0) *> b1s P0 (LWs 0)).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* Lemma S: one record interval, class by class.                         *)
(* ===================================================================== *)

Lemma drop_step L Re Rs nu X' :
  reach 100000 (Rc B (L, TV 0) (Re, T0)) (Lc D ([], TV 0) (Rs, T0)) = true ->
  ev_runs nu L X' {{B}}> evR nu Re -->+ X' <{{D}} evR nu Rs.
Proof. intros H. exact (reach_spec _ _ _ H nu (fun _ => X')). Qed.

Definition W5t (t : N) : N := (18701 + 149688 * t)%N.
Definition W5s (t : N) : N := (6227 + 49896 * t)%N.
Definition W5a (t : N) : N := (2069 + 16632 * t)%N.

Lemma rec_r5_ok : reach 100000 (Rc B ([(S0, cn 1); (S0, tl1 74806 598752)], TV 0) (Re_r5, T0)) (Lc D ([], TV 0) (Rs_r0, T0)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma step_r5 t f1 deep :
  chs (repeat D2 (S (length deep))) ([W5t t; W5s t; W5a t; f1] :: deep) (b1s PD2 (LWs 81)) {{B}}> evR [t] Re_r5 -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([W5s t; W5a t; f1; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r0).
Proof.
  pose proof (regroup ([W5t t; W5s t; W5a t; f1] :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop rshift nth Gc].
  set (X' := chs (repeat U0 (S (length deep))) ([W5s t; W5a t; f1; rtop deep 0%N] :: rshift deep 0%N) (b1s P0 (LWs 0))).
  replace (2 + 4 * N.to_nat (W5t t)) with (ev [t] (tl1 74806 598752)) by (unfold ev, W5t, tl1; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t] (tl1 74806 598752)) *> X')) with (ev_runs [t] [(S0, cn 1); (S0, tl1 74806 598752)] X').
  apply drop_step, rec_r5_ok.
Qed.

Lemma pow_K0 k0 e : 2 <= e -> 3 ^ (k0 + 2 * e) = 3 ^ (k0 + 4) * 9 ^ (e - 2).
Proof.
  intros He. replace (k0 + 2 * e) with ((k0 + 4) + 2 * (e - 2)) by lia.
  rewrite Nat.pow_add_r, Nat.pow_mul_r. reflexivity.
Qed.

(* one record interval of class r5 *)
Lemma S_r5 e t f1 deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 1 + 2 * e ->
  Gc (repeat U0 (S (length deep)), P0, 0) ([W5t t; W5s t; W5a t; f1] :: deep) (evR [t] Rs_r5) -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([W5s t; W5a t; f1; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r0).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r5 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (length deep))) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (1 + 2 * e)))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (length deep)) = 27 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (1 + 2 * e))) with (3 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 3278 26244)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (27 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 3278 26244)) with (ev [t] (tl1 173868 1390932))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r5.
Qed.

Definition wv (c a t : N) : N := (c + a * t)%N.

Lemma evN_tl1 c a t : evN [t] (tl1 c a) = wv c a t.
Proof. unfold evN, tl1, wv. cbn [lc lv dot]. lia. Qed.

Lemma take_step L first4 Re' Rs nu sg X' :
  reach 100000 (Rc B (L, TV 0) (first4, TV 1)) (Rc A (comp_runs sg (blk U0), TV 0) ([], TV 1)) = true ->
  ep_run true Re' = Some Rs ->
  ev_runs nu L X' {{B}}> ev_runs nu first4 (evR nu Re') -->+
    ev_runs (map (evN nu) sg) (blk U0) X' <{{D}} evR nu Rs.
Proof.
  intros H1 H2. eapply progress_evstep_trans.
  - exact (reach_spec _ _ _ H1 nu (sg2 X' (evR nu Re'))).
  - change (ev_runs nu (comp_runs sg (blk U0)) X' {{A}}> evR nu Re' -->*
            ev_runs (map (evN nu) sg) (blk U0) X' <{{D}} evR nu Rs).
    rewrite ev_runs_comp. apply (ep_run_spec _ _ _ H2 nu).
Qed.

Lemma split4 nu r1 r2 r3 b c v rest X :
  ev_runs nu (r1 :: r2 :: r3 :: (b, LF (3 + c) v) :: rest) X =
  ev_runs nu [r1; r2; r3; (b, cn 3)] (ev_runs nu ((sneg b, LF c v) :: rest) X).
Proof.
  destruct r1 as [b1 n1], r2 as [b2 n2], r3 as [b3 n3]. cbn [ev_runs].
  assert (E : alt b (ev nu (LF (3 + c) v)) = alt b 3 ++ alt (sneg b) (ev nu (LF c v))).
  { unfold ev. cbn [lc lv].
    replace (N.to_nat (3 + c + dot v nu)) with (3 + N.to_nat (c + dot v nu)) by lia.
    rewrite alt_add. reflexivity. }
  rewrite E, Str_app_assoc. reflexivity.
Qed.

(* ---------- r0 -> r1 (take in x1, x2, x3) ---------- *)

Definition W0t := wv 6227 49896.
Definition W0s := wv 2069 16632.
Definition W1t := wv 168389 1347192.
Definition W1s := wv 56123 449064.
Definition W1a := wv 18701 149688.
Definition W1I := wv 6227 49896.
Definition W1u := wv 2069 16632.   (* t gap of block K-1 *)

Definition sig01 : list lf := [tl1 168389 1347192; tl1 56123 449064; tl1 18701 149688; tl1 6227 49896]%N.
Definition f4_r0 : list run := [(S0, tl1 74804 598752); (S1, tl1 224496 1796256); (S0, tl1 673560 5388768); (S1, cn 3)]%N.
Definition Rp_r0 : list run := [(S0, tl1 2020748 16166304); (S1, cn 7); (S1, tl1 551120 4408992); (S0, tl1 1564798 12518388); (S1, cn 1)]%N.

Lemma rec_r0a : reach 100000 (Rc B ([(S0, cn 1); (S0, tl1 24910 199584)], TV 0) (f4_r0, TV 1))
  (Rc A (comp_runs sig01 (blk U0), TV 0) ([], TV 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rec_r0b : ep_run true Rp_r0 = Some Rs_r1.
Proof. vm_compute. reflexivity. Qed.

Lemma split_r0 t : evR [t] Re_r0 = ev_runs [t] f4_r0 (evR [t] Rp_r0).
Proof.
  unfold evR, Re_r0, f4_r0, Rp_r0, tl1.
  change (2020751)%N with (3 + 2020748)%N. rewrite split4. reflexivity.
Qed.

Lemma step_r0 t f1 f2 deep :
  chs (repeat D2 (S (length deep))) ([W0t t; W0s t; f1; f2] :: deep) (b1s PD2 (LWs 81)) {{B}}> evR [t] Re_r0 -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0)
     ([W1t t; W1s t; W1a t; W1I t] :: [W0s t; f1; f2; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r1).
Proof.
  pose proof (regroup ([W0t t; W0s t; f1; f2] :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop rshift nth Gc].
  set (X' := chs (repeat U0 (S (length deep))) ([W0s t; f1; f2; rtop deep 0%N] :: rshift deep 0%N) (b1s P0 (LWs 0))).
  replace (2 + 4 * N.to_nat (W0t t)) with (ev [t] (tl1 24910 199584)) by (unfold ev, W0t, wv, tl1; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t] (tl1 24910 199584)) *> X')) with (ev_runs [t] [(S0, cn 1); (S0, tl1 24910 199584)] X').
  rewrite split_r0.
  replace [W1t t; W1s t; W1a t; W1I t] with (map (evN [t]) sig01)
    by (unfold sig01; cbn [map]; rewrite !evN_tl1; reflexivity).
  change (chs (repeat U0 (S (S (length deep)))) (map (evN [t]) sig01 :: [W0s t; f1; f2; rtop deep 0%N] :: rshift deep 0%N)
            (b1s P0 (LWs 0))) with (ev_runs (map (evN [t]) sig01) (blk U0) X').
  apply take_step; [exact rec_r0a | exact rec_r0b].
Qed.

(* ---------- r3 -> r4 (drop 1) ---------- *)

Definition W3t := wv 18701 149688.

Lemma rec_r3_ok : reach 100000 (Rc B ([(S0, cn 1); (S0, tl1 74806 598752)], TV 0) (Re_r3, T0)) (Lc D ([], TV 0) (Rs_r4, T0)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma step_r3 t f1 f2 f3 deep :
  chs (repeat D2 (S (length deep))) ([W3t t; f1; f2; f3] :: deep) (b1s PD2 (LWs 81)) {{B}}> evR [t] Re_r3 -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r4).
Proof.
  pose proof (regroup ([W3t t; f1; f2; f3] :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop rshift nth Gc].
  set (X' := chs (repeat U0 (S (length deep))) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (b1s P0 (LWs 0))).
  replace (2 + 4 * N.to_nat (W3t t)) with (ev [t] (tl1 74806 598752)) by (unfold ev, W3t, wv, tl1; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t] (tl1 74806 598752)) *> X')) with (ev_runs [t] [(S0, cn 1); (S0, tl1 74806 598752)] X').
  apply drop_step, rec_r3_ok.
Qed.

(* ---------- r1 -> r2 (drop 5) ---------- *)

Definition sig12 : list lf := [tl1 56123 449064; tl1 18701 149688; tl1 6227 49896; tl1 2069 16632]%N.

Lemma rec_r1_ok : reach 100000 (Rc B ([(S0, cn 1); (S0, tl1 673558 5388768)] ++ comp_runs sig12 (blk U0), TV 0) (Re_r1, T0))
  (Lc D ([], TV 0) (Rs_r2, T0)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma step_r1 t f1 f2 f3 deep :
  chs (repeat D2 (S (S (length deep)))) ([W1t t; W1s t; W1a t; W1I t] :: [W1u t; f1; f2; f3] :: deep) (b1s PD2 (LWs 81))
    {{B}}> evR [t] Re_r1 -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r2).
Proof.
  pose proof (regroup ([W1t t; W1s t; W1a t; W1I t] :: [W1u t; f1; f2; f3] :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop rshift nth Gc].
  set (X' := chs (repeat U0 (S (length deep))) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (b1s P0 (LWs 0))).
  change (chs (repeat U0 (S (S (length deep)))) ([W1s t; W1a t; W1I t; W1u t] :: [f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N)
            (b1s P0 (LWs 0))) with (ev_runs [W1s t; W1a t; W1I t; W1u t] (blk U0) X').
  replace [W1s t; W1a t; W1I t; W1u t] with (map (evN [t]) sig12) by (unfold sig12; cbn [map]; rewrite !evN_tl1; reflexivity).
  rewrite <-ev_runs_comp.
  replace (2 + 4 * N.to_nat (W1t t)) with (ev [t] (tl1 673558 5388768)) by (unfold ev, W1t, wv, tl1; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t] (tl1 673558 5388768)) *> ev_runs [t] (comp_runs sig12 (blk U0)) X'))
    with (ev_runs [t] ([(S0, cn 1); (S0, tl1 673558 5388768)] ++ comp_runs sig12 (blk U0)) X').
  apply drop_step, rec_r1_ok.
Qed.

(* ---------- r2 -> r3 (take in x1, x2, x3; the last t gap of the chain is free) ---------- *)

Definition xv : lf := LF 2 [0; 4]%N.
Definition sig23 : list lf := [tl1 18701 149688; tl1 6227 49896; tl1 2069 16632; LF 0 [0; 1]]%N.
Definition f4_r2 : list run := [(S0, tl1 8276 66528); (S1, tl1 24912 199584); (S0, tl1 74808 598752); (S1, cn 3)]%N.
Definition Rp_r2 : list run := [(S0, tl1 224492 1796256); (S1, tl1 673559 5388768); (S1, tl1 2020752 16166304);
  (S0, tl1 6062328 48498912); (S1, cn 3); (S1, tl1 1564801 12518388); (S1, cn 1)]%N.

Lemma rec_r2a : reach 100000 (Rc B ([(S0, cn 1); (S0, xv)], TV 0) (f4_r2, TV 1))
  (Rc A (comp_runs sig23 (blk U0), TV 0) ([], TV 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rec_r2b : ep_run true Rp_r2 = Some Rs_r3.
Proof. vm_compute. reflexivity. Qed.

Lemma split_r2 nu : evR nu Re_r2 = ev_runs nu f4_r2 (evR nu Rp_r2).
Proof.
  unfold evR, Re_r2, f4_r2, Rp_r2, tl1.
  change (224495)%N with (3 + 224492)%N. rewrite split4. reflexivity.
Qed.

Lemma step_r2 t q deep :
  chs (repeat D2 (S (length deep))) (q :: deep) (b1s PD2 (LWs 81)) {{B}}> evR [t] Re_r2 -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0)
     ([W3t t; wv 6227 49896 t; wv 2069 16632 t; nth 0 q 0%N] :: rshift (q :: deep) 0%N) (evR [t] Rs_r3).
Proof.
  pose proof (regroup (q :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop Gc].
  set (xK := nth 0 q 0%N).
  set (X' := chs (repeat U0 (S (length deep))) (rshift (q :: deep) 0%N) (b1s P0 (LWs 0))).
  replace (evR [t] Re_r2) with (evR [t; xK] Re_r2) by reflexivity.
  replace (evR [t] Rs_r3) with (evR [t; xK] Rs_r3) by reflexivity.
  replace (2 + 4 * N.to_nat xK) with (ev [t; xK] xv) by (unfold ev, xv; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t; xK] xv) *> X')) with (ev_runs [t; xK] [(S0, cn 1); (S0, xv)] X').
  replace [W3t t; wv 6227 49896 t; wv 2069 16632 t; xK] with (map (evN [t; xK]) sig23)
    by (unfold sig23, W3t, wv, tl1, evN; cbn [map lc lv dot]; f_equal; [lia|f_equal; [lia|f_equal; [lia|f_equal; lia]]]).
  change (chs (repeat U0 (S (S (length deep)))) (map (evN [t; xK]) sig23 :: rshift (q :: deep) 0%N) (b1s P0 (LWs 0)))
    with (ev_runs (map (evN [t; xK]) sig23) (blk U0) X').
  rewrite split_r2.
  apply take_step; [exact rec_r2a | exact rec_r2b].
Qed.

(* ---------- r4 -> r5 (take in x1, x2, x3; next epoch, u -> 9 u, t -> 1 + 9 t) ---------- *)

Definition sub9_lf (l : lf) : lf := match lv l with [a] => LF (lc l + a) [9 * a] | _ => l end%N.
Definition sub9 (rs : list run) : list run := map (fun r => (fst r, sub9_lf (snd r))) rs.

Lemma ev_runs_sub9 t rs X : forallb (fun r => Nat.leb (length (lv (snd r))) 1) rs = true ->
  ev_runs [t] (sub9 rs) X = ev_runs [(1 + 9 * t)%N] rs X.
Proof.
  unfold sub9. induction rs as [|[b l] rs IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. cbn [map ev_runs fst snd]. rewrite IH by exact H2.
  f_equal. f_equal. unfold sub9_lf, ev. destruct l as [c [|a [|a' v]]]; cbn [lc lv dot length Nat.leb] in *; [reflexivity | f_equal; ring | discriminate].
Qed.

Lemma evR_sub9_r5 t : evR [t] (sub9 Rs_r5) = evR [(1 + 9 * t)%N] Rs_r5.
Proof. unfold evR. apply ev_runs_sub9. reflexivity. Qed.

Definition sig45 : list lf := [tl1 168389 1347192; tl1 56123 449064; tl1 18701 149688; LF 0 [0; 1]]%N.
Definition f4_r4 : list run := [(S0, tl1 74804 598752); (S1, tl1 224496 1796256); (S0, tl1 673560 5388768); (S1, cn 3)]%N.
Definition Rp_r4 : list run := [(S0, tl1 2020748 16166304); (S1, tl1 6062327 48498912); (S1, cn 7);
  (S1, tl1 88573 708588); (S1, tl1 17478488 139828032); (S0, cn 2)]%N.

Lemma rec_r4a : reach 100000 (Rc B ([(S0, cn 1); (S0, xv)], TV 0) (f4_r4, TV 1))
  (Rc A (comp_runs sig45 (blk U0), TV 0) ([], TV 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rec_r4b : ep_run true Rp_r4 = Some (sub9 Rs_r5).
Proof. vm_compute. reflexivity. Qed.

Lemma split_r4 nu : evR nu Re_r4 = ev_runs nu f4_r4 (evR nu Rp_r4).
Proof.
  unfold evR, Re_r4, f4_r4, Rp_r4, tl1.
  change (2020751)%N with (3 + 2020748)%N. rewrite split4. reflexivity.
Qed.

Lemma step_r4 t q deep :
  chs (repeat D2 (S (length deep))) (q :: deep) (b1s PD2 (LWs 81)) {{B}}> evR [t] Re_r4 -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0)
     ([W5t (1 + 9 * t); W5s (1 + 9 * t); W5a (1 + 9 * t); nth 0 q 0%N] :: rshift (q :: deep) 0%N)
     (evR [(1 + 9 * t)%N] Rs_r5).
Proof.
  pose proof (regroup (q :: deep) 0%N _ (b1s P0 (LWs 0)) regroup_b1) as E.
  cbn [length] in E. rewrite E. clear E. cbn [rtop Gc].
  set (xK := nth 0 q 0%N).
  set (X' := chs (repeat U0 (S (length deep))) (rshift (q :: deep) 0%N) (b1s P0 (LWs 0))).
  replace (evR [t] Re_r4) with (evR [t; xK] Re_r4) by reflexivity.
  rewrite <-evR_sub9_r5.
  replace (evR [t] (sub9 Rs_r5)) with (evR [t; xK] (sub9 Rs_r5)) by reflexivity.
  replace (2 + 4 * N.to_nat xK) with (ev [t; xK] xv) by (unfold ev, xv; cbn [lc lv dot]; lia).
  change (alt S0 1 *> (alt S0 (ev [t; xK] xv) *> X')) with (ev_runs [t; xK] [(S0, cn 1); (S0, xv)] X').
  replace [W5t (1 + 9 * t); W5s (1 + 9 * t); W5a (1 + 9 * t); xK] with (map (evN [t; xK]) sig45)
    by (unfold sig45, W5t, W5s, W5a, tl1, evN; cbn [map lc lv dot]; f_equal; [lia|f_equal; [lia|f_equal; [lia|f_equal; lia]]]).
  change (chs (repeat U0 (S (S (length deep)))) (map (evN [t; xK]) sig45 :: rshift (q :: deep) 0%N) (b1s P0 (LWs 0)))
    with (ev_runs (map (evN [t; xK]) sig45) (blk U0) X').
  rewrite split_r4.
  apply take_step; [exact rec_r4a | exact rec_r4b].
Qed.

Lemma S_r0 e t f1 f2 deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 1 + 2 * e ->
  Gc (repeat U0 (S (length deep)), P0, 0) ([W0t t; W0s t; f1; f2] :: deep) (evR [t] Rs_r0) -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0) ([W1t t; W1s t; W1a t; W1I t] :: [W0s t; f1; f2; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r1).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r0 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (length deep))) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (1 + 2 * e)))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (length deep)) = 27 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (1 + 2 * e))) with (3 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 3278 26244)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (27 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 3278 26244)) with (ev [t] (tl1 173868 1390932))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r0.
Qed.

Lemma S_r1 e t f1 f2 f3 deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 1 + 2 * e ->
  Gc (repeat U0 (S (S (length deep))), P0, 0) ([W1t t; W1s t; W1a t; W1I t] :: [W1u t; f1; f2; f3] :: deep) (evR [t] Rs_r1) -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r2).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r1 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (S (length deep)))) = 243 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (S (1 + 2 * e))))) with (5 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (S (length deep))) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (1 + 2 * e)))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 9839 78732)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (81 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 9839 78732)) with (ev [t] (tl1 521601 4172796))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r1.
Qed.

Lemma S_r2 e t q deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 1 + 2 * e ->
  Gc (repeat U0 (S (length deep)), P0, 0) (q :: deep) (evR [t] Rs_r2) -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0) ([W3t t; wv 6227 49896 t; wv 2069 16632 t; nth 0 q 0%N] :: rshift (q :: deep) 0%N) (evR [t] Rs_r3).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r2 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (length deep))) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (1 + 2 * e)))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (length deep)) = 27 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (1 + 2 * e))) with (3 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 3278 26244)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (27 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 3278 26244)) with (ev [t] (tl1 173868 1390932))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r2.
Qed.

Lemma S_r3 e t f1 f2 f3 deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 2 + 2 * e ->
  Gc (repeat U0 (S (length deep)), P0, 0) ([W3t t; f1; f2; f3] :: deep) (evR [t] Rs_r3) -->+
  Gc (repeat U0 (S (length deep)), P0, 0) ([f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N) (evR [t] Rs_r4).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r3 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (length deep))) = 243 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (2 + 2 * e)))) with (5 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (length deep)) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (2 + 2 * e))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 9839 78732)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (81 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 9839 78732)) with (ev [t] (tl1 521601 4172796))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r3.
Qed.

Lemma S_r4 e t q deep : 2 <= e -> 1 + 8 * N.to_nat t = 9 ^ (e - 2) -> length deep = 2 + 2 * e ->
  Gc (repeat U0 (S (length deep)), P0, 0) (q :: deep) (evR [t] Rs_r4) -->+
  Gc (repeat U0 (S (S (length deep))), P0, 0) ([W5t (1 + 9 * t); W5s (1 + 9 * t); W5a (1 + 9 * t); nth 0 q 0%N] :: rshift (q :: deep) 0%N) (evR [(1 + 9 * t)%N] Rs_r5).
Proof.
  intros He Ht Hl.
  eapply evstep_progress_trans; [apply interval_tm; [lia | reflexivity |]|].
  - intros T ET. pose proof (prog_check_spec _ _ _ _ _ int_r4 [t]) as HP.
    assert (E3 : 3 ^ S (S (S (length deep))) = 243 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (S (2 + 2 * e)))) with (5 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    assert (E2 : 3 ^ S (S (length deep)) = 81 * 81 * (1 + 8 * N.to_nat t)).
    { rewrite Ht, Hl. replace (S (S (2 + 2 * e))) with (4 + 2 * e) by lia.
      rewrite pow_K0 by exact He. reflexivity. }
    rewrite E3 in ET. rewrite E2.
    replace T with (ev [t] (tl1 9839 78732)) by (unfold ev, tl1; cbn [lc lv dot]; lia).
    replace (81 * (81 * 81 * (1 + 8 * N.to_nat t)) - 1 - ev [t] (tl1 9839 78732)) with (ev [t] (tl1 521601 4172796))
      by (unfold ev, tl1; cbn [lc lv dot]; lia).
    exact HP.
  - eapply progress_trans; [apply record_visit; reflexivity|].
    apply step_r4.
Qed.

(* ===================================================================== *)
(* Base case: the blank tape reaches record exit 28.                     *)
(* ===================================================================== *)

Definition cfg28 : cfg :=
  Rc B
    ([(S0, cn 74808); (S1, cn 24912); (S0, cn 8277); (S0, cn 2737); (S0, cn 972); (S1, cn 36);
      (S0, cn 37); (S0, cn 37); (S0, cn 44); (S1, cn 24); (S0, cn 13); (S0, cn 9);
      (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5); (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5);
      (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 6); (S1, cn 4); (S0, cn 1);
      (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 2)], T0)
    ([(S1, cn 224495); (S1, cn 673559); (S1, cn 7); (S1, cn 9841); (S1, cn 1942040); (S0, cn 2)], T0).

(* The run from the blank tape to record exit 28, in 38 pieces of at most 500,000 simulator
   steps (each piece is one computation; intermediate configurations written out). *)
Definition mkc (rc : bool) (q : Q) (l r : list (Sym * N)) : cfg :=
  let f := map (fun x : Sym * N => (fst x, cn (snd x))) in
  if rc then Rc q (f l, T0) (f r, T0) else Lc q (f l, T0) (f r, T0).
Definition b28_0 : cfg := mkc true A [] [].
Definition b28_1 : cfg := mkc true F [(S0, 1%N); (S0, 5003%N); (S0, 9%N); (S0, 24909%N); (S0, 8281%N); (S0, 2736%N); (S1, 972%N); (S0, 34%N); (S1, 40%N); (S0, 36%N); (S1, 44%N); (S0, 21%N); (S0, 17%N); (S0, 8%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S0, 34783%N); (S0, 2%N)].
Definition b28_2 : cfg := mkc false C [(S1, 972%N); (S0, 36%N); (S1, 40%N); (S0, 34%N); (S1, 44%N); (S0, 24%N); (S1, 16%N); (S0, 6%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S0, 2734%N); (S1, 8280%N); (S0, 24912%N); (S1, 74807%N); (S1, 7%N); (S1, 20408%N); (S0, 18958%N); (S1, 1%N)].
Definition b28_3 : cfg := mkc false E [(S0, 24913%N); (S0, 8280%N); (S1, 2736%N); (S0, 969%N); (S0, 37%N); (S0, 40%N); (S1, 36%N); (S0, 41%N); (S0, 25%N); (S0, 16%N); (S1, 8%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 74805%N); (S1, 8%N); (S0, 15237%N); (S0, 102601%N); (S0, 2%N)].
Definition b28_4 : cfg := mkc true B [(S1, 8%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S0, 16%N); (S1, 23%N); (S1, 43%N); (S1, 36%N); (S0, 40%N); (S1, 35%N); (S1, 971%N); (S1, 2736%N); (S0, 8280%N); (S1, 24911%N); (S1, 74807%N); (S1, 8%N); (S0, 2576%N); (S1, 203893%N)].
Definition b28_5 : cfg := mkc false D [(S0, 224496%N); (S1, 74808%N); (S0, 24911%N); (S0, 8279%N); (S0, 2736%N); (S1, 972%N); (S0, 33%N); (S0, 41%N); (S0, 36%N); (S1, 44%N); (S0, 23%N); (S0, 15%N); (S0, 8%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 4%N); (S0, 47814%N); (S1, 1%N)].
Definition b28_6 : cfg := mkc false D [(S1, 55470%N); (S0, 61233%N); (S0, 7%N); (S0, 224495%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_7 : cfg := mkc true B [(S1, 61232%N); (S0, 5%N); (S0, 224497%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 1%N); (S1, 126903%N); (S1, 1%N)].
Definition b28_8 : cfg := mkc true A [(S0, 204457%N); (S0, 58637%N); (S0, 9%N); (S0, 224494%N); (S1, 74808%N); (S0, 24912%N); (S1, 8280%N); (S0, 2735%N); (S0, 971%N); (S0, 36%N); (S1, 40%N); (S0, 34%N); (S1, 44%N); (S0, 24%N); (S1, 16%N); (S0, 6%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_9 : cfg := mkc true B [(S1, 45980%N); (S0, 9%N); (S0, 224494%N); (S1, 74808%N); (S0, 24912%N); (S1, 8280%N); (S0, 2734%N); (S1, 972%N); (S0, 36%N); (S1, 40%N); (S0, 34%N); (S1, 44%N); (S0, 24%N); (S1, 16%N); (S0, 7%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N); (S1, 305726%N); (S0, 2%N)].
Definition b28_10 : cfg := mkc true B [(S1, 40%N); (S0, 34%N); (S1, 44%N); (S0, 24%N); (S1, 16%N); (S0, 5%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S0, 36%N); (S1, 971%N); (S1, 2735%N); (S1, 8280%N); (S0, 24912%N); (S1, 74807%N); (S1, 224495%N); (S1, 8%N); (S0, 33320%N); (S1, 407005%N)].
Definition b28_11 : cfg := mkc true B [(S0, 20664%N); (S1, 8%N); (S0, 224495%N); (S0, 74807%N); (S0, 24912%N); (S1, 8280%N); (S0, 2734%N); (S1, 972%N); (S0, 36%N); (S1, 40%N); (S0, 33%N); (S0, 45%N); (S0, 24%N); (S1, 16%N); (S0, 6%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 508270%N); (S0, 2%N)].
Definition b28_12 : cfg := mkc false D [(S1, 8%N); (S0, 224493%N); (S0, 74809%N); (S0, 24912%N); (S1, 8280%N); (S0, 2733%N); (S0, 973%N); (S0, 36%N); (S1, 40%N); (S0, 33%N); (S0, 45%N); (S0, 24%N); (S1, 16%N); (S0, 7%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S0, 8001%N); (S0, 609553%N); (S0, 2%N)].
Definition b28_13 : cfg := mkc true B [(S1, 224496%N); (S0, 74805%N); (S0, 24913%N); (S0, 8280%N); (S1, 2736%N); (S0, 970%N); (S1, 36%N); (S0, 40%N); (S1, 36%N); (S0, 41%N); (S0, 25%N); (S0, 16%N); (S1, 8%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S0, 673560%N); (S1, 4%N); (S0, 22085%N); (S0, 2%N)].
Definition b28_14 : cfg := mkc false D [(S0, 74806%N); (S1, 24912%N); (S0, 8280%N); (S1, 2736%N); (S0, 971%N); (S0, 35%N); (S0, 40%N); (S1, 36%N); (S0, 43%N); (S0, 23%N); (S0, 16%N); (S1, 8%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 224496%N); (S0, 673560%N); (S1, 3%N); (S1, 82093%N); (S1, 1%N)].
Definition b28_15 : cfg := mkc false A [(S0, 1%N); (S0, 24911%N); (S0, 8280%N); (S1, 2736%N); (S0, 970%N); (S1, 36%N); (S0, 40%N); (S1, 36%N); (S0, 43%N); (S0, 23%N); (S0, 16%N); (S1, 8%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 1%N); (S1, 74805%N); (S1, 224496%N); (S0, 673560%N); (S1, 4%N); (S0, 142098%N); (S1, 1%N)].
Definition b28_16 : cfg := mkc false D [(S1, 183704%N); (S0, 6%N); (S1, 673560%N); (S0, 224496%N); (S1, 74808%N); (S0, 24911%N); (S0, 8279%N); (S0, 2736%N); (S1, 972%N); (S0, 35%N); (S0, 39%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S0, 21909%N); (S0, 2%N)].
Definition b28_17 : cfg := mkc true B [(S1, 93339%N); (S1, 183704%N); (S0, 6%N); (S1, 673560%N); (S0, 224496%N); (S1, 74808%N); (S0, 24910%N); (S1, 8280%N); (S0, 2736%N); (S1, 972%N); (S0, 35%N); (S0, 39%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [].
Definition b28_18 : cfg := mkc false A [(S0, 1%N); (S0, 164770%N); (S1, 183704%N); (S0, 6%N); (S1, 673560%N); (S0, 224496%N); (S1, 74808%N); (S0, 24909%N); (S0, 8281%N); (S0, 2736%N); (S1, 972%N); (S0, 35%N); (S0, 39%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_19 : cfg := mkc true B [(S0, 5%N); (S0, 673561%N); (S0, 224496%N); (S1, 74808%N); (S0, 24911%N); (S0, 8279%N); (S0, 2736%N); (S1, 972%N); (S0, 34%N); (S1, 40%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 183703%N); (S1, 236201%N); (S1, 1%N)].
Definition b28_20 : cfg := mkc false D [(S1, 307633%N); (S1, 183704%N); (S0, 7%N); (S0, 673559%N); (S0, 224496%N); (S1, 74808%N); (S0, 24909%N); (S0, 8281%N); (S0, 2736%N); (S1, 972%N); (S0, 34%N); (S1, 40%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_21 : cfg := mkc false D [(S1, 74808%N); (S0, 24911%N); (S0, 8279%N); (S0, 2736%N); (S1, 972%N); (S0, 33%N); (S0, 41%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S0, 224496%N); (S1, 673559%N); (S1, 7%N); (S1, 183704%N); (S0, 379066%N); (S1, 1%N)].
Definition b28_22 : cfg := mkc true B [(S0, 7%N); (S0, 673559%N); (S0, 224496%N); (S1, 74808%N); (S0, 24910%N); (S1, 8280%N); (S0, 2736%N); (S1, 972%N); (S0, 33%N); (S0, 41%N); (S0, 36%N); (S1, 44%N); (S0, 22%N); (S1, 16%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 183703%N); (S1, 450497%N); (S1, 1%N)].
Definition b28_23 : cfg := mkc false D [(S0, 24911%N); (S0, 8279%N); (S0, 2736%N); (S1, 972%N); (S0, 35%N); (S0, 39%N); (S0, 36%N); (S1, 44%N); (S0, 21%N); (S0, 17%N); (S0, 8%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 6%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 74808%N); (S0, 224496%N); (S1, 673559%N); (S1, 7%N); (S1, 183704%N); (S0, 521925%N); (S0, 2%N)].
Definition b28_24 : cfg := mkc false D [(S1, 1%N); (S1, 611006%N); (S0, 176219%N); (S0, 9%N); (S0, 673557%N); (S0, 224497%N); (S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 39%N); (S0, 35%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_25 : cfg := mkc true B [(S1, 712274%N); (S0, 163560%N); (S1, 8%N); (S0, 673558%N); (S1, 224496%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 38%N); (S1, 36%N); (S0, 44%N); (S1, 24%N); (S0, 13%N); (S0, 9%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_26 : cfg := mkc true B [(S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 38%N); (S1, 36%N); (S0, 44%N); (S1, 24%N); (S0, 14%N); (S1, 8%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [(S1, 24912%N); (S0, 74808%N); (S1, 224495%N); (S1, 673559%N); (S1, 8%N); (S0, 150901%N); (S0, 813545%N); (S0, 2%N)].
Definition b28_27 : cfg := mkc true B [(S0, 914810%N); (S1, 138244%N); (S0, 9%N); (S0, 673559%N); (S0, 224495%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N)] [].
Definition b28_28 : cfg := mkc true B [(S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 13%N); (S0, 9%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 224495%N); (S1, 673559%N); (S1, 8%N); (S0, 125586%N); (S1, 1016072%N); (S0, 2%N)].
Definition b28_29 : cfg := mkc true B [(S0, 673559%N); (S0, 224495%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 39%N); (S0, 35%N); (S0, 44%N); (S1, 24%N); (S0, 13%N); (S0, 9%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 8%N); (S0, 112925%N); (S0, 1117353%N); (S0, 2%N)].
Definition b28_30 : cfg := mkc false A [(S0, 1%N); (S0, 7%N); (S0, 673558%N); (S1, 224496%N); (S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 39%N); (S0, 35%N); (S0, 44%N); (S1, 24%N); (S0, 14%N); (S1, 8%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 1%N); (S1, 100267%N); (S1, 1218616%N); (S0, 2%N)].
Definition b28_31 : cfg := mkc true C [(S1, 1%N); (S1, 1319886%N); (S0, 87610%N); (S1, 8%N); (S0, 673559%N); (S0, 224495%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 38%N); (S1, 36%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [].
Definition b28_32 : cfg := mkc false A [(S0, 1%N); (S0, 1421144%N); (S1, 74952%N); (S0, 9%N); (S0, 673557%N); (S0, 224497%N); (S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 38%N); (S1, 36%N); (S0, 44%N); (S1, 24%N); (S0, 13%N); (S0, 9%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 2%N)] [(S1, 1%N)].
Definition b28_33 : cfg := mkc false D [(S1, 1522415%N); (S1, 62293%N); (S1, 8%N); (S0, 673558%N); (S1, 224496%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 14%N); (S1, 8%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 2%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 1%N); (S1, 1%N)].
Definition b28_34 : cfg := mkc false E [(S0, 224497%N); (S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 37%N); (S0, 37%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 673557%N); (S1, 8%N); (S0, 49634%N); (S1, 1623688%N); (S0, 2%N)].
Definition b28_35 : cfg := mkc true B [(S0, 36974%N); (S1, 8%N); (S0, 673559%N); (S0, 224495%N); (S0, 74808%N); (S1, 24912%N); (S0, 8279%N); (S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 39%N); (S0, 35%N); (S0, 44%N); (S1, 24%N); (S0, 15%N); (S0, 7%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 1724965%N)].
Definition b28_36 : cfg := mkc false D [(S1, 1826223%N); (S1, 24317%N); (S1, 8%N); (S0, 673557%N); (S0, 224497%N); (S0, 74808%N); (S1, 24912%N); (S0, 8278%N); (S1, 2736%N); (S0, 972%N); (S1, 36%N); (S0, 39%N); (S0, 35%N); (S0, 44%N); (S1, 24%N); (S0, 13%N); (S0, 9%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 1%N); (S0, 5%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 1%N); (S1, 1%N)].
Definition b28_37 : cfg := mkc false D [(S0, 2735%N); (S0, 972%N); (S1, 36%N); (S0, 38%N); (S1, 36%N); (S0, 44%N); (S1, 24%N); (S0, 14%N); (S1, 8%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 2%N); (S1, 4%N); (S0, 4%N); (S1, 4%N); (S0, 1%N); (S0, 5%N); (S0, 4%N); (S1, 4%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 3%N); (S0, 2%N)] [(S1, 8279%N); (S1, 24912%N); (S0, 74808%N); (S1, 224495%N); (S1, 673559%N); (S1, 8%N); (S0, 11658%N); (S1, 1927496%N); (S0, 2%N)].
Lemma ck_0 : runp 500000 b28_0 = Some (b28_1, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_1 : runp 500000 b28_1 = Some (b28_2, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_2 : runp 500000 b28_2 = Some (b28_3, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_3 : runp 500000 b28_3 = Some (b28_4, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_4 : runp 500000 b28_4 = Some (b28_5, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_5 : runp 500000 b28_5 = Some (b28_6, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_6 : runp 500000 b28_6 = Some (b28_7, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_7 : runp 500000 b28_7 = Some (b28_8, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_8 : runp 500000 b28_8 = Some (b28_9, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_9 : runp 500000 b28_9 = Some (b28_10, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_10 : runp 500000 b28_10 = Some (b28_11, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_11 : runp 500000 b28_11 = Some (b28_12, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_12 : runp 500000 b28_12 = Some (b28_13, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_13 : runp 500000 b28_13 = Some (b28_14, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_14 : runp 500000 b28_14 = Some (b28_15, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_15 : runp 500000 b28_15 = Some (b28_16, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_16 : runp 500000 b28_16 = Some (b28_17, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_17 : runp 500000 b28_17 = Some (b28_18, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_18 : runp 500000 b28_18 = Some (b28_19, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_19 : runp 500000 b28_19 = Some (b28_20, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_20 : runp 500000 b28_20 = Some (b28_21, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_21 : runp 500000 b28_21 = Some (b28_22, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_22 : runp 500000 b28_22 = Some (b28_23, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_23 : runp 500000 b28_23 = Some (b28_24, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_24 : runp 500000 b28_24 = Some (b28_25, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_25 : runp 500000 b28_25 = Some (b28_26, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_26 : runp 500000 b28_26 = Some (b28_27, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_27 : runp 500000 b28_27 = Some (b28_28, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_28 : runp 500000 b28_28 = Some (b28_29, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_29 : runp 500000 b28_29 = Some (b28_30, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_30 : runp 500000 b28_30 = Some (b28_31, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_31 : runp 500000 b28_31 = Some (b28_32, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_32 : runp 500000 b28_32 = Some (b28_33, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_33 : runp 500000 b28_33 = Some (b28_34, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_34 : runp 500000 b28_34 = Some (b28_35, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_35 : runp 500000 b28_35 = Some (b28_36, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_36 : runp 500000 b28_36 = Some (b28_37, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_37 : runp 71896 b28_37 = Some (cfg28, true).
Proof. native_compute. reflexivity. Qed.
Lemma ck_ev p c c' : runp p c = Some (c', true) ->
  ev_cfg [] (fun _ => const S0) c -->* ev_cfg [] (fun _ => const S0) c'.
Proof. intros H. apply progress_evstep. exact (runp_spec [] (fun _ => const S0) _ _ _ _ H). Qed.

Lemma init28 : c0 -->* ev_cfg [] (fun _ => const S0) cfg28.
Proof.
  change c0 with (ev_cfg [] (fun _ => const S0) b28_0).
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_0)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_1)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_2)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_3)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_4)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_5)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_6)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_7)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_8)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_9)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_10)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_11)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_12)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_13)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_14)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_15)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_16)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_17)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_18)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_19)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_20)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_21)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_22)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_23)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_24)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_25)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_26)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_27)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_28)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_29)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_30)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_31)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_32)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_33)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_34)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_35)|].
  eapply evstep_trans; [exact (ck_ev _ _ _ ck_36)|].
  exact (ck_ev _ _ _ ck_37).
Qed.


(* ===================================================================== *)
(* The invariant at the start of every record interval, and its closure. *)
(* ===================================================================== *)

Inductive cls := C5 | C0 | C1 | C2 | C3 | C4.

Definition Rs (r : cls) : list run :=
  match r with C5 => Rs_r5 | C0 => Rs_r0 | C1 => Rs_r1 | C2 => Rs_r2 | C3 => Rs_r3 | C4 => Rs_r4 end.

Definition ist : Type := (cls * nat * N * list (list N))%type.

Definition cfgI (s : ist) : Q * tape :=
  let '(r, e, t, nus) := s in Gc (repeat U0 (length nus), P0, 0) nus (evR [t] (Rs r)).

Definition win (r : cls) (e : nat) (t : N) (nus : list (list N)) : Prop :=
  match r with
  | C5 => exists f1 deep, nus = [W5t t; W5s t; W5a t; f1] :: deep /\ length deep = 1 + 2 * e
  | C0 => exists f1 f2 deep, nus = [W0t t; W0s t; f1; f2] :: deep /\ length deep = 1 + 2 * e
  | C1 => exists f1 f2 f3 deep, nus = [W1t t; W1s t; W1a t; W1I t] :: [W1u t; f1; f2; f3] :: deep /\
            length deep = 1 + 2 * e
  | C2 => exists q deep, nus = q :: deep /\ length deep = 1 + 2 * e
  | C3 => exists f1 f2 f3 deep, nus = [W3t t; f1; f2; f3] :: deep /\ length deep = 2 + 2 * e
  | C4 => exists q deep, nus = q :: deep /\ length deep = 2 + 2 * e
  end.

Definition Inv (s : ist) : Prop :=
  let '(r, e, t, nus) := s in 2 <= e /\ 1 + 8 * N.to_nat t = 9 ^ (e - 2) /\ win r e t nus.

Lemma inv_step s : Inv s -> exists s', cfgI s -->+ cfgI s' /\ Inv s'.
Proof.
  destruct s as [[[r e] t] nus]. intros [He [Ht Hw]].
  destruct r; cbn [win] in Hw.
  - destruct Hw as [f1 [deep [-> Hl]]].
    exists (C0, e, t, [W5s t; W5a t; f1; rtop deep 0%N] :: rshift deep 0%N). split.
    + cbn [cfgI length Rs]. rewrite shift_len. apply (S_r5 e); assumption.
    + cbn [Inv win]. split; [exact He|]. split; [exact Ht|].
      exists f1, (rtop deep 0%N), (rshift deep 0%N). split; [reflexivity|]. rewrite shift_len. exact Hl.
  - destruct Hw as [f1 [f2 [deep [-> Hl]]]].
    exists (C1, e, t, [W1t t; W1s t; W1a t; W1I t] :: [W0s t; f1; f2; rtop deep 0%N] :: rshift deep 0%N). split.
    + cbn [cfgI length Rs]. rewrite shift_len. apply (S_r0 e); assumption.
    + cbn [Inv win]. split; [exact He|]. split; [exact Ht|].
      exists f1, f2, (rtop deep 0%N), (rshift deep 0%N). split; [reflexivity|]. rewrite shift_len. exact Hl.
  - destruct Hw as [f1 [f2 [f3 [deep [-> Hl]]]]].
    exists (C2, e, t, [f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N). split.
    + cbn [cfgI length Rs]. rewrite shift_len. apply (S_r1 e); assumption.
    + cbn [Inv win]. split; [exact He|]. split; [exact Ht|].
      exists [f1; f2; f3; rtop deep 0%N], (rshift deep 0%N). split; [reflexivity|]. rewrite shift_len. exact Hl.
  - destruct Hw as [q [deep [-> Hl]]].
    exists (C3, e, t, [W3t t; wv 6227 49896 t; wv 2069 16632 t; nth 0 q 0%N] :: rshift (q :: deep) 0%N). split.
    + cbn [cfgI length Rs]. rewrite shift_len. cbn [length]. apply (S_r2 e); assumption.
    + cbn [Inv win]. split; [exact He|]. split; [exact Ht|].
      exists (wv 6227 49896 t), (wv 2069 16632 t), (nth 0 q 0%N), (rshift (q :: deep) 0%N). split; [reflexivity|].
      rewrite shift_len. cbn [length]. lia.
  - destruct Hw as [f1 [f2 [f3 [deep [-> Hl]]]]].
    exists (C4, e, t, [f1; f2; f3; rtop deep 0%N] :: rshift deep 0%N). split.
    + cbn [cfgI length Rs]. rewrite shift_len. apply (S_r3 e); assumption.
    + cbn [Inv win]. split; [exact He|]. split; [exact Ht|].
      exists [f1; f2; f3; rtop deep 0%N], (rshift deep 0%N). split; [reflexivity|]. rewrite shift_len. exact Hl.
  - destruct Hw as [q [deep [-> Hl]]].
    exists (C5, S e, (1 + 9 * t)%N, [W5t (1 + 9 * t); W5s (1 + 9 * t); W5a (1 + 9 * t); nth 0 q 0%N] :: rshift (q :: deep) 0%N).
    split.
    + cbn [cfgI length Rs]. rewrite shift_len. cbn [length]. apply (S_r4 e); assumption.
    + cbn [Inv win]. split; [lia|]. split.
      * replace (S e - 2) with (S (e - 2)) by lia. cbn [Nat.pow]. rewrite <-Ht. lia.
      * exists (nth 0 q 0%N), (rshift (q :: deep) 0%N). split; [reflexivity|]. rewrite shift_len. cbn [length]. lia.
Qed.

(* ===================================================================== *)
(* From record exit 28 to the invariant (class r5, e = 2, u = 1).        *)
(* ===================================================================== *)

Definition L28 : list run :=
  [(S0, cn 74808); (S1, cn 24912); (S0, cn 8277); (S0, cn 2737); (S0, cn 972); (S1, cn 36);
   (S0, cn 37); (S0, cn 37); (S0, cn 44); (S1, cn 24); (S0, cn 13); (S0, cn 9);
   (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5); (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5);
   (S0, cn 4); (S1, cn 4); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 6); (S1, cn 4); (S0, cn 1);
   (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 1); (S0, cn 5); (S0, cn 2)]%N.
Definition R28 : list run := [(S0, cn 224492); (S1, cn 673559); (S1, cn 7); (S1, cn 9841); (S1, cn 1942040); (S0, cn 2)]%N.

Definition nus28 : list (list N) :=
  [[18701; 6227; 2069; 683]; [242; 8; 9; 8]; [10; 5; 3; 1]; [0; 0; 0; 0]; [0; 0; 0; 0]; [0; 0; 0; 0]]%N.

Lemma inv28 : Inv (C5, 2, 0%N, nus28).
Proof.
  cbn [Inv win]. split; [lia|]. split; [reflexivity|].
  exists 683%N, (tl nus28). split; reflexivity.
Qed.

Lemma split1 nu b c v rest X :
  ev_runs nu ((b, LF (3 + c) v) :: rest) X = ev_runs nu [(b, cn 3)] (ev_runs nu ((sneg b, LF c v) :: rest) X).
Proof.
  cbn [ev_runs]. unfold ev. cbn [lc lv].
  replace (N.to_nat (3 + c + dot v nu)) with (3 + N.to_nat (c + dot v nu)) by lia.
  rewrite alt_add, Str_app_assoc. reflexivity.
Qed.

Lemma b28a : reach 1000 (Rc B (L28, T0) ([(S1, cn 3)], TV 1)) (Rc A ((S0, cn 3) :: L28, T0) ([], TV 1)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b28b : ep_run true R28 = Some (map (fun r => (fst r, cn (evN [0%N] (snd r)))) Rs_r5).
Proof. vm_compute. reflexivity. Qed.

Lemma b28_chain : ev_runs [] ((S0, cn 3) :: L28) (const S0) = chs (repeat U0 6) nus28 (b1s P0 (LWs 0)).
Proof. reflexivity. Qed.

Lemma b28_right : evR [] (map (fun r => (fst r, cn (evN [0%N] (snd r)))) Rs_r5) = evR [0%N] Rs_r5.
Proof. reflexivity. Qed.

Lemma base28 :
  ev_runs [] L28 (const S0) {{B}}> ev_runs [] ((S1, cn 224495) :: tl R28) (const S0) -->*
  cfgI (C5, 2, 0%N, nus28).
Proof.
  change (cn 224495) with (LF (3 + 224492) []).
  rewrite split1.
  eapply evstep_trans.
  - apply progress_evstep. exact (reach_spec _ _ _ b28a [] (sg2 (const S0) (evR [] R28))).
  - change (ev_runs [] ((S0, cn 3) :: L28) (const S0) {{A}}> evR [] R28 -->* cfgI (C5, 2, 0%N, nus28)).
    replace (cfgI (C5, 2, 0%N, nus28))
      with (ev_runs [] ((S0, cn 3) :: L28) (const S0) <{{D}} evR [] (map (fun r => (fst r, cn (evN [0%N] (snd r)))) Rs_r5)).
    + apply (ep_run_spec _ _ _ b28b []).
    + unfold cfgI, Gc. rewrite b28_chain, b28_right. reflexivity.
Qed.

(* ===================================================================== *)
(* The machine never halts.                                              *)
(* ===================================================================== *)

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [apply init28 | exact base28].
  - apply (progress_nonhalt_cond tm ist (C5, 2, 0%N, nus28) cfgI Inv inv_step inv28).
Qed.



(*
```
1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA---

     0    1
A   1RB  0RF
B   1RC  0RB
C   1LD  0RA
D   1LE  0LD
E   1RB  0LC
F   1LA  ---

sweep cycles (alternating cells, every cell complemented):
  right:  B0 C1 A0 B1   (1RC 0RA 1RB 0RB)
  left :  D1 D0 E1 C0   (0LD 1LE 0LC 1LD)

configuration at the start of a record interval (cfgI):
  chs (U0^m) nus (b1s P0 (LWs 0)) <{{D}} evR [t] (Rs r)
  chain: m = K - 1 blocks with m = 3 (gap variables nus, nearest the head first), block 1
         (m = 1), left word W_1; right region: run list Rs r, linear in t, u = 9^(e-2) = 1 + 8 t.

block rules (all gaps symbolic, both sides abstract), entering from the right at phase c (D):
  U0 -> U1, U1 -> U2, W0 -> W1, W1 -> D0       leave right at c + 2 (A)
  D1 -> D0, D2 -> D1                           leave right at c     (B)
  U2, D0 passed                                leave left  at c + 2 (D)
entering from the left: U2 at c -> U0 (A), U2 at c + 2 -> W0 (A), D0 at c + 2 -> D2 (B)
block 1: P0 -> P1 -> PD0 (A), PD2 -> PD1 -> PD0 (B), PD0 passed (E), PD0 from the left -> PD2.

one interval (S_r):  (81 * 3^K - 1) visits + episodes (interval_tm, int_r),
  record visit: carry-out at all D0, left record, carry back to all D2 (record_visit),
  regrouping one defect later (regroup), record-exit episode (step_r).
classes r5 -> r0 -> r1 -> r2 -> r3 -> r4 -> r5 (e + 1, t -> 1 + 9 t); K0 = 3 3 4 3 4 4.
```
*)
