(** * Two more starts of the table of PR_LongTranslatedCycler

    The BB(6) holdouts

      1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---
      1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---

    are the machine [T0 = 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---] of
    PR_LongTranslatedCycler.v with the tape mirrored, the states renamed, and the run started
    in state B (first machine) or state C (second machine) of T0 instead of state A.

    Both starts of T0 reach the same restart configuration  [cfg R = 0^inf {{C}}> S *> R]
    as the start in state A, so the [cycle] lemma of PR_LongTranslatedCycler.v applies unchanged:
    - from state B within 101,413 RWLAccT macro steps (a direct simulation reaches the restart
      configuration at machine step 1,700,871,744,916,068);
    - from state C within 314,374 RWLAccT macro steps (at about machine step 1.576e46).

    This file adds only the two pre-runs (checked by the kernel's virtual machine, as [pre_ok]
    there) and the transfer of non-halting along the mirror-and-rename map.

    AI assistance: this proof, the scripts and the checks were produced with the help of Claude
    (Anthropic). *)

From BusyCoq Require Import RWLAccT62 PR_LongTranslatedCycler.
Require Import List NArith String.
Import ListNotations.

(** the machine proved in PR_LongTranslatedCycler.v *)
Notation tm0 := PR_LongTranslatedCycler.tm.

(** ** T0 started on the blank tape in any state *)

Definition blank_from (q:Q) : Q * tape := (q, (Streams.const s0, s0, Streams.const s0)).

Definition nblank : N := 1000000000000000000000000000000%N.
Definition cpre_from (q:Q) : RWL_config := ([], [(zw,(0%N,0%N),nblank)], q, R).

Lemma cpre_from_blank q: to_config (Streams.const s0) 0 0 (cpre_from q) = blank_from q.
Proof.
  unfold cpre_from, to_config, to_side_t, tl_of, tr_of.
  cbn [flat_map].
  rewrite app_nil_r.
  unfold to_seg.
  generalize (N.to_nat 0 * 0 + N.to_nat 0 * 0 + N.to_nat nblank)%nat as m.
  intros m. rewrite zw_pow_const.
  reflexivity.
Qed.

(** if the pre-run from state [q] ends in a restart configuration, T0 never halts from there *)
Lemma nonhalt_from q T:
  is_some (run T 2000 4900 2000 (cpre_from q)) = true -> ~ halts tm0 (blank_from q).
Proof.
  intros Hok.
  destruct (run T 2000 4900 2000 (cpre_from q)) as [[M rest]|] eqn:E; [|discriminate Hok].
  pose proof (run_spec T 2000 4900 2000 _ _ _ (Streams.const s0) E) as H0.
  rewrite cpre_from_blank in H0.
  eapply multistep_nonhalt.
  1: apply progress_evstep, H0.
  apply (progress_nonhalt tm0 (fun c => exists R, c = cfg R)).
  - intros c [R Hc]. subst c.
    destruct (cycle R) as [R' H].
    exists (cfg R'). split; [exists R'; reflexivity | exact H].
  - eexists. reflexivity.
Qed.

(** ** Mirror the tape and rename the states *)

Definition fl (d:dir) : dir := match d with L => R | R => L end.

Section Transfer.
Variable tm1 : TM.
Variable sig : Q -> Q.
Variable tm_some: forall q s s' d q',
  tm1 (q,s) = Some (s',d,q') -> tm0 (sig q, s) = Some (s', fl d, sig q').
Variable tm_none: forall q s, tm1 (q,s) = None -> tm0 (sig q, s) = None.

Definition mir (c:Q*tape) : Q*tape := match c with (q,(l,s,r)) => (sig q,(r,s,l)) end.

Lemma mir_step c c': c -[ tm1 ]-> c' -> mir c -[ tm0 ]-> mir c'.
Proof.
  intros H. destruct H as [q q' s s' l r E | q q' s s' l r E].
  - exact (step_right (tm_some _ _ _ _ _ E)).
  - exact (step_left (tm_some _ _ _ _ _ E)).
Qed.

Lemma mir_multistep n c c': c -[ tm1 ]->> n / c' -> mir c -[ tm0 ]->> n / mir c'.
Proof.
  intros H. induction H.
  - constructor.
  - econstructor. 1: apply mir_step; eassumption. assumption.
Qed.

Lemma mir_halted c: halted tm1 c -> halted tm0 (mir c).
Proof.
  destruct c as [q [[l s] r]]. unfold halted, mir. intros H.
  apply tm_none, H.
Qed.

Lemma mir_halts c: halts tm1 c -> halts tm0 (mir c).
Proof.
  intros [n [ch [H1 H2]]]. exists n, (mir ch). split.
  - apply mir_multistep, H1.
  - apply mir_halted, H2.
Qed.

Lemma mir_c0: mir c0 = blank_from (sig A).
Proof. reflexivity. Qed.

Lemma sibling_nonhalt T:
  is_some (run T 2000 4900 2000 (cpre_from (sig A))) = true -> ~ halts tm1 c0.
Proof.
  intros Hok H. apply mir_halts in H. rewrite mir_c0 in H.
  exact (nonhalt_from _ _ Hok H).
Qed.

End Transfer.

(** ** 1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---  (T0 mirrored, started in its state B) *)

Module StartB.

Open Scope string.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---").
Close Scope string.

Definition sig (q:Q) : Q := match q with A => B | B => C | C => D | D => E | E => A | F => F end.

Lemma tm_some q s s' d q':
  tm (q,s) = Some (s',d,q') -> tm0 (sig q, s) = Some (s', fl d, sig q').
Proof. destruct q, s; cbn; intros H; inversion H; reflexivity. Qed.

Lemma tm_none q s: tm (q,s) = None -> tm0 (sig q, s) = None.
Proof. destruct q, s; cbn; intros H; (discriminate H || reflexivity). Qed.

Definition Tpre : N := 101413%N.

Lemma pre_ok: is_some (run Tpre 2000 4900 2000 (cpre_from B)) = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Theorem nonhalt: ~ halts tm c0.
Proof. exact (sibling_nonhalt tm sig tm_some tm_none Tpre pre_ok). Qed.

End StartB.

(** ** 1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---  (T0 mirrored, started in its state C) *)

Module StartC.

Open Scope string.
Definition tm := Eval compute in (TM_from_str "1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---").
Close Scope string.

Definition sig (q:Q) : Q := match q with A => C | B => D | C => B | D => E | E => A | F => F end.

Lemma tm_some q s s' d q':
  tm (q,s) = Some (s',d,q') -> tm0 (sig q, s) = Some (s', fl d, sig q').
Proof. destruct q, s; cbn; intros H; inversion H; reflexivity. Qed.

Lemma tm_none q s: tm (q,s) = None -> tm0 (sig q, s) = None.
Proof. destruct q, s; cbn; intros H; (discriminate H || reflexivity). Qed.

Definition Tpre : N := 314374%N.

Lemma pre_ok: is_some (run Tpre 2000 4900 2000 (cpre_from C)) = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Theorem nonhalt: ~ halts tm c0.
Proof. exact (sibling_nonhalt tm sig tm_some tm_none Tpre pre_ok). Qed.

End StartC.
