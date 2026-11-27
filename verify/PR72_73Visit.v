From BusyCoq Require Import Individual62.
From BusyCoq Require Import VisitLaw2.
From Coq Require Import String.
Set Default Goal Selector "!".

(* Only the transition E/1 differs.  Abstract it behind the reconvergence
   lemma below; the rest of the visit protocol is common. *)
Definition machine72 : TM :=
  Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---"%string).

Definition machine73 : TM :=
  Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---"%string).

Definition machine (e1 : option (Sym * dir * Q)) : TM :=
  fun '(q, s) =>
  match q, s with
  | A, S0 => Some (S1, R, B) | A, S1 => Some (S0, L, B)
  | B, S0 => Some (S0, R, C) | B, S1 => Some (S0, L, E)
  | C, S0 => Some (S1, R, D) | C, S1 => Some (S0, R, F)
  | D, S0 => Some (S1, L, B) | D, S1 => Some (S1, R, B)
  | E, S0 => Some (S0, L, A) | E, S1 => e1
  | F, S0 => Some (S1, R, E) | F, S1 => None
  end.

Definition selected (new : bool) : TM :=
  machine (if new then Some (S1, R, B) else Some (S0, R, E)).

Lemma machine72_exact : selected false = machine72.
Proof. reflexivity. Qed.

Lemma machine73_exact : selected true = machine73.
Proof. reflexivity. Qed.

Section Rules.
Variable new : bool.
Local Notation tm := (selected new).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition returns (q : Q) (s s' : side) : Prop :=
  forall x l, S0 >> x >> l {{q}}> S0 >> s -->+ l {{A}}> x >> S0 >> S0 >> s'.
Definition stops (q : Q) (s : side) : Prop :=
  forall x l, halts tm (S0 >> x >> l {{q}}> S0 >> s).
Definition left_edge (s : side) : Q * tape :=
  const S0 {{A}}> S1 >> S0 >> S0 >> s.

(* At E/1 with a blank next cell, PR72 takes E1,E0,A0,B0;
   PR73 takes E1,B0.  In both cases the pair 10 is preserved and
   the head enters the following cell in C. *)
Lemma e_common : forall l r,
  l {{E}}> S1 >> S0 >> r -->+ S0 >> S1 >> l {{C}}> r.
Proof. intros l r. destruct new; execute. Qed.

Ltac use H := eapply evstep_trans; [apply progress_evstep; apply H|].
Ltac vis H1 H2 := intros x l; (eapply progress_intro; [prove_step|simpl_tape]);
  repeat (first [solve [finish] | use H1 | use H2 | use e_common | step]).
Ltac hv H H1 := intros x l; (eapply halts_evstep; [apply H|]);
  repeat (first [apply evstep_refl | use H1 | use e_common | eapply evstep_step; [prove_step|simpl_tape]]).

Lemma v0 : forall q r, q = C \/ q = F -> returns q (S0 >> r) (S1 >> r).
Proof. intros q r [-> | ->] x l; execute. Qed.
Lemma vH : forall q r r', q = C \/ q = F -> returns C r r' ->
  returns q (S1 >> S0 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Proof. intros q r r' [-> | ->] H; vis H H. Qed.
Lemma vG : forall r r', returns C r r' -> returns C (S1 >> S1 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Proof. intros r r' H; vis H H. Qed.
Lemma vL : forall q r r1 r2, q = C \/ q = F -> returns F r r1 -> returns C r1 r2 ->
  returns q (S1 >> S0 >> S1 >> S0 >> r) (S1 >> S0 >> S1 >> S0 >> r2).
Proof. intros q r r1 r2 [-> | ->] H1 H2; vis H1 H2. Qed.
Lemma h1011 : forall q r, q = C \/ q = F -> stops q (S1 >> S0 >> S1 >> S1 >> r).
Proof.
  intros q r [-> | ->] x l.
  - solve_halt.
  - eapply halts_evstep; [|eapply evstep_step; [prove_step|simpl_tape; apply progress_evstep, e_common]].
    solve_halt.
Qed.
Lemma hH : forall q r, q = C \/ q = F -> stops C r -> stops q (S1 >> S0 >> S0 >> r).
Proof. intros q r [-> | ->] H; hv H H. Qed.
Lemma hG : forall r, stops C r -> stops C (S1 >> S1 >> S0 >> r).
Proof. intros r H; hv H H. Qed.
Lemma hL1 : forall q r, q = C \/ q = F -> stops F r -> stops q (S1 >> S0 >> S1 >> S0 >> r).
Proof. intros q r [-> | ->] H; hv H H. Qed.
Lemma hL2 : forall q r r1, q = C \/ q = F -> returns F r r1 -> stops C r1 -> stops q (S1 >> S0 >> S1 >> S0 >> r).
Proof. intros q r r1 [-> | ->] H1 H2; hv H2 H1. Qed.

Lemma round_step : forall s s', returns C (S1 >> S0 >> s) s' -> left_edge s -->+ left_edge s'.
Proof.
  intros s s' H. unfold left_edge. eapply progress_intro; [prove_step|simpl_tape].
  repeat (first [apply progress_evstep; apply H | step]).
Qed.
Lemma round_halt : forall s, stops C (S1 >> S0 >> s) -> halts tm (left_edge s).
Proof.
  intros s H. unfold left_edge. eapply halts_evstep; [apply H|].
  repeat (first [apply evstep_refl | eapply evstep_step; [prove_step|simpl_tape]]).
Qed.
Lemma blank_start : c0 -->+ left_edge (S1 >> const S0).
Proof.
  unfold c0, left_edge, tape0. eapply progress_intro; [prove_step|simpl_tape].
  repeat (first [solve [finish] | step]).
Qed.

Theorem common_visit_halt : forall n, check n = true -> halts tm c0.
Proof.
  intros n Hcheck.
  apply (halts_of_check tm (returns C) (returns F) (stops C) (stops F) left_edge) with (n := n);
    solve [exact vG | exact hG | exact round_step | exact round_halt | exact blank_start | exact Hcheck
          | intros; apply v0; auto | intros; apply vH; auto | intros; eapply vL; eauto
          | intros; apply h1011; auto | intros; apply hH; auto | intros; apply hL1; auto
          | intros; eapply hL2; eauto].
Qed.
End Rules.

Theorem both_halt_of_check : forall n, check n = true ->
  halts machine72 c0 /\ halts machine73 c0.
Proof.
  intros n H. split; [rewrite <- machine72_exact | rewrite <- machine73_exact];
    eapply common_visit_halt; exact H.
Qed.
Print Assumptions both_halt_of_check.
