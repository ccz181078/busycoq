(* 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE--- halts from the blank tape.

   The machine obeys the visit law of VisitLaw2.v with two forms of visit.  A visit: the head stands on a 0 with a
   0 on its left and the stream s on its right, in state C (form V) or in state F (form W); it comes back in
   state A two cells further left, both 0s restored and s rewritten:

     0 s -> 1 s      100 s -> 000 v(s)      110 s -> 000 v(s) (form V)      1010 s -> 1010 v(w(s))

   and a visit that meets 1011 halts.  The lemmas below prove these rules by running the machine.  After 6 steps
   the tape is [LE (1 0^inf)], and a round takes [LE s] to [LE s'] by one visit of form V to 1 0 s.
   [VisitLaw2.check_ok] runs the law for 161,210 rounds and finds that the next round halts.
   In this machine form W also obeys the rule for 110, which is not needed.  1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE--- differs in one
   transition (E1) and obeys the same law, where form W does not have the rule for 110. *)
From BusyCoq Require Import Individual62 VisitLaw2.
From Coq Require Import String.
Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---"%string).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition Vq (q : Q) (s s' : side) : Prop :=
  forall x l, S0 >> x >> l {{q}}> S0 >> s -->+ l {{A}}> x >> S0 >> S0 >> s'.
Definition Hq (q : Q) (s : side) : Prop :=
  forall x l, halts tm (S0 >> x >> l {{q}}> S0 >> s).
Definition LE (s : side) : Q * tape := const S0 {{A}}> S1 >> S0 >> S0 >> s.

Ltac use H := eapply evstep_trans; [apply progress_evstep; apply H|].
Ltac vis H1 H2 := intros x l; (eapply progress_intro; [prove_step|simpl_tape]);
  repeat (first [solve [finish] | use H1 | use H2 | step]).
Ltac hv H H1 := intros x l; (eapply halts_evstep; [apply H|]);
  repeat (first [apply evstep_refl | use H1 | eapply evstep_step; [prove_step|simpl_tape]]).

Lemma v0 : forall q r, q = C \/ q = F -> Vq q (S0 >> r) (S1 >> r).
Proof. intros q r [-> | ->] x l; execute. Qed.
Lemma vH : forall q r r', q = C \/ q = F -> Vq C r r' -> Vq q (S1 >> S0 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Proof. intros q r r' [-> | ->] H; vis H H. Qed.
Lemma vG : forall r r', Vq C r r' -> Vq C (S1 >> S1 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Proof. intros r r' H; vis H H. Qed.
Lemma vL : forall q r r1 r2, q = C \/ q = F -> Vq F r r1 -> Vq C r1 r2 ->
  Vq q (S1 >> S0 >> S1 >> S0 >> r) (S1 >> S0 >> S1 >> S0 >> r2).
Proof. intros q r r1 r2 [-> | ->] H1 H2; vis H1 H2. Qed.
Lemma h1011 : forall q r, q = C \/ q = F -> Hq q (S1 >> S0 >> S1 >> S1 >> r).
Proof. intros q r [-> | ->] x l; solve_halt. Qed.
Lemma hH : forall q r, q = C \/ q = F -> Hq C r -> Hq q (S1 >> S0 >> S0 >> r).
Proof. intros q r [-> | ->] H; hv H H. Qed.
Lemma hG : forall r, Hq C r -> Hq C (S1 >> S1 >> S0 >> r).
Proof. intros r H; hv H H. Qed.
Lemma hL1 : forall q r, q = C \/ q = F -> Hq F r -> Hq q (S1 >> S0 >> S1 >> S0 >> r).
Proof. intros q r [-> | ->] H; hv H H. Qed.
Lemma hL2 : forall q r r1, q = C \/ q = F -> Vq F r r1 -> Hq C r1 -> Hq q (S1 >> S0 >> S1 >> S0 >> r).
Proof. intros q r r1 [-> | ->] H1 H2; hv H2 H1. Qed.
Lemma round_step : forall s s', Vq C (S1 >> S0 >> s) s' -> LE s -->+ LE s'.
Proof.
  intros s s' H. unfold LE. eapply progress_intro; [prove_step|simpl_tape].
  repeat (first [apply progress_evstep; apply H | step]).
Qed.
Lemma round_halt : forall s, Hq C (S1 >> S0 >> s) -> halts tm (LE s).
Proof.
  intros s H. unfold LE. eapply halts_evstep; [apply H|].
  repeat (first [apply evstep_refl | eapply evstep_step; [prove_step|simpl_tape]]).
Qed.
Lemma blank_start : c0 -->+ LE (S1 >> const S0).
Proof.
  unfold c0, LE, tape0. eapply progress_intro; [prove_step|simpl_tape]. repeat (first [solve [finish] | step]).
Qed.

Theorem halts : halts tm c0.
Proof.
  apply (halts_of_check tm (Vq C) (Vq F) (Hq C) (Hq F) LE) with (n := 161210%nat); [..|exact check_ok].
  - intros r. apply v0. auto.
  - intros r r'. apply vH. auto.
  - exact vG.
  - intros r r1 r2. apply vL. auto.
  - intros r. apply v0. auto.
  - intros r r'. apply vH. auto.
  - intros r r1 r2. apply vL. auto.
  - intros r. apply h1011. auto.
  - intros r. apply hH. auto.
  - exact hG.
  - intros r. apply hL1. auto.
  - intros r r1. apply hL2. auto.
  - intros r. apply h1011. auto.
  - intros r. apply hH. auto.
  - intros r. apply hL1. auto.
  - intros r r1. apply hL2. auto.
  - exact round_step.
  - exact round_halt.
  - exact blank_start.
Qed.

Print Assumptions halts.
