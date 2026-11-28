From BusyCoq Require Import Individual62 PR100RunShared.
From Coq Require Import String.
Local Open Scope string_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE").

Definition rename q := match q with E => F | F => E | q => q end.
Definition lift (c : Q * tape) := (rename (fst c);; snd c).

Lemma stop c : halted Engine.src_tm c -> halts tm (lift c).
Proof.
  intros H. exists 0%nat, (lift c); split; [constructor|].
  destruct c as [q [[l b] r]]. destruct q, b; cbv in H |- *; congruence.
Qed.

Lemma advance c c' : c -[Engine.src_tm]-> c' ->
  (lift c -[tm]->* lift c') \/ halts tm (lift c).
Proof.
  intros E.
  destruct E as [q q' s s' l r H | q q' s s' l r H];
    destruct q, s; cbv in H; inversion H; subst;
    try (left; eapply evstep_step; [solve [constructor; reflexivity]|apply evstep_refl]).
  destruct l as [x l']; destruct x.
  - left.
    eapply evstep_step; [eapply step_left; reflexivity |].
    eapply evstep_step; [eapply step_right; reflexivity |].
    eapply evstep_step; [eapply step_right; reflexivity |].
    apply evstep_refl.
  - right. exists 1%nat; eexists; split.
    + econstructor; [eapply step_left; reflexivity | constructor].
    + reflexivity.
Qed.

Lemma transfer c : halts Engine.src_tm c -> halts tm (lift c).
Proof.
  intros [n [ch [Hrun Hstop]]].
  induction Hrun as [c | n c c1 c2 Hstep _ IH].
  - now apply stop.
  - destruct (advance c c1 Hstep) as [H | H]; [|exact H].
    eapply halts_evstep; [now apply IH | exact H].
Qed.

Theorem halt_from_certificate : check_start 19 A = true -> halts tm c0.
Proof. intro H; exact (transfer (A;; tape0) (check_start_sound _ _ H)). Qed.

Lemma cert_ok : check_start 19 A = true.
Proof. native_check_eq. Qed.

Theorem halt : halts tm c0.
Proof. exact (halt_from_certificate cert_ok). Qed.
End TM1.

Print Assumptions TM1.halt.
