From BusyCoq Require Import Individual62 PR100RunShared.
From Coq Require Import String.
Local Open Scope string_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---").

Definition rename q :=
  match q with A => D | B => A | C => B | D => C | q => q end.

Lemma valid : Perm (flip Engine.src_tm) tm rename.
Proof.
  split;
  [intros q s H; destruct q, s; cbv in H |- *; try discriminate; reflexivity
  |intros q s s' d q' H; destruct q, s; cbv in H |- *; inversion H; subst; reflexivity].
Qed.

Theorem halt_from_certificate : check_start 19 B = true -> halts tm c0.
Proof.
  intros H. apply check_start_sound in H. apply flip_halts in H.
  exact (perm_halts _ _ _ _ _ valid H).
Qed.

Lemma cert_ok : check_start 19 B = true.
Proof. native_check_eq. Qed.

Theorem halt : halts tm c0.
Proof. exact (halt_from_certificate cert_ok). Qed.
End TM1.

Print Assumptions TM1.halt.
