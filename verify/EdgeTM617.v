From BusyCoq Require Import Individual62.
Require Import Ascii String List PeanoNat NArith.


Lemma Permute_halts_iff tm tm' f q t:
  Perm tm tm' f ->
  halts tm (q,t) <->
  halts tm' (f q,t).
Proof.
  intro H.
  split; intro.
  - eapply perm_halts; eauto.
  - eapply perm_halts'; eauto.
Qed.

Open Scope N.

Definition Q_from_char'(x:ascii):Q :=
match Q_from_char x with
| Some y => y
| _ => A
end.

Fixpoint mp_from_str(x:string)(n:Q):Q :=
match x with
| String x0 (String x1 (String x2 (String x3 (String x4 (String x5 _))))) =>
  match n with
  | A => Q_from_char' x0
  | B => Q_from_char' x1
  | C => Q_from_char' x2
  | D => Q_from_char' x3
  | E => Q_from_char' x4
  | F => Q_from_char' x5
  end
| _ => n
end.

Ltac solve_evstep T :=
  eapply without_counter;
  eapply multistep_c_spec with (n:=N.to_nat T);
  vm_compute;
  simpl_tape;
  reflexivity.

Ltac solve_eqv tm tm' f T1 T2 :=
  rewrite (halts_evstep_iff tm);
  [ | solve_evstep T1 ];
  rewrite (halts_evstep_iff tm');
  [ | solve_evstep T2 ];
  eapply (Permute_halts_iff tm tm' f);
  split;
  [ intros q s; destruct q,s; cbn; congruence
  | intros q s s' d q'; destruct q,s; cbn; intros H; inverts H; reflexivity ].

Module TM617.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0RE_1RC1LB_1RA1LB_0LD---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECBADF") 2235 3242.
Time Qed.
End TM617.

Check TM617.eqv.
Print Assumptions TM617.eqv.
