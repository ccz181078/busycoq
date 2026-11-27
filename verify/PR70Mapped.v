From BusyCoq Require Import Individual62 OpaqueBlocks.
From BusyCoq Require PR69Shared.
Require Import List.
Import ListNotations.
Close Scope sym_scope.
Require Coq.Strings.String.
Import String.StringSyntax.

Definition tm := Eval compute in
  TM_from_str "1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA".

(* Transfer PR70 configurations to PR69 without changing the tape. *)
Definition rename (q : Q) : Q :=
  match q with A => C | B => A | C => B | q => q end.

Definition config (c : Q * tape) : Q * tape := (rename (fst c), snd c).

Definition rename_transition (o : option (Sym * dir * Q)) :=
  option_map (fun '(w, d, q') => (w, d, rename q')) o.

Lemma table q s :
  rename_transition (tm (q, s)) =
  PR69Shared.tm (rename q, s).
Proof. destruct q, s; reflexivity. Qed.

Lemma transition q s o (H : tm (q, s) = o) :
  PR69Shared.tm (rename q, s) = rename_transition o.
Proof. exact (eq_trans (eq_sym (table q s)) (f_equal rename_transition H)). Qed.

Lemma map_step c c' : c -[ tm ]-> c' ->
  config c -[ PR69Shared.tm ]-> config c'.
Proof.
  destruct 1 as [q q' s w l r H | q q' s w l r H].
  - exact (@step_left PR69Shared.tm (rename q) (rename q') s w l r (transition q s _ H)).
  - exact (@step_right PR69Shared.tm (rename q) (rename q') s w l r (transition q s _ H)).
Qed.

Lemma map_halts c : halts tm c -> halts PR69Shared.tm (config c).
Proof.
  intros [n [ch [Hsteps Hhalted]]].
  exists n, (config ch); split.
  - clear Hhalted.
    induction Hsteps; [constructor | eapply multistep_S; eauto using map_step].
  - destruct ch as [q [[l s] r]].
    cbn [halted config fst snd] in *.
    exact (transition q s None Hhalted).
Qed.

Definition entry := nth 32 PR69Shared.TP [].

Lemma start : c0 -[ tm ]->* D A (36, 113) entry.
Proof. apply start_spec with (n := 7 * Nat.pow 10 5). vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  intro H.
  apply (proj1 (halts_evstep_iff _ _ _ start)) in H.
  apply map_halts in H.
  change (halts PR69Shared.tm (D C (36, 113) entry)) in H.
  eapply (PR69Shared.template_nonhalt 36 113 entry PR69Shared.cert_ok);
    [vm_compute; reflexivity | reflexivity | exact H].
Qed.

Print Assumptions nonhalt.
