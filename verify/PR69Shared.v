From BusyCoq Require Import Individual62 OpaqueBlocks.
Require Import List.
Import ListNotations.
Close Scope sym_scope.
Require Coq.Strings.String.
Import String.StringSyntax.

Definition tm := Eval compute in
  TM_from_str "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC".

Definition s (l : list nat) : list tok :=
  map (fun n => Cl (match n with 0 => S0 | _ => S1 end)) l.
Definition p (n : nat) : list tok := map Cl ([S0; S1] ^^ n).
Definition tpl (r : list tok) : list tok :=
  s [0;1;0] ++ [Bk W false] ++ p 4 ++ s [0;0;0] ++
  [Bk W true] ++ p 4 ++ s [0;0;0] ++ r.

Definition seeds : list (list tok * nat) := [
  (tpl (p 21 ++ s [1;1] ++ p 3 ++ s [0;0;0] ++ p 4 ++ s [0;0;0] ++ p 7 ++ s [0;0;0] ++ p 4 ++
        s [0;0;0;0;1;0;0;0;0;1;0;0;0] ++ p 2), 22);
  (tpl (p 10 ++ s [0;0;0] ++ p 4 ++ s [0;0;0] ++ p 12 ++ s [1;1;0;0;0] ++ p 2), 15);
  (tpl (p 33 ++ s [1;1] ++ p 6 ++ s [0;0;0] ++ p 2), 16);
  (tpl (p 22 ++ s [0;0;0] ++ p 10 ++ s [0;0;0] ++ p 7 ++ s [0;0;0] ++ p 6 ++ s [1;1;0;0;0] ++ p 2), 9)].

Definition TP : list (list tok) := flat_map (fun x => orbit tm C (snd x) (fst x)) seeds.

Lemma template_nonhalt k j t :
  forallb (ok tm C TP 147) TP = true ->
  mem TP t = true -> Nat.leb 147 (k + j) = true -> ~ halts tm (D C (k, j) t).
Proof.
  intros Hcert Ht Hkj.
  apply (progress_nonhalt tm (Good C TP 147)).
  - exact (Good_step tm C TP 147 Hcert).
  - exists t, k, j. repeat split.
    + now apply mem_spec.
    + now apply PeanoNat.Nat.leb_le.
Qed.

(* This is the only expensive closure check for either machine. *)
Lemma cert_ok : forallb (ok tm C TP 147) TP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma start : c0 -[ tm ]->* D C (38, 164) (nth 0 TP []).
Proof. apply start_spec with (n := 13 * Nat.pow 10 5). vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  intro H.
  apply (proj1 (halts_evstep_iff _ _ _ start)) in H.
  eapply (template_nonhalt 38 164 (nth 0 TP []) cert_ok).
  - vm_compute. reflexivity.
  - reflexivity.
  - exact H.
Qed.

Print Assumptions nonhalt.
