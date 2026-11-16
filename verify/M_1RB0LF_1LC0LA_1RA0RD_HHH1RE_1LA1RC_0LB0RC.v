From BusyCoq Require Import Individual62 OpaqueBlocks.
Require Import List.
Import ListNotations.
Close Scope sym_scope.
Require Coq.Strings.String.
Import String.StringSyntax.

(** * 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC does not halt

  Each time state C steps onto a new cell at the left end, the tape is

    [C> 010 (01)^a 000 (01)^b T]

  with a short tail [T] of runs of [01] separated by [000], [11] or [00001000].
  One round trip takes 3 pairs from [a], adds at least 3 to [b] and rewrites [T].
  [T] runs through one of four cycles, of 22, 15, 16 and 9 round trips.  When [a]
  is used up, the left end is rebuilt, [b] becomes the new [a], and after at most
  147 round trips [T] is in one of the four cycles again, with the first run of
  the old tail as the new [b].

  [OpaqueBlocks] checks this with [a = 3k + 4] and [b = 3j + 4] ([k], [j] unknown)
  for the 62 tapes of the four cycles.  The run from blank tape reaches the tape
  [nth 0 TP] with [k = 38], [j = 164] after 1,277,432 steps.

  1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA is the same table started in state C;
  the same certificate proves it in the file of that name. *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC").

Definition s (l : list nat) : list tok := map (fun n => Cl (match n with 0 => S0 | _ => S1 end)) l.
Definition p (n : nat) : list tok := map Cl ([S0; S1] ^^ n).
Definition tpl (r : list tok) : list tok :=
  s [0;1;0] ++ [Bk W false] ++ p 4 ++ s [0;0;0] ++ [Bk W true] ++ p 4 ++ s [0;0;0] ++ r.

(** One tape of each tail cycle, and the length of the cycle. *)
Definition seeds : list (list tok * nat) := [
  (tpl (p 21 ++ s [1;1] ++ p 3 ++ s [0;0;0] ++ p 4 ++ s [0;0;0] ++ p 7 ++ s [0;0;0] ++ p 4 ++
        s [0;0;0;0;1;0;0;0;0;1;0;0;0] ++ p 2), 22);
  (tpl (p 10 ++ s [0;0;0] ++ p 4 ++ s [0;0;0] ++ p 12 ++ s [1;1;0;0;0] ++ p 2), 15);
  (tpl (p 33 ++ s [1;1] ++ p 6 ++ s [0;0;0] ++ p 2), 16);
  (tpl (p 22 ++ s [0;0;0] ++ p 10 ++ s [0;0;0] ++ p 7 ++ s [0;0;0] ++ p 6 ++ s [1;1;0;0;0] ++ p 2), 9)].

(** The 62 templates: the tapes of the four cycles. *)
Definition TP : list (list tok) := flat_map (fun x => orbit tm C (snd x) (fst x)) seeds.

Lemma cert_ok : forallb (ok tm C TP 147) TP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma start : c0 -[ tm ]->* D C (38, 164) (nth 0 TP []).
Proof. apply start_spec with (n := 13 * Nat.pow 10 5). vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (nonhalt_of_cert tm C TP 147 38 164 (nth 0 TP []) cert_ok);
    [vm_compute; reflexivity | reflexivity | exact start].
Qed.

Print Assumptions nonhalt.
