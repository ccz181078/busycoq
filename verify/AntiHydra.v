(* Proof of Antihydra rules. Based on https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html *)

From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

(* Low-level Rule *)

(* 11 <B 0 1^c 0^inf  ->  <B 0 1^c+3 0^inf *)
Lemma B_once c l:
  l <* [1;1] <{{B}} [0] *> [1]^^c *> const 0  -->*
  l <{{B}} [0] *> [1]^^(c + 3) *> const 0.
Proof.
  es.
Qed.

Lemma B_rep n c l:
  l <* [1]^^(n*2) <{{B}} [0] *> [1]^^c *> const 0  -->*
  l <{{B}} [0] *> [1]^^(n*3 + c) *> const 0.
Proof.
  gen c l.
  ind n B_once.
Qed.

(* General Configuration: E a b := 0^inf 1^b 0 1^a E> 0^inf *)
Definition E a b :=
  const 0 <* [1]^^b <* [0] <* [1]^^a {{E}}> const 0.

(* High-level Rules *)
(* E 2n b  ->  E 3n+2 b+2  for all n >= 1 *)
Lemma R0 n b:
  E (n*2 + 2) b -->*
  E (n*3 + 5) (b + 2).
Proof.
  replace (n*2 + 2) with (2 + n*2) by lia.
  unfold E.
  rewrite lpow_add, Str_app_assoc.
  do 9 step.
  follow (B_rep n 3 (const 0 <* [1]^^b <* [0])).
  es.
Qed.

(* E 2n+1 b+1  ->  E 3n+3 b  for all n >= 1 *)
Lemma R1 n b:
  E (n*2 + 3) (b + 1) -->*
  E (n*3 + 6) b.
Proof.
  replace (n*2 + 3) with (2 + n*2 + 1) by lia.
  unfold E.
  rewrite lpow_add, Str_app_assoc.
  do 9 step.
  follow (B_rep n 3 (const 0 <* [1]^^b <* [1;0;1])).
  es.
Qed.

(* E 2n+1 0 -> Halt  for all n >= 1 *)
Lemma Rhalt n:
  halts tm (E (n*2 + 3) 0).
Proof.
  unfold halts,halts_in.
  eapply halts_evstep.
  2:{
    replace (n*2 + 3) with (2 + n*2 + 1) by lia.
    unfold E.
    rewrite lpow_add, Str_app_assoc.
    do 9 step.
    follow (B_rep n 3 (const 0 <* [1])).
    repeat step.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma init:
  c0 -->* E 4 0.
Proof.
  unfold E.
  solve_init.
Qed.


Check init.
Check R0.
Check R1.
Check Rhalt.
