From BusyCoq Require Import Individual62.

Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1RC0LC_1LD1RF_---1LE_0RC1LA_0RB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition Z := [0].

Definition R k := [1]^^k.

Definition U ls := flat_map (fun n => Z ++ R n) ls.

Close Scope sym.

Definition S1 n :=
  0inf%sym <{{E}}
  ((R 2)++(U [7])^^3++(U [10;19;4;22;1;1;4;1;25;7;31])++(U [28;1;25])^^19++(U [22])) *>
  ((R 6)++(U [1;25;28])^^26++(U [1;25;22]))^^(1+n) *>
  ((U [1;1;4;1;25;4;1;19;4;1;4;4;1;1;4;1;
    10;4;1;43;4;1;4;4;1;7;4;1;25;4;1;1;
    40;1;1;22;1;1;4;1;1;4;1;1;4;1;1;28;
    1;1;34;1;7;4;1;13;10;1;1;4;1;13;4;1])++Z) *>
  ((R 10)++(U [4;1;10;4;1;1;4;1;37;4;1;40;4;1;
    19;4;1;37;4;1;10;4;1;1;13;1;4;4;1;13;
    4;1;13;4;1;10;4;1;1;13;1;1;19;1;1;13;
    1;1;4;1;1;40;1;1;43;1;1;22;1;1;40;1;1;
    13;1;1;4;1;10;7;1;1;16;1;1;16;1;1;13;
    1;1;4;1;10;4;1;6]))^^(1+n) *>
  ((R 1)++(U [1])^^3++Z++(U [3;5])++(U [7])^^3++(U [1])) *>
  0inf%sym.

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; repeat rewrite <-const_unfold; reflexivity.

Lemma init:
  c0 -->* S1 0.
Proof.
  stepn 4760139%N.
Qed.

Lemma BigStep n:
  S1 (n) -->+ S1 (1+n).
Proof.
  unfold S1.
  es' n.
Time Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros i; exists (1+i).
  apply BigStep.
Qed.

End TM1.



